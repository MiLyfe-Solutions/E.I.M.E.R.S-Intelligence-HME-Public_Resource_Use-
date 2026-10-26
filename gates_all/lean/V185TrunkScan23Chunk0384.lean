import V185TrunkScan23Chunk0383

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2270496 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 2, 5]
def baseStart_2270496 : Nat := 118140960795 + 2270496 * 2 ^ 59
def prefixEnd_2270496 : Nat := 4983230072969 + 3 ^ 40 * 2270496 * 2
def baseEnd_2270496 : Nat := 388618590703617969219395

theorem tailTrace_2270496 : CollatzResearch.WordTrace tailWord_2270496 prefixEnd_2270496 388618590703617969219395 := by
  unfold tailWord_2270496
  simp only [CollatzResearch.WordTrace]
  refine ⟨41405896191194118344987671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55207861588258824459983561 41405896191194118344987671)
  ·
    refine ⟨62108844286791177517481507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41405896191194118344987671 62108844286791177517481507)
    ·
      refine ⟨93163266430186766276222261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62108844286791177517481507 93163266430186766276222261)
      ·
        refine ⟨8734056227830009338395837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93163266430186766276222261 8734056227830009338395837)
        ·
          refine ⟨3275271085436253501898439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8734056227830009338395837 3275271085436253501898439)
          ·
            refine ⟨4912906628154380252847659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275271085436253501898439 4912906628154380252847659)
            ·
              refine ⟨7369359942231570379271489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4912906628154380252847659 7369359942231570379271489)
              ·
                refine ⟨5527019956673677784453617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7369359942231570379271489 5527019956673677784453617)
                ·
                  refine ⟨4145264967505258338340213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5527019956673677784453617 4145264967505258338340213)
                  ·
                    refine ⟨388618590703617969219395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4145264967505258338340213 388618590703617969219395)
                    ·
                      rfl

theorem cell23_2270496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 5].length) (baseStart_2270496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270496 prefixEnd_2270496 := by exact prefixLift 2270496
  have htrace : WordTrace (prefixWord ++ tailWord_2270496) baseStart_2270496 baseEnd_2270496 := by
    simpa [prefixWord, tailWord_2270496, baseEnd_2270496] using wordTrace_append hprefix tailTrace_2270496
  have hstable : (prefixWord ++ tailWord_2270496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270496).length < 2 ^ (prefixWord ++ tailWord_2270496).sum := by decide
  have hdescent : baseEnd_2270496 < baseStart_2270496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270499 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 4]
def baseStart_2270499 : Nat := 118140960795 + 2270499 * 2 ^ 59
def prefixEnd_2270499 : Nat := 4983230072969 + 3 ^ 40 * 2270499 * 2
def baseEnd_2270499 : Nat := 1165857312552817395920671

theorem tailTrace_2270499 : CollatzResearch.WordTrace tailWord_2270499 prefixEnd_2270499 1165857312552817395920671 := by
  unfold tailWord_2270499
  simp only [CollatzResearch.WordTrace]
  refine ⟨82811901801377368202334551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55207934534251578801556367 82811901801377368202334551)
  ·
    refine ⟨124217852702066052303501827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82811901801377368202334551 124217852702066052303501827)
    ·
      refine ⟨186326779053099078455252741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124217852702066052303501827 186326779053099078455252741)
      ·
        refine ⟨34936271072456077210359889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186326779053099078455252741 34936271072456077210359889)
        ·
          refine ⟨26202203304342057907769917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34936271072456077210359889 26202203304342057907769917)
          ·
            refine ⟨9825826239128271715413719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26202203304342057907769917 9825826239128271715413719)
            ·
              refine ⟨14738739358692407573120579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9825826239128271715413719 14738739358692407573120579)
              ·
                refine ⟨22108109038038611359680869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14738739358692407573120579 22108109038038611359680869)
                ·
                  refine ⟨4145270444632239629940163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22108109038038611359680869 4145270444632239629940163)
                  ·
                    refine ⟨6217905666948359444910245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4145270444632239629940163 6217905666948359444910245)
                    ·
                      refine ⟨1165857312552817395920671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6217905666948359444910245 1165857312552817395920671)
                      ·
                        rfl

theorem cell23_2270499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_2270499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270499 prefixEnd_2270499 := by exact prefixLift 2270499
  have htrace : WordTrace (prefixWord ++ tailWord_2270499) baseStart_2270499 baseEnd_2270499 := by
    simpa [prefixWord, tailWord_2270499, baseEnd_2270499] using wordTrace_append hprefix tailTrace_2270499
  have hstable : (prefixWord ++ tailWord_2270499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270499).length < 2 ^ (prefixWord ++ tailWord_2270499).sum := by decide
  have hdescent : baseEnd_2270499 < baseStart_2270499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270506 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2270506 : Nat := 118140960795 + 2270506 * 2 ^ 59
def prefixEnd_2270506 : Nat := 4983230072969 + 3 ^ 40 * 2270506 * 2
def baseEnd_2270506 : Nat := 1165860906917398868533139

theorem tailTrace_2270506 : CollatzResearch.WordTrace tailWord_2270506 prefixEnd_2270506 1165860906917398868533139 := by
  unfold tailWord_2270506
  simp only [CollatzResearch.WordTrace]
  refine ⟨20703039278088002099459843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55208104741568005598559581 20703039278088002099459843)
  ·
    refine ⟨31054558917132003149189765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20703039278088002099459843 31054558917132003149189765)
    ·
      refine ⟨5822729796962250590473081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31054558917132003149189765 5822729796962250590473081)
      ·
        refine ⟨4367047347721687942854811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5822729796962250590473081 4367047347721687942854811)
        ·
          refine ⟨6550571021582531914282217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367047347721687942854811 6550571021582531914282217)
          ·
            refine ⟨4912928266186898935711663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6550571021582531914282217 4912928266186898935711663)
            ·
              refine ⟨7369392399280348403567495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4912928266186898935711663 7369392399280348403567495)
              ·
                refine ⟨11054088598920522605351243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7369392399280348403567495 11054088598920522605351243)
                ·
                  refine ⟨16581132898380783908026865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11054088598920522605351243 16581132898380783908026865)
                  ·
                    refine ⟨12435849673785587931020149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16581132898380783908026865 12435849673785587931020149)
                    ·
                      refine ⟨1165860906917398868533139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12435849673785587931020149 1165860906917398868533139)
                      ·
                        rfl

theorem cell23_2270506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2270506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270506 prefixEnd_2270506 := by exact prefixLift 2270506
  have htrace : WordTrace (prefixWord ++ tailWord_2270506) baseStart_2270506 baseEnd_2270506 := by
    simpa [prefixWord, tailWord_2270506, baseEnd_2270506] using wordTrace_append hprefix tailTrace_2270506
  have hstable : (prefixWord ++ tailWord_2270506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270506).length < 2 ^ (prefixWord ++ tailWord_2270506).sum := by decide
  have hdescent : baseEnd_2270506 < baseStart_2270506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270516 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2270516 : Nat := 118140960795 + 2270516 * 2 ^ 59
def prefixEnd_2270516 : Nat := 4983230072969 + 3 ^ 40 * 2270516 * 2
def baseEnd_2270516 : Nat := 1165866041723943829408093

theorem tailTrace_2270516 : CollatzResearch.WordTrace tailWord_2270516 prefixEnd_2270516 1165866041723943829408093 := by
  unfold tailWord_2270516
  simp only [CollatzResearch.WordTrace]
  refine ⟨41406260921157890052851701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55208347894877186737135601 41406260921157890052851701)
  ·
    refine ⟨3881836961358552192454847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41406260921157890052851701 3881836961358552192454847)
    ·
      refine ⟨5822755442037828288682271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3881836961358552192454847 5822755442037828288682271)
      ·
        refine ⟨8734133163056742433023407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5822755442037828288682271 8734133163056742433023407)
        ·
          refine ⟨13101199744585113649535111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8734133163056742433023407 13101199744585113649535111)
          ·
            refine ⟨19651799616877670474302667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13101199744585113649535111 19651799616877670474302667)
            ·
              refine ⟨29477699425316505711454001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19651799616877670474302667 29477699425316505711454001)
              ·
                refine ⟨22108274568987379283590501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29477699425316505711454001 22108274568987379283590501)
                ·
                  refine ⟨4145301481685133615673219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22108274568987379283590501 4145301481685133615673219)
                  ·
                    refine ⟨6217952222527700423509829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4145301481685133615673219 6217952222527700423509829)
                    ·
                      refine ⟨1165866041723943829408093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6217952222527700423509829 1165866041723943829408093)
                      ·
                        rfl

theorem cell23_2270516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2270516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270516 prefixEnd_2270516 := by exact prefixLift 2270516
  have htrace : WordTrace (prefixWord ++ tailWord_2270516) baseStart_2270516 baseEnd_2270516 := by
    simpa [prefixWord, tailWord_2270516, baseEnd_2270516] using wordTrace_append hprefix tailTrace_2270516
  have hstable : (prefixWord ++ tailWord_2270516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270516).length < 2 ^ (prefixWord ++ tailWord_2270516).sum := by decide
  have hdescent : baseEnd_2270516 < baseStart_2270516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270526 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_2270526 : Nat := 118140960795 + 2270526 * 2 ^ 59
def prefixEnd_2270526 : Nat := 4983230072969 + 3 ^ 40 * 2270526 * 2
def baseEnd_2270526 : Nat := 388623725510162930094349

theorem tailTrace_2270526 : CollatzResearch.WordTrace tailWord_2270526 prefixEnd_2270526 388623725510162930094349 := by
  unfold tailWord_2270526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10351610821534943976695929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55208591048186367875711621 10351610821534943976695929)
  ·
    refine ⟨7763708116151207982521947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10351610821534943976695929 7763708116151207982521947)
    ·
      refine ⟨11645562174226811973782921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7763708116151207982521947 11645562174226811973782921)
      ·
        refine ⟨8734171630670108980337191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11645562174226811973782921 8734171630670108980337191)
        ·
          refine ⟨13101257446005163470505787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8734171630670108980337191 13101257446005163470505787)
          ·
            refine ⟨19651886169007745205758681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13101257446005163470505787 19651886169007745205758681)
            ·
              refine ⟨14738914626755808904319011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19651886169007745205758681 14738914626755808904319011)
              ·
                refine ⟨22108371940133713356478517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14738914626755808904319011 22108371940133713356478517)
                ·
                  refine ⟨2072659869387535627169861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22108371940133713356478517 2072659869387535627169861)
                  ·
                    refine ⟨388623725510162930094349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2072659869387535627169861 388623725510162930094349)
                    ·
                      rfl

theorem cell23_2270526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_2270526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270526 prefixEnd_2270526 := by exact prefixLift 2270526
  have htrace : WordTrace (prefixWord ++ tailWord_2270526) baseStart_2270526 baseEnd_2270526 := by
    simpa [prefixWord, tailWord_2270526, baseEnd_2270526] using wordTrace_append hprefix tailTrace_2270526
  have hstable : (prefixWord ++ tailWord_2270526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270526).length < 2 ^ (prefixWord ++ tailWord_2270526).sum := by decide
  have hdescent : baseEnd_2270526 < baseStart_2270526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270560 : List Nat := [2, 1, 1, 3, 4, 1, 4, 2, 1, 4]
def baseStart_2270560 : Nat := 118140960795 + 2270560 * 2 ^ 59
def prefixEnd_2270560 : Nat := 4983230072969 + 3 ^ 40 * 2270560 * 2
def baseEnd_2270560 : Nat := 388629544957580552419297

theorem tailTrace_2270560 : CollatzResearch.WordTrace tailWord_2270560 prefixEnd_2270560 388629544957580552419297 := by
  unfold tailWord_2270560
  simp only [CollatzResearch.WordTrace]
  refine ⟨41407063327078187810152567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55209417769437583746870089 41407063327078187810152567)
  ·
    refine ⟨62110594990617281715228851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41407063327078187810152567 62110594990617281715228851)
    ·
      refine ⟨93165892485925922572843277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62110594990617281715228851 93165892485925922572843277)
      ·
        refine ⟨34937209682222220964816229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93165892485925922572843277 34937209682222220964816229)
        ·
          refine ⟨6550726815416666430903043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34937209682222220964816229 6550726815416666430903043)
          ·
            refine ⟨9826090223124999646354565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550726815416666430903043 9826090223124999646354565)
            ·
              refine ⟨1842391916835937433691481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9826090223124999646354565 1842391916835937433691481)
              ·
                refine ⟨1381793937626953075268611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1842391916835937433691481 1381793937626953075268611)
                ·
                  refine ⟨2072690906440429612902917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381793937626953075268611 2072690906440429612902917)
                  ·
                    refine ⟨388629544957580552419297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2072690906440429612902917 388629544957580552419297)
                    ·
                      rfl

theorem cell23_2270560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 1, 4].length) (baseStart_2270560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270560 prefixEnd_2270560 := by exact prefixLift 2270560
  have htrace : WordTrace (prefixWord ++ tailWord_2270560) baseStart_2270560 baseEnd_2270560 := by
    simpa [prefixWord, tailWord_2270560, baseEnd_2270560] using wordTrace_append hprefix tailTrace_2270560
  have hstable : (prefixWord ++ tailWord_2270560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270560).length < 2 ^ (prefixWord ++ tailWord_2270560).sum := by decide
  have hdescent : baseEnd_2270560 < baseStart_2270560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270576 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 1, 5, 2]
def baseStart_2270576 : Nat := 118140960795 + 2270576 * 2 ^ 59
def prefixEnd_2270576 : Nat := 4983230072969 + 3 ^ 40 * 2270576 * 2
def baseEnd_2270576 : Nat := 1165896850563213594657817

theorem tailTrace_2270576 : CollatzResearch.WordTrace tailWord_2270576 prefixEnd_2270576 1165896850563213594657817 := by
  unfold tailWord_2270576
  simp only [CollatzResearch.WordTrace]
  refine ⟨41407355111049205176443791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55209806814732273568591721 41407355111049205176443791)
  ·
    refine ⟨62111032666573807764665687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41407355111049205176443791 62111032666573807764665687)
    ·
      refine ⟨93166548999860711646998531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62111032666573807764665687 93166548999860711646998531)
      ·
        refine ⟨139749823499791067470497797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93166548999860711646998531 139749823499791067470497797)
        ·
          refine ⟨26203091906210825150718337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139749823499791067470497797 26203091906210825150718337)
          ·
            refine ⟨19652318929658118863038753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26203091906210825150718337 19652318929658118863038753)
            ·
              refine ⟨14739239197243589147279065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19652318929658118863038753 14739239197243589147279065)
              ·
                refine ⟨11054429397932691860459299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14739239197243589147279065 11054429397932691860459299)
                ·
                  refine ⟨16581644096899037790688949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11054429397932691860459299 16581644096899037790688949)
                  ·
                    refine ⟨1554529134084284792877089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16581644096899037790688949 1554529134084284792877089)
                    ·
                      refine ⟨1165896850563213594657817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554529134084284792877089 1165896850563213594657817)
                      ·
                        rfl

theorem cell23_2270576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 5, 2].length) (baseStart_2270576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270576 prefixEnd_2270576 := by exact prefixLift 2270576
  have htrace : WordTrace (prefixWord ++ tailWord_2270576) baseStart_2270576 baseEnd_2270576 := by
    simpa [prefixWord, tailWord_2270576, baseEnd_2270576] using wordTrace_append hprefix tailTrace_2270576
  have hstable : (prefixWord ++ tailWord_2270576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270576).length < 2 ^ (prefixWord ++ tailWord_2270576).sum := by decide
  have hdescent : baseEnd_2270576 < baseStart_2270576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270600 : List Nat := [2, 1, 3, 3, 1, 2, 1, 5, 1, 1, 3]
def baseStart_2270600 : Nat := 118140960795 + 2270600 * 2 ^ 59
def prefixEnd_2270600 : Nat := 4983230072969 + 3 ^ 40 * 2270600 * 2
def baseEnd_2270600 : Nat := 1165909174098921500757707

theorem tailTrace_2270600 : CollatzResearch.WordTrace tailWord_2270600 prefixEnd_2270600 1165909174098921500757707 := by
  unfold tailWord_2270600
  simp only [CollatzResearch.WordTrace]
  refine ⟨41407792787005731225880627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55210390382674308301174169 41407792787005731225880627)
  ·
    refine ⟨62111689180508596838820941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41407792787005731225880627 62111689180508596838820941)
    ·
      refine ⟨23291883442690723814557853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62111689180508596838820941 23291883442690723814557853)
      ·
        refine ⟨8734456291009021430459195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23291883442690723814557853 8734456291009021430459195)
        ·
          refine ⟨13101684436513532145688793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8734456291009021430459195 13101684436513532145688793)
          ·
            refine ⟨9826263327385149109266595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13101684436513532145688793 9826263327385149109266595)
            ·
              refine ⟨14739394991077723663899893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9826263327385149109266595 14739394991077723663899893)
              ·
                refine ⟨1381818280413536593490615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14739394991077723663899893 1381818280413536593490615)
                ·
                  refine ⟨2072727420620304890235923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381818280413536593490615 2072727420620304890235923)
                  ·
                    refine ⟨3109091130930457335353885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2072727420620304890235923 3109091130930457335353885)
                    ·
                      refine ⟨1165909174098921500757707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3109091130930457335353885 1165909174098921500757707)
                      ·
                        rfl

theorem cell23_2270600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_2270600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270600 prefixEnd_2270600 := by exact prefixLift 2270600
  have htrace : WordTrace (prefixWord ++ tailWord_2270600) baseStart_2270600 baseEnd_2270600 := by
    simpa [prefixWord, tailWord_2270600, baseEnd_2270600] using wordTrace_append hprefix tailTrace_2270600
  have hstable : (prefixWord ++ tailWord_2270600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270600).length < 2 ^ (prefixWord ++ tailWord_2270600).sum := by decide
  have hdescent : baseEnd_2270600 < baseStart_2270600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270626 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2270626 : Nat := 118140960795 + 2270626 * 2 ^ 59
def prefixEnd_2270626 : Nat := 4983230072969 + 3 ^ 40 * 2270626 * 2
def baseEnd_2270626 : Nat := 1165922524595938399032587

theorem tailTrace_2270626 : CollatzResearch.WordTrace tailWord_2270626 prefixEnd_2270626 1165922524595938399032587 := by
  unfold tailWord_2270626
  simp only [CollatzResearch.WordTrace]
  refine ⟨20704133467979317223051933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55211022581278179261471821 20704133467979317223051933)
  ·
    refine ⟨7764050050492243958644475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20704133467979317223051933 7764050050492243958644475)
    ·
      refine ⟨11646075075738365937966713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7764050050492243958644475 11646075075738365937966713)
      ·
        refine ⟨8734556306803774453475035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11646075075738365937966713 8734556306803774453475035)
        ·
          refine ⟨13101834460205661680212553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8734556306803774453475035 13101834460205661680212553)
          ·
            refine ⟨9826375845154246260159415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13101834460205661680212553 9826375845154246260159415)
            ·
              refine ⟨14739563767731369390239123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9826375845154246260159415 14739563767731369390239123)
              ·
                refine ⟨22109345651597054085358685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14739563767731369390239123 22109345651597054085358685)
                ·
                  refine ⟨8291004619348895282009507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22109345651597054085358685 8291004619348895282009507)
                  ·
                    refine ⟨12436506929023342923014261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8291004619348895282009507 12436506929023342923014261)
                    ·
                      refine ⟨1165922524595938399032587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12436506929023342923014261 1165922524595938399032587)
                      ·
                        rfl

theorem cell23_2270626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2270626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270626 prefixEnd_2270626 := by exact prefixLift 2270626
  have htrace : WordTrace (prefixWord ++ tailWord_2270626) baseStart_2270626 baseEnd_2270626 := by
    simpa [prefixWord, tailWord_2270626, baseEnd_2270626] using wordTrace_append hprefix tailTrace_2270626
  have hstable : (prefixWord ++ tailWord_2270626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270626).length < 2 ^ (prefixWord ++ tailWord_2270626).sum := by decide
  have hdescent : baseEnd_2270626 < baseStart_2270626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270636 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 4]
def baseStart_2270636 : Nat := 118140960795 + 2270636 * 2 ^ 59
def prefixEnd_2270636 : Nat := 4983230072969 + 3 ^ 40 * 2270636 * 2
def baseEnd_2270636 : Nat := 1165927659402483359907541

theorem tailTrace_2270636 : CollatzResearch.WordTrace tailWord_2270636 prefixEnd_2270636 1165927659402483359907541 := by
  unfold tailWord_2270636
  simp only [CollatzResearch.WordTrace]
  refine ⟨41408449300940520300035881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55211265734587360400047841 41408449300940520300035881)
  ·
    refine ⟨31056336975705390225026911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41408449300940520300035881 31056336975705390225026911)
    ·
      refine ⟨46584505463558085337540367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31056336975705390225026911 46584505463558085337540367)
      ·
        refine ⟨69876758195337128006310551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46584505463558085337540367 69876758195337128006310551)
        ·
          refine ⟨104815137293005692009465827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69876758195337128006310551 104815137293005692009465827)
          ·
            refine ⟨157222705939508538014198741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104815137293005692009465827 157222705939508538014198741)
            ·
              refine ⟨3684907170457231359707783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 157222705939508538014198741 3684907170457231359707783)
              ·
                refine ⟨5527360755685847039561675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3684907170457231359707783 5527360755685847039561675)
                ·
                  refine ⟨8291041133528770559342513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5527360755685847039561675 8291041133528770559342513)
                  ·
                    refine ⟨6218280850146577919506885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8291041133528770559342513 6218280850146577919506885)
                    ·
                      refine ⟨1165927659402483359907541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6218280850146577919506885 1165927659402483359907541)
                      ·
                        rfl

theorem cell23_2270636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_2270636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270636 prefixEnd_2270636 := by exact prefixLift 2270636
  have htrace : WordTrace (prefixWord ++ tailWord_2270636) baseStart_2270636 baseEnd_2270636 := by
    simpa [prefixWord, tailWord_2270636, baseEnd_2270636] using wordTrace_append hprefix tailTrace_2270636
  have hstable : (prefixWord ++ tailWord_2270636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270636).length < 2 ^ (prefixWord ++ tailWord_2270636).sum := by decide
  have hdescent : baseEnd_2270636 < baseStart_2270636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270656 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 3]
def baseStart_2270656 : Nat := 118140960795 + 2270656 * 2 ^ 59
def prefixEnd_2270656 : Nat := 4983230072969 + 3 ^ 40 * 2270656 * 2
def baseEnd_2270656 : Nat := 1165937929015573281657449

theorem tailTrace_2270656 : CollatzResearch.WordTrace tailWord_2270656 prefixEnd_2270656 1165937929015573281657449 := by
  unfold tailWord_2270656
  simp only [CollatzResearch.WordTrace]
  refine ⟨41408814030904292007899911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55211752041205722677199881 41408814030904292007899911)
  ·
    refine ⟨62113221046356438011849867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41408814030904292007899911 62113221046356438011849867)
    ·
      refine ⟨93169831569534657017774801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62113221046356438011849867 93169831569534657017774801)
      ·
        refine ⟨69877373677150992763331101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93169831569534657017774801 69877373677150992763331101)
        ·
          refine ⟨26204015128931622286249163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69877373677150992763331101 26204015128931622286249163)
          ·
            refine ⟨39306022693397433429373745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26204015128931622286249163 39306022693397433429373745)
            ·
              refine ⟨29479517020048075072030309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39306022693397433429373745 29479517020048075072030309)
              ·
                refine ⟨5527409441259014076005683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29479517020048075072030309 5527409441259014076005683)
                ·
                  refine ⟨8291114161888521114008525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5527409441259014076005683 8291114161888521114008525)
                  ·
                    refine ⟨3109167810708195417753197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8291114161888521114008525 3109167810708195417753197)
                    ·
                      refine ⟨1165937929015573281657449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3109167810708195417753197 1165937929015573281657449)
                      ·
                        rfl

theorem cell23_2270656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_2270656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270656 prefixEnd_2270656 := by exact prefixLift 2270656
  have htrace : WordTrace (prefixWord ++ tailWord_2270656) baseStart_2270656 baseEnd_2270656 := by
    simpa [prefixWord, tailWord_2270656, baseEnd_2270656] using wordTrace_append hprefix tailTrace_2270656
  have hstable : (prefixWord ++ tailWord_2270656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270656).length < 2 ^ (prefixWord ++ tailWord_2270656).sum := by decide
  have hdescent : baseEnd_2270656 < baseStart_2270656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270660 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2270660 : Nat := 118140960795 + 2270660 * 2 ^ 59
def prefixEnd_2270660 : Nat := 4983230072969 + 3 ^ 40 * 2270660 * 2
def baseEnd_2270660 : Nat := 1165939982938191266007431

theorem tailTrace_2270660 : CollatzResearch.WordTrace tailWord_2270660 prefixEnd_2270660 1165939982938191266007431 := by
  unfold tailWord_2270660
  simp only [CollatzResearch.WordTrace]
  refine ⟨41408886976897046349472717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55211849302529395132630289 41408886976897046349472717)
  ·
    refine ⟨15528332616336392381052269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41408886976897046349472717 15528332616336392381052269)
    ·
      refine ⟨5823124731126147142894601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15528332616336392381052269 5823124731126147142894601)
      ·
        refine ⟨4367343548344610357170951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5823124731126147142894601 4367343548344610357170951)
        ·
          refine ⟨6551015322516915535756427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367343548344610357170951 6551015322516915535756427)
          ·
            refine ⟨9826522983775373303634641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6551015322516915535756427 9826522983775373303634641)
            ·
              refine ⟨7369892237831529977725981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9826522983775373303634641 7369892237831529977725981)
              ·
                refine ⟨2763709589186823741647243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7369892237831529977725981 2763709589186823741647243)
                ·
                  refine ⟨4145564383780235612470865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763709589186823741647243 4145564383780235612470865)
                  ·
                    refine ⟨3109173287835176709353149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4145564383780235612470865 3109173287835176709353149)
                    ·
                      refine ⟨1165939982938191266007431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3109173287835176709353149 1165939982938191266007431)
                      ·
                        rfl

theorem cell23_2270660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2270660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270660 prefixEnd_2270660 := by exact prefixLift 2270660
  have htrace : WordTrace (prefixWord ++ tailWord_2270660) baseStart_2270660 baseEnd_2270660 := by
    simpa [prefixWord, tailWord_2270660, baseEnd_2270660] using wordTrace_append hprefix tailTrace_2270660
  have hstable : (prefixWord ++ tailWord_2270660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270660).length < 2 ^ (prefixWord ++ tailWord_2270660).sum := by decide
  have hdescent : baseEnd_2270660 < baseStart_2270660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270716 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_2270716 : Nat := 118140960795 + 2270716 * 2 ^ 59
def prefixEnd_2270716 : Nat := 4983230072969 + 3 ^ 40 * 2270716 * 2
def baseEnd_2270716 : Nat := 1165968737854843046907173

theorem tailTrace_2270716 : CollatzResearch.WordTrace tailWord_2270716 prefixEnd_2270716 1165968737854843046907173 := by
  unfold tailWord_2270716
  simp only [CollatzResearch.WordTrace]
  refine ⟨41409908220795607131492001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55213210961060809508656001 41409908220795607131492001)
  ·
    refine ⟨31057431165596705348619001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41409908220795607131492001 31057431165596705348619001)
    ·
      refine ⟨23293073374197529011464251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31057431165596705348619001 23293073374197529011464251)
      ·
        refine ⟨34939610061296293517196377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23293073374197529011464251 34939610061296293517196377)
        ·
          refine ⟨26204707545972220137897283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34939610061296293517196377 26204707545972220137897283)
          ·
            refine ⟨39307061318958330206845925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26204707545972220137897283 39307061318958330206845925)
            ·
              refine ⟨7370073997304686913783611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39307061318958330206845925 7370073997304686913783611)
              ·
                refine ⟨11055110995957030370675417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7370073997304686913783611 11055110995957030370675417)
                ·
                  refine ⟨8291333246967772778006563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11055110995957030370675417 8291333246967772778006563)
                  ·
                    refine ⟨12436999870451659167009845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8291333246967772778006563 12436999870451659167009845)
                    ·
                      refine ⟨1165968737854843046907173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12436999870451659167009845 1165968737854843046907173)
                      ·
                        rfl

theorem cell23_2270716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_2270716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270716 prefixEnd_2270716 := by exact prefixLift 2270716
  have htrace : WordTrace (prefixWord ++ tailWord_2270716) baseStart_2270716 baseEnd_2270716 := by
    simpa [prefixWord, tailWord_2270716, baseEnd_2270716] using wordTrace_append hprefix tailTrace_2270716
  have hstable : (prefixWord ++ tailWord_2270716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270716).length < 2 ^ (prefixWord ++ tailWord_2270716).sum := by decide
  have hdescent : baseEnd_2270716 < baseStart_2270716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270717 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 1, 3, 2]
def baseStart_2270717 : Nat := 118140960795 + 2270717 * 2 ^ 59
def prefixEnd_2270717 : Nat := 4983230072969 + 3 ^ 40 * 2270717 * 2
def baseEnd_2270717 : Nat := 1165969251335497542994669

theorem tailTrace_2270717 : CollatzResearch.WordTrace tailWord_2270717 prefixEnd_2270717 1165969251335497542994669 := by
  unfold tailWord_2270717
  simp only [CollatzResearch.WordTrace]
  refine ⟨82819852914587591433770405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55213235276391727622513603 82819852914587591433770405)
  ·
    refine ⟨15528722421485173393831951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82819852914587591433770405 15528722421485173393831951)
    ·
      refine ⟨23293083632227760090747927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15528722421485173393831951 23293083632227760090747927)
      ·
        refine ⟨34939625448341640136121891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23293083632227760090747927 34939625448341640136121891)
        ·
          refine ⟨52409438172512460204182837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34939625448341640136121891 52409438172512460204182837)
          ·
            refine ⟨4913384828673043144142141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52409438172512460204182837 4913384828673043144142141)
            ·
              refine ⟨1842519310752391179053303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4913384828673043144142141 1842519310752391179053303)
              ·
                refine ⟨2763778966128586768579955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842519310752391179053303 2763778966128586768579955)
                ·
                  refine ⟨4145668449192880152869933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763778966128586768579955 4145668449192880152869933)
                  ·
                    refine ⟨1554625668447330057326225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4145668449192880152869933 1554625668447330057326225)
                    ·
                      refine ⟨1165969251335497542994669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554625668447330057326225 1165969251335497542994669)
                      ·
                        rfl

theorem cell23_2270717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_2270717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270717 prefixEnd_2270717 := by exact prefixLift 2270717
  have htrace : WordTrace (prefixWord ++ tailWord_2270717) baseStart_2270717 baseEnd_2270717 := by
    simpa [prefixWord, tailWord_2270717, baseEnd_2270717] using wordTrace_append hprefix tailTrace_2270717
  have hstable : (prefixWord ++ tailWord_2270717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270717).length < 2 ^ (prefixWord ++ tailWord_2270717).sum := by decide
  have hdescent : baseEnd_2270717 < baseStart_2270717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270719 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 11]
def baseStart_2270719 : Nat := 118140960795 + 2270719 * 2 ^ 59
def prefixEnd_2270719 : Nat := 4983230072969 + 3 ^ 40 * 2270719 * 2
def baseEnd_2270719 : Nat := 129552253144089615018851

theorem tailTrace_2270719 : CollatzResearch.WordTrace tailWord_2270719 prefixEnd_2270719 129552253144089615018851 := by
  unfold tailWord_2270719
  simp only [CollatzResearch.WordTrace]
  refine ⟨82819925860580345775343211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55213283907053563850228807 82819925860580345775343211)
  ·
    refine ⟨124229888790870518663014817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82819925860580345775343211 124229888790870518663014817)
    ·
      refine ⟨93172416593152888997261113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124229888790870518663014817 93172416593152888997261113)
      ·
        refine ⟨69879312444864666747945835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93172416593152888997261113 69879312444864666747945835)
        ·
          refine ⟨104818968667297000121918753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69879312444864666747945835 104818968667297000121918753)
          ·
            refine ⟨78614226500472750091439065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104818968667297000121918753 78614226500472750091439065)
            ·
              refine ⟨58960669875354562568579299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78614226500472750091439065 58960669875354562568579299)
              ·
                refine ⟨88441004813031843852868949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58960669875354562568579299 88441004813031843852868949)
                ·
                  refine ⟨129552253144089615018851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 88441004813031843852868949 129552253144089615018851)
                  ·
                    rfl

theorem cell23_2270719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 11].length) (baseStart_2270719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270719 prefixEnd_2270719 := by exact prefixLift 2270719
  have htrace : WordTrace (prefixWord ++ tailWord_2270719) baseStart_2270719 baseEnd_2270719 := by
    simpa [prefixWord, tailWord_2270719, baseEnd_2270719] using wordTrace_append hprefix tailTrace_2270719
  have hstable : (prefixWord ++ tailWord_2270719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270719).length < 2 ^ (prefixWord ++ tailWord_2270719).sum := by decide
  have hdescent : baseEnd_2270719 < baseStart_2270719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270740 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2270740 : Nat := 118140960795 + 2270740 * 2 ^ 59
def prefixEnd_2270740 : Nat := 4983230072969 + 3 ^ 40 * 2270740 * 2
def baseEnd_2270740 : Nat := 388660353796850317669021

theorem tailTrace_2270740 : CollatzResearch.WordTrace tailWord_2270740 prefixEnd_2270740 388660353796850317669021 := by
  unfold tailWord_2270740
  simp only [CollatzResearch.WordTrace]
  refine ⟨41410345896752133180928837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55213794529002844241238449 41410345896752133180928837)
  ·
    refine ⟨7764439855641024971424157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41410345896752133180928837 7764439855641024971424157)
    ·
      refine ⟨2911664945865384364284059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7764439855641024971424157 2911664945865384364284059)
      ·
        refine ⟨4367497418798076546426089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2911664945865384364284059 4367497418798076546426089)
        ·
          refine ⟨3275623064098557409819567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4367497418798076546426089 3275623064098557409819567)
          ·
            refine ⟨4913434596147836114729351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275623064098557409819567 4913434596147836114729351)
            ·
              refine ⟨7370151894221754172094027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913434596147836114729351 7370151894221754172094027)
              ·
                refine ⟨11055227841332631258141041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7370151894221754172094027 11055227841332631258141041)
                ·
                  refine ⟨8291420880999473443605781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11055227841332631258141041 8291420880999473443605781)
                  ·
                    refine ⟨388660353796850317669021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8291420880999473443605781 388660353796850317669021)
                    ·
                      rfl

theorem cell23_2270740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2270740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270740 prefixEnd_2270740 := by exact prefixLift 2270740
  have htrace : WordTrace (prefixWord ++ tailWord_2270740) baseStart_2270740 baseEnd_2270740 := by
    simpa [prefixWord, tailWord_2270740, baseEnd_2270740] using wordTrace_append hprefix tailTrace_2270740
  have hstable : (prefixWord ++ tailWord_2270740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270740).length < 2 ^ (prefixWord ++ tailWord_2270740).sum := by decide
  have hdescent : baseEnd_2270740 < baseStart_2270740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270781 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 2, 2, 2]
def baseStart_2270781 : Nat := 118140960795 + 2270781 * 2 ^ 59
def prefixEnd_2270781 : Nat := 4983230072969 + 3 ^ 40 * 2270781 * 2
def baseEnd_2270781 : Nat := 1166002114097385292594375

theorem tailTrace_2270781 : CollatzResearch.WordTrace tailWord_2270781 prefixEnd_2270781 1166002114097385292594375 := by
  unfold tailWord_2270781
  simp only [CollatzResearch.WordTrace]
  refine ⟨82822187186355730364100197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55214791457570486909400131 82822187186355730364100197)
  ·
    refine ⟨15529160097441699443268787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82822187186355730364100197 15529160097441699443268787)
    ·
      refine ⟨23293740146162549164903181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15529160097441699443268787 23293740146162549164903181)
      ·
        refine ⟨8735152554810955936838693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23293740146162549164903181 8735152554810955936838693)
        ·
          refine ⟨1637841104027054238157255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8735152554810955936838693 1637841104027054238157255)
          ·
            refine ⟨2456761656040581357235883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637841104027054238157255 2456761656040581357235883)
            ·
              refine ⟨3685142484060872035853825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456761656040581357235883 3685142484060872035853825)
              ·
                refine ⟨2763856863045654026890369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3685142484060872035853825 2763856863045654026890369)
                ·
                  refine ⟨2072892647284240520167777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2763856863045654026890369 2072892647284240520167777)
                  ·
                    refine ⟨1554669485463180390125833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2072892647284240520167777 1554669485463180390125833)
                    ·
                      refine ⟨1166002114097385292594375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554669485463180390125833 1166002114097385292594375)
                      ·
                        rfl

theorem cell23_2270781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_2270781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270781 prefixEnd_2270781 := by exact prefixLift 2270781
  have htrace : WordTrace (prefixWord ++ tailWord_2270781) baseStart_2270781 baseEnd_2270781 := by
    simpa [prefixWord, tailWord_2270781, baseEnd_2270781] using wordTrace_append hprefix tailTrace_2270781
  have hstable : (prefixWord ++ tailWord_2270781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270781).length < 2 ^ (prefixWord ++ tailWord_2270781).sum := by decide
  have hdescent : baseEnd_2270781 < baseStart_2270781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270816 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2270816 : Nat := 118140960795 + 2270816 * 2 ^ 59
def prefixEnd_2270816 : Nat := 4983230072969 + 3 ^ 40 * 2270816 * 2
def baseEnd_2270816 : Nat := 1166020085920292655656713

theorem tailTrace_2270816 : CollatzResearch.WordTrace tailWord_2270816 prefixEnd_2270816 1166020085920292655656713 := by
  unfold tailWord_2270816
  simp only [CollatzResearch.WordTrace]
  refine ⟨41411731870614465670812151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55215642494152620894416201 41411731870614465670812151)
  ·
    refine ⟨62117597805921698506218227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41411731870614465670812151 62117597805921698506218227)
    ·
      refine ⟨93176396708882547759327341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62117597805921698506218227 93176396708882547759327341)
      ·
        refine ⟨34941148765830955409747753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93176396708882547759327341 34941148765830955409747753)
        ·
          refine ⟨26205861574373216557310815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34941148765830955409747753 26205861574373216557310815)
          ·
            refine ⟨39308792361559824835966223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26205861574373216557310815 39308792361559824835966223)
            ·
              refine ⟨58963188542339737253949335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39308792361559824835966223 58963188542339737253949335)
              ·
                refine ⟨88444782813509605880924003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58963188542339737253949335 88444782813509605880924003)
                ·
                  refine ⟨132667174220264408821386005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88444782813509605880924003 132667174220264408821386005)
                  ·
                    refine ⟨6218773791574894163502469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 132667174220264408821386005 6218773791574894163502469)
                    ·
                      refine ⟨1166020085920292655656713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6218773791574894163502469 1166020085920292655656713)
                      ·
                        rfl

theorem cell23_2270816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2270816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270816 prefixEnd_2270816 := by exact prefixLift 2270816
  have htrace : WordTrace (prefixWord ++ tailWord_2270816) baseStart_2270816 baseEnd_2270816 := by
    simpa [prefixWord, tailWord_2270816, baseEnd_2270816] using wordTrace_append hprefix tailTrace_2270816
  have hstable : (prefixWord ++ tailWord_2270816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270816).length < 2 ^ (prefixWord ++ tailWord_2270816).sum := by decide
  have hdescent : baseEnd_2270816 < baseStart_2270816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270823 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_2270823 : Nat := 118140960795 + 2270823 * 2 ^ 59
def prefixEnd_2270823 : Nat := 4983230072969 + 3 ^ 40 * 2270823 * 2
def baseEnd_2270823 : Nat := 1166023680284874128269181

theorem tailTrace_2270823 : CollatzResearch.WordTrace tailWord_2270823 prefixEnd_2270823 1166023680284874128269181 := by
  unfold tailWord_2270823
  simp only [CollatzResearch.WordTrace]
  refine ⟨82823719052203571537129123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55215812701469047691419415 82823719052203571537129123)
  ·
    refine ⟨124235578578305357305693685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82823719052203571537129123 124235578578305357305693685)
    ·
      refine ⟨11647085491716127247408783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124235578578305357305693685 11647085491716127247408783)
      ·
        refine ⟨17470628237574190871113175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11647085491716127247408783 17470628237574190871113175)
        ·
          refine ⟨26205942356361286306669763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17470628237574190871113175 26205942356361286306669763)
          ·
            refine ⟨39308913534541929460004645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26205942356361286306669763 39308913534541929460004645)
            ·
              refine ⟨7370421287726611773750871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39308913534541929460004645 7370421287726611773750871)
              ·
                refine ⟨11055631931589917660626307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7370421287726611773750871 11055631931589917660626307)
                ·
                  refine ⟨16583447897384876490939461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11055631931589917660626307 16583447897384876490939461)
                  ·
                    refine ⟨3109396480759664342051149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16583447897384876490939461 3109396480759664342051149)
                    ·
                      refine ⟨1166023680284874128269181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3109396480759664342051149 1166023680284874128269181)
                      ·
                        rfl

theorem cell23_2270823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_2270823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270823 prefixEnd_2270823 := by exact prefixLift 2270823
  have htrace : WordTrace (prefixWord ++ tailWord_2270823) baseStart_2270823 baseEnd_2270823 := by
    simpa [prefixWord, tailWord_2270823, baseEnd_2270823] using wordTrace_append hprefix tailTrace_2270823
  have hstable : (prefixWord ++ tailWord_2270823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270823).length < 2 ^ (prefixWord ++ tailWord_2270823).sum := by decide
  have hdescent : baseEnd_2270823 < baseStart_2270823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270873 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 1, 5]
def baseStart_2270873 : Nat := 118140960795 + 2270873 * 2 ^ 59
def prefixEnd_2270873 : Nat := 4983230072969 + 3 ^ 40 * 2270873 * 2
def baseEnd_2270873 : Nat := 388683118105866310881317

theorem tailTrace_2270873 : CollatzResearch.WordTrace tailWord_2270873 prefixEnd_2270873 388683118105866310881317 := by
  unfold tailWord_2270873
  simp only [CollatzResearch.WordTrace]
  refine ⟨82825542702022430076449273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55217028468014953384299515 82825542702022430076449273)
  ·
    refine ⟨62119157026516822557336955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82825542702022430076449273 62119157026516822557336955)
    ·
      refine ⟨93178735539775233836005433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62119157026516822557336955 93178735539775233836005433)
      ·
        refine ⟨69884051654831425377004075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93178735539775233836005433 69884051654831425377004075)
        ·
          refine ⟨104826077482247138065506113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69884051654831425377004075 104826077482247138065506113)
          ·
            refine ⟨78619558111685353549129585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104826077482247138065506113 78619558111685353549129585)
            ·
              refine ⟨58964668583764015161847189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78619558111685353549129585 58964668583764015161847189)
              ·
                refine ⟨2763968839863938210711587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58964668583764015161847189 2763968839863938210711587)
                ·
                  refine ⟨4145953259795907316067381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763968839863938210711587 4145953259795907316067381)
                  ·
                    refine ⟨388683118105866310881317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4145953259795907316067381 388683118105866310881317)
                    ·
                      rfl

theorem cell23_2270873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 5].length) (baseStart_2270873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270873 prefixEnd_2270873 := by exact prefixLift 2270873
  have htrace : WordTrace (prefixWord ++ tailWord_2270873) baseStart_2270873 baseEnd_2270873 := by
    simpa [prefixWord, tailWord_2270873, baseEnd_2270873] using wordTrace_append hprefix tailTrace_2270873
  have hstable : (prefixWord ++ tailWord_2270873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270873).length < 2 ^ (prefixWord ++ tailWord_2270873).sum := by decide
  have hdescent : baseEnd_2270873 < baseStart_2270873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270910 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_2270910 : Nat := 118140960795 + 2270910 * 2 ^ 59
def prefixEnd_2270910 : Nat := 4983230072969 + 3 ^ 40 * 2270910 * 2
def baseEnd_2270910 : Nat := 1166068353101815287881281

theorem tailTrace_2270910 : CollatzResearch.WordTrace tailWord_2270910 prefixEnd_2270910 1166068353101815287881281 := by
  unfold tailWord_2270910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10353361525361048174443273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55217928135258923597030789 10353361525361048174443273)
  ·
    refine ⟨7765021144020786130832455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10353361525361048174443273 7765021144020786130832455)
    ·
      refine ⟨11647531716031179196248683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7765021144020786130832455 11647531716031179196248683)
      ·
        refine ⟨17471297574046768794373025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11647531716031179196248683 17471297574046768794373025)
        ·
          refine ⟨13103473180535076595779769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17471297574046768794373025 13103473180535076595779769)
          ·
            refine ⟨9827604885401307446834827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13103473180535076595779769 9827604885401307446834827)
            ·
              refine ⟨14741407328101961170252241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9827604885401307446834827 14741407328101961170252241)
              ·
                refine ⟨11056055496076470877689181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14741407328101961170252241 11056055496076470877689181)
                ·
                  refine ⟨4146020811028676579133443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11056055496076470877689181 4146020811028676579133443)
                  ·
                    refine ⟨6219031216543014868700165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4146020811028676579133443 6219031216543014868700165)
                    ·
                      refine ⟨1166068353101815287881281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6219031216543014868700165 1166068353101815287881281)
                      ·
                        rfl

theorem cell23_2270910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_2270910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270910 prefixEnd_2270910 := by exact prefixLift 2270910
  have htrace : WordTrace (prefixWord ++ tailWord_2270910) baseStart_2270910 baseEnd_2270910 := by
    simpa [prefixWord, tailWord_2270910, baseEnd_2270910] using wordTrace_append hprefix tailTrace_2270910
  have hstable : (prefixWord ++ tailWord_2270910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270910).length < 2 ^ (prefixWord ++ tailWord_2270910).sum := by decide
  have hdescent : baseEnd_2270910 < baseStart_2270910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270920 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 2, 4]
def baseStart_2270920 : Nat := 118140960795 + 2270920 * 2 ^ 59
def prefixEnd_2270920 : Nat := 4983230072969 + 3 ^ 40 * 2270920 * 2
def baseEnd_2270920 : Nat := 388691162636120082918745

theorem tailTrace_2270920 : CollatzResearch.WordTrace tailWord_2270920 prefixEnd_2270920 388691162636120082918745 := by
  unfold tailWord_2270920
  simp only [CollatzResearch.WordTrace]
  refine ⟨41413628466426078551705107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55218171288568104735606809 41413628466426078551705107)
  ·
    refine ⟨62120442699639117827557661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41413628466426078551705107 62120442699639117827557661)
    ·
      refine ⟨23295166012364669185334123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62120442699639117827557661 23295166012364669185334123)
      ·
        refine ⟨34942749018547003778001185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23295166012364669185334123 34942749018547003778001185)
        ·
          refine ⟨26207061763910252833500889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34942749018547003778001185 26207061763910252833500889)
          ·
            refine ⟨19655296322932689625125667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26207061763910252833500889 19655296322932689625125667)
            ·
              refine ⟨29482944484399034437688501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19655296322932689625125667 29482944484399034437688501)
              ·
                refine ⟨2764026045412409478533297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29482944484399034437688501 2764026045412409478533297)
                ·
                  refine ⟨2073019534059307108899973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2764026045412409478533297 2073019534059307108899973)
                  ·
                    refine ⟨388691162636120082918745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2073019534059307108899973 388691162636120082918745)
                    ·
                      rfl

theorem cell23_2270920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_2270920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270920 prefixEnd_2270920 := by exact prefixLift 2270920
  have htrace : WordTrace (prefixWord ++ tailWord_2270920) baseStart_2270920 baseEnd_2270920 := by
    simpa [prefixWord, tailWord_2270920, baseEnd_2270920] using wordTrace_append hprefix tailTrace_2270920
  have hstable : (prefixWord ++ tailWord_2270920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270920).length < 2 ^ (prefixWord ++ tailWord_2270920).sum := by decide
  have hdescent : baseEnd_2270920 < baseStart_2270920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270941 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2270941 : Nat := 118140960795 + 2270941 * 2 ^ 59
def prefixEnd_2270941 : Nat := 4983230072969 + 3 ^ 40 * 2270941 * 2
def baseEnd_2270941 : Nat := 388694757000701555531213

theorem tailTrace_2270941 : CollatzResearch.WordTrace tailWord_2270941 prefixEnd_2270941 388694757000701555531213 := by
  unfold tailWord_2270941
  simp only [CollatzResearch.WordTrace]
  refine ⟨82828022865776077689924677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55218681910517385126616451 82828022865776077689924677)
  ·
    refine ⟨15530254287333014566860877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82828022865776077689924677 15530254287333014566860877)
    ·
      refine ⟨5823845357749880462572829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15530254287333014566860877 5823845357749880462572829)
      ·
        refine ⟨2183942009156205173464811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5823845357749880462572829 2183942009156205173464811)
        ·
          refine ⟨3275913013734307760197217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183942009156205173464811 3275913013734307760197217)
          ·
            refine ⟨2456934760300730820147913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3275913013734307760197217 2456934760300730820147913)
            ·
              refine ⟨1842701070225548115110935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2456934760300730820147913 1842701070225548115110935)
              ·
                refine ⟨2764051605338322172666403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842701070225548115110935 2764051605338322172666403)
                ·
                  refine ⟨4146077408007483258999605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764051605338322172666403 4146077408007483258999605)
                  ·
                    refine ⟨388694757000701555531213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4146077408007483258999605 388694757000701555531213)
                    ·
                      rfl

theorem cell23_2270941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2270941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270941 prefixEnd_2270941 := by exact prefixLift 2270941
  have htrace : WordTrace (prefixWord ++ tailWord_2270941) baseStart_2270941 baseEnd_2270941 := by
    simpa [prefixWord, tailWord_2270941, baseEnd_2270941] using wordTrace_append hprefix tailTrace_2270941
  have hstable : (prefixWord ++ tailWord_2270941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270941).length < 2 ^ (prefixWord ++ tailWord_2270941).sum := by decide
  have hdescent : baseEnd_2270941 < baseStart_2270941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270944 : List Nat := [2, 1, 1, 3, 1, 2, 3, 5, 1, 2, 2]
def baseStart_2270944 : Nat := 118140960795 + 2270944 * 2 ^ 59
def prefixEnd_2270944 : Nat := 4983230072969 + 3 ^ 40 * 2270944 * 2
def baseEnd_2270944 : Nat := 1166085811444068154856125

theorem tailTrace_2270944 : CollatzResearch.WordTrace tailWord_2270944 prefixEnd_2270944 1166085811444068154856125 := by
  unfold tailWord_2270944
  simp only [CollatzResearch.WordTrace]
  refine ⟨41414066142382604601141943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55218754856510139468189257 41414066142382604601141943)
  ·
    refine ⟨62121099213573906901712915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41414066142382604601141943 62121099213573906901712915)
    ·
      refine ⟨93181648820360860352569373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62121099213573906901712915 93181648820360860352569373)
      ·
        refine ⟨34943118307635322632213515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93181648820360860352569373 34943118307635322632213515)
        ·
          refine ⟨52414677461452983948320273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34943118307635322632213515 52414677461452983948320273)
          ·
            refine ⟨39311008096089737961240205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52414677461452983948320273 39311008096089737961240205)
            ·
              refine ⟨14741628036033651735465077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39311008096089737961240205 14741628036033651735465077)
              ·
                refine ⟨1382027628378154850199851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14741628036033651735465077 1382027628378154850199851)
                ·
                  refine ⟨2073041442567232275299777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382027628378154850199851 2073041442567232275299777)
                  ·
                    refine ⟨1554781081925424206474833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2073041442567232275299777 1554781081925424206474833)
                    ·
                      refine ⟨1166085811444068154856125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554781081925424206474833 1166085811444068154856125)
                      ·
                        rfl

theorem cell23_2270944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_2270944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270944 prefixEnd_2270944 := by exact prefixLift 2270944
  have htrace : WordTrace (prefixWord ++ tailWord_2270944) baseStart_2270944 baseEnd_2270944 := by
    simpa [prefixWord, tailWord_2270944, baseEnd_2270944] using wordTrace_append hprefix tailTrace_2270944
  have hstable : (prefixWord ++ tailWord_2270944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270944).length < 2 ^ (prefixWord ++ tailWord_2270944).sum := by decide
  have hdescent : baseEnd_2270944 < baseStart_2270944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270964 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2270964 : Nat := 118140960795 + 2270964 * 2 ^ 59
def prefixEnd_2270964 : Nat := 4983230072969 + 3 ^ 40 * 2270964 * 2
def baseEnd_2270964 : Nat := 1166096081057158076606033

theorem tailTrace_2270964 : CollatzResearch.WordTrace tailWord_2270964 prefixEnd_2270964 1166096081057158076606033 := by
  unfold tailWord_2270964
  simp only [CollatzResearch.WordTrace]
  refine ⟨41414430872346376309005973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55219241163128501745341297 41414430872346376309005973)
  ·
    refine ⟨1941301447141236389484655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41414430872346376309005973 1941301447141236389484655)
    ·
      refine ⟨2911952170711854584226983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1941301447141236389484655 2911952170711854584226983)
      ·
        refine ⟨4367928256067781876340475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2911952170711854584226983 4367928256067781876340475)
        ·
          refine ⟨6551892384101672814510713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367928256067781876340475 6551892384101672814510713)
          ·
            refine ⟨4913919288076254610883035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6551892384101672814510713 4913919288076254610883035)
            ·
              refine ⟨7370878932114381916324553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913919288076254610883035 7370878932114381916324553)
              ·
                refine ⟨5528159199085786437243415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7370878932114381916324553 5528159199085786437243415)
                ·
                  refine ⟨8292238798628679655865123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5528159199085786437243415 8292238798628679655865123)
                  ·
                    refine ⟨12438358197943019483797685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8292238798628679655865123 12438358197943019483797685)
                    ·
                      refine ⟨1166096081057158076606033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12438358197943019483797685 1166096081057158076606033)
                      ·
                        rfl

theorem cell23_2270964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2270964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270964 prefixEnd_2270964 := by exact prefixLift 2270964
  have htrace : WordTrace (prefixWord ++ tailWord_2270964) baseStart_2270964 baseEnd_2270964 := by
    simpa [prefixWord, tailWord_2270964, baseEnd_2270964] using wordTrace_append hprefix tailTrace_2270964
  have hstable : (prefixWord ++ tailWord_2270964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270964).length < 2 ^ (prefixWord ++ tailWord_2270964).sum := by decide
  have hdescent : baseEnd_2270964 < baseStart_2270964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270974 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_2270974 : Nat := 118140960795 + 2270974 * 2 ^ 59
def prefixEnd_2270974 : Nat := 4983230072969 + 3 ^ 40 * 2270974 * 2
def baseEnd_2270974 : Nat := 1166101215863703037480987

theorem tailTrace_2270974 : CollatzResearch.WordTrace tailWord_2270974 prefixEnd_2270974 1166101215863703037480987 := by
  unfold tailWord_2270974
  simp only [CollatzResearch.WordTrace]
  refine ⟨10353653309332065540734497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55219484316437682883917317 10353653309332065540734497)
  ·
    refine ⟨7765239981999049155550873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10353653309332065540734497 7765239981999049155550873)
    ·
      refine ⟨5823929986499286866663155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7765239981999049155550873 5823929986499286866663155)
      ·
        refine ⟨8735894979748930299994733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5823929986499286866663155 8735894979748930299994733)
        ·
          refine ⟨3275960617405848862498025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8735894979748930299994733 3275960617405848862498025)
          ·
            refine ⟨2456970463054386646873519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3275960617405848862498025 2456970463054386646873519)
            ·
              refine ⟨3685455694581579970310279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456970463054386646873519 3685455694581579970310279)
              ·
                refine ⟨5528183541872369955465419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3685455694581579970310279 5528183541872369955465419)
                ·
                  refine ⟨8292275312808554933198129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5528183541872369955465419 8292275312808554933198129)
                  ·
                    refine ⟨6219206484606416199898597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8292275312808554933198129 6219206484606416199898597)
                    ·
                      refine ⟨1166101215863703037480987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6219206484606416199898597 1166101215863703037480987)
                      ·
                        rfl

theorem cell23_2270974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_2270974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270974 prefixEnd_2270974 := by exact prefixLift 2270974
  have htrace : WordTrace (prefixWord ++ tailWord_2270974) baseStart_2270974 baseEnd_2270974 := by
    simpa [prefixWord, tailWord_2270974, baseEnd_2270974] using wordTrace_append hprefix tailTrace_2270974
  have hstable : (prefixWord ++ tailWord_2270974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270974).length < 2 ^ (prefixWord ++ tailWord_2270974).sum := by decide
  have hdescent : baseEnd_2270974 < baseStart_2270974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270977 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_2270977 : Nat := 118140960795 + 2270977 * 2 ^ 59
def prefixEnd_2270977 : Nat := 4983230072969 + 3 ^ 40 * 2270977 * 2
def baseEnd_2270977 : Nat := 1166102756305666525743473

theorem tailTrace_2270977 : CollatzResearch.WordTrace tailWord_2270977 prefixEnd_2270977 1166102756305666525743473 := by
  unfold tailWord_2270977
  simp only [CollatzResearch.WordTrace]
  refine ⟨82829335893645655838235185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55219557262430437225490123 82829335893645655838235185)
  ·
    refine ⟨62122001920234241878676389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82829335893645655838235185 62122001920234241878676389)
    ·
      refine ⟨11647875360043920352251823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62122001920234241878676389 11647875360043920352251823)
      ·
        refine ⟨17471813040065880528377735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11647875360043920352251823 17471813040065880528377735)
        ·
          refine ⟨26207719560098820792566603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17471813040065880528377735 26207719560098820792566603)
          ·
            refine ⟨39311579340148231188849905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26207719560098820792566603 39311579340148231188849905)
            ·
              refine ⟨29483684505111173391637429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39311579340148231188849905 29483684505111173391637429)
              ·
                refine ⟨2764095422354172505466009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29483684505111173391637429 2764095422354172505466009)
                ·
                  refine ⟨2073071566765629379099507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2764095422354172505466009 2073071566765629379099507)
                  ·
                    refine ⟨3109607350148444068649261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2073071566765629379099507 3109607350148444068649261)
                    ·
                      refine ⟨1166102756305666525743473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3109607350148444068649261 1166102756305666525743473)
                      ·
                        rfl

theorem cell23_2270977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_2270977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270977 prefixEnd_2270977 := by exact prefixLift 2270977
  have htrace : WordTrace (prefixWord ++ tailWord_2270977) baseStart_2270977 baseEnd_2270977 := by
    simpa [prefixWord, tailWord_2270977, baseEnd_2270977] using wordTrace_append hprefix tailTrace_2270977
  have hstable : (prefixWord ++ tailWord_2270977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270977).length < 2 ^ (prefixWord ++ tailWord_2270977).sum := by decide
  have hdescent : baseEnd_2270977 < baseStart_2270977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270987 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 1, 3, 2]
def baseStart_2270987 : Nat := 118140960795 + 2270987 * 2 ^ 59
def prefixEnd_2270987 : Nat := 4983230072969 + 3 ^ 40 * 2270987 * 2
def baseEnd_2270987 : Nat := 1166107891112211486618427

theorem tailTrace_2270987 : CollatzResearch.WordTrace tailWord_2270987 prefixEnd_2270987 1166107891112211486618427 := by
  unfold tailWord_2270987
  simp only [CollatzResearch.WordTrace]
  refine ⟨82829700623609427546099215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55219800415739618364066143 82829700623609427546099215)
  ·
    refine ⟨124244550935414141319148823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82829700623609427546099215 124244550935414141319148823)
    ·
      refine ⟨186366826403121211978723235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124244550935414141319148823 186366826403121211978723235)
      ·
        refine ⟨279550239604681817968084853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186366826403121211978723235 279550239604681817968084853)
        ·
          refine ⟨26207834962938920434507955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 279550239604681817968084853 26207834962938920434507955)
          ·
            refine ⟨39311752444408380651761933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26207834962938920434507955 39311752444408380651761933)
            ·
              refine ⟨14741907166653142744410725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39311752444408380651761933 14741907166653142744410725)
              ·
                refine ⟨2764107593747464264577011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14741907166653142744410725 2764107593747464264577011)
                ·
                  refine ⟨4146161390621196396865517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764107593747464264577011 4146161390621196396865517)
                  ·
                    refine ⟨1554810521482948648824569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4146161390621196396865517 1554810521482948648824569)
                    ·
                      refine ⟨1166107891112211486618427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554810521482948648824569 1166107891112211486618427)
                      ·
                        rfl

theorem cell23_2270987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 3, 2].length) (baseStart_2270987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270987 prefixEnd_2270987 := by exact prefixLift 2270987
  have htrace : WordTrace (prefixWord ++ tailWord_2270987) baseStart_2270987 baseEnd_2270987 := by
    simpa [prefixWord, tailWord_2270987, baseEnd_2270987] using wordTrace_append hprefix tailTrace_2270987
  have hstable : (prefixWord ++ tailWord_2270987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270987).length < 2 ^ (prefixWord ++ tailWord_2270987).sum := by decide
  have hdescent : baseEnd_2270987 < baseStart_2270987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270989 : List Nat := [1, 7, 2, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2270989 : Nat := 118140960795 + 2270989 * 2 ^ 59
def prefixEnd_2270989 : Nat := 4983230072969 + 3 ^ 40 * 2270989 * 2
def baseEnd_2270989 : Nat := 1166108918073520478793419

theorem tailTrace_2270989 : CollatzResearch.WordTrace tailWord_2270989 prefixEnd_2270989 1166108918073520478793419 := by
  unfold tailWord_2270989
  simp only [CollatzResearch.WordTrace]
  refine ⟨82829773569602181887672021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55219849046401454591781347 82829773569602181887672021)
  ·
    refine ⟨1941322818037551137992313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 82829773569602181887672021 1941322818037551137992313)
    ·
      refine ⟨1455992113528163353494235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1941322818037551137992313 1455992113528163353494235)
      ·
        refine ⟨2183988170292245030241353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1455992113528163353494235 2183988170292245030241353)
        ·
          refine ⟨1637991127719183772681015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2183988170292245030241353 1637991127719183772681015)
          ·
            refine ⟨2456986691578775659021523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637991127719183772681015 2456986691578775659021523)
            ·
              refine ⟨3685480037368163488532285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456986691578775659021523 3685480037368163488532285)
              ·
                refine ⟨1382055014013061308199607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3685480037368163488532285 1382055014013061308199607)
                ·
                  refine ⟨2073082521019591962299411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382055014013061308199607 2073082521019591962299411)
                  ·
                    refine ⟨3109623781529387943449117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2073082521019591962299411 3109623781529387943449117)
                    ·
                      refine ⟨1166108918073520478793419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3109623781529387943449117 1166108918073520478793419)
                      ·
                        rfl

theorem cell23_2270989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2270989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270989 prefixEnd_2270989 := by exact prefixLift 2270989
  have htrace : WordTrace (prefixWord ++ tailWord_2270989) baseStart_2270989 baseEnd_2270989 := by
    simpa [prefixWord, tailWord_2270989, baseEnd_2270989] using wordTrace_append hprefix tailTrace_2270989
  have hstable : (prefixWord ++ tailWord_2270989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270989).length < 2 ^ (prefixWord ++ tailWord_2270989).sum := by decide
  have hdescent : baseEnd_2270989 < baseStart_2270989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270994 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2270994 : Nat := 118140960795 + 2270994 * 2 ^ 59
def prefixEnd_2270994 : Nat := 4983230072969 + 3 ^ 40 * 2270994 * 2
def baseEnd_2270994 : Nat := 1166111485476792959230895

theorem tailTrace_2270994 : CollatzResearch.WordTrace tailWord_2270994 prefixEnd_2270994 1166111485476792959230895 := by
  unfold tailWord_2270994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20707488983646016935401009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55219970623056045161069357 20707488983646016935401009)
  ·
    refine ⟨15530616737734512701550757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20707488983646016935401009 15530616737734512701550757)
    ·
      refine ⟨2911990638325221131540767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15530616737734512701550757 2911990638325221131540767)
      ·
        refine ⟨4367985957487831697311151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2911990638325221131540767 4367985957487831697311151)
        ·
          refine ⟨6551978936231747545966727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367985957487831697311151 6551978936231747545966727)
          ·
            refine ⟨9827968404347621318950091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6551978936231747545966727 9827968404347621318950091)
            ·
              refine ⟨14741952606521431978425137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9827968404347621318950091 14741952606521431978425137)
              ·
                refine ⟨11056464454891073983818853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14741952606521431978425137 11056464454891073983818853)
                ·
                  refine ⟨2073087085292076371966035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11056464454891073983818853 2073087085292076371966035)
                  ·
                    refine ⟨3109630627938114557949053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2073087085292076371966035 3109630627938114557949053)
                    ·
                      refine ⟨1166111485476792959230895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3109630627938114557949053 1166111485476792959230895)
                      ·
                        rfl

theorem cell23_2270994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2270994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270994 prefixEnd_2270994 := by exact prefixLift 2270994
  have htrace : WordTrace (prefixWord ++ tailWord_2270994) baseStart_2270994 baseEnd_2270994 := by
    simpa [prefixWord, tailWord_2270994, baseEnd_2270994] using wordTrace_append hprefix tailTrace_2270994
  have hstable : (prefixWord ++ tailWord_2270994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270994).length < 2 ^ (prefixWord ++ tailWord_2270994).sum := by decide
  have hdescent : baseEnd_2270994 < baseStart_2270994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271003 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 5]
def baseStart_2271003 : Nat := 118140960795 + 2271003 * 2 ^ 59
def prefixEnd_2271003 : Nat := 4983230072969 + 3 ^ 40 * 2271003 * 2
def baseEnd_2271003 : Nat := 1166116106802683424018353

theorem tailTrace_2271003 : CollatzResearch.WordTrace tailWord_2271003 prefixEnd_2271003 1166116106802683424018353 := by
  unfold tailWord_2271003
  simp only [CollatzResearch.WordTrace]
  refine ⟨82830284191551462278681663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55220189461034308185787775 82830284191551462278681663)
  ·
    refine ⟨124245426287327193418022495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82830284191551462278681663 124245426287327193418022495)
    ·
      refine ⟨186368139430990790127033743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124245426287327193418022495 186368139430990790127033743)
      ·
        refine ⟨279552209146486185190550615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186368139430990790127033743 279552209146486185190550615)
        ·
          refine ⟨419328313719729277785825923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279552209146486185190550615 419328313719729277785825923)
          ·
            refine ⟨628992470579593916678738885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419328313719729277785825923 628992470579593916678738885)
            ·
              refine ⟨117936088233673859377263541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 628992470579593916678738885 117936088233673859377263541)
              ·
                refine ⟨11056508271906924316618457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117936088233673859377263541 11056508271906924316618457)
                ·
                  refine ⟨8292381203930193237463843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11056508271906924316618457 8292381203930193237463843)
                  ·
                    refine ⟨12438571805895289856195765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8292381203930193237463843 12438571805895289856195765)
                    ·
                      refine ⟨1166116106802683424018353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12438571805895289856195765 1166116106802683424018353)
                      ·
                        rfl

theorem cell23_2271003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 5].length) (baseStart_2271003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271003 prefixEnd_2271003 := by exact prefixLift 2271003
  have htrace : WordTrace (prefixWord ++ tailWord_2271003) baseStart_2271003 baseEnd_2271003 := by
    simpa [prefixWord, tailWord_2271003, baseEnd_2271003] using wordTrace_append hprefix tailTrace_2271003
  have hstable : (prefixWord ++ tailWord_2271003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271003).length < 2 ^ (prefixWord ++ tailWord_2271003).sum := by decide
  have hdescent : baseEnd_2271003 < baseStart_2271003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271028 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_2271028 : Nat := 118140960795 + 2271028 * 2 ^ 59
def prefixEnd_2271028 : Nat := 4983230072969 + 3 ^ 40 * 2271028 * 2
def baseEnd_2271028 : Nat := 1166128943819045826205739

theorem tailTrace_2271028 : CollatzResearch.WordTrace tailWord_2271028 prefixEnd_2271028 1166128943819045826205739 := by
  unfold tailWord_2271028
  simp only [CollatzResearch.WordTrace]
  refine ⟨41415598008230445774170869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55220797344307261032227825 41415598008230445774170869)
  ·
    refine ⟨3882712313271604291328519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41415598008230445774170869 3882712313271604291328519)
    ·
      refine ⟨5824068469907406436992779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3882712313271604291328519 5824068469907406436992779)
      ·
        refine ⟨8736102704861109655489169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5824068469907406436992779 8736102704861109655489169)
        ·
          refine ⟨6552077028645832241616877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8736102704861109655489169 6552077028645832241616877)
          ·
            refine ⟨2457028885742187090606329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6552077028645832241616877 2457028885742187090606329)
            ·
              refine ⟨1842771664306640317954747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2457028885742187090606329 1842771664306640317954747)
              ·
                refine ⟨2764157496459960476932121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842771664306640317954747 2764157496459960476932121)
                ·
                  refine ⟨2073118122344970357699091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2764157496459960476932121 2073118122344970357699091)
                  ·
                    refine ⟨3109677183517455536548637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2073118122344970357699091 3109677183517455536548637)
                    ·
                      refine ⟨1166128943819045826205739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3109677183517455536548637 1166128943819045826205739)
                      ·
                        rfl

theorem cell23_2271028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_2271028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271028 prefixEnd_2271028 := by exact prefixLift 2271028
  have htrace : WordTrace (prefixWord ++ tailWord_2271028) baseStart_2271028 baseEnd_2271028 := by
    simpa [prefixWord, tailWord_2271028, baseEnd_2271028] using wordTrace_append hprefix tailTrace_2271028
  have hstable : (prefixWord ++ tailWord_2271028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271028).length < 2 ^ (prefixWord ++ tailWord_2271028).sum := by decide
  have hdescent : baseEnd_2271028 < baseStart_2271028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271068 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_2271068 : Nat := 118140960795 + 2271068 * 2 ^ 59
def prefixEnd_2271068 : Nat := 4983230072969 + 3 ^ 40 * 2271068 * 2
def baseEnd_2271068 : Nat := 1166149483045225669705555

theorem tailTrace_2271068 : CollatzResearch.WordTrace tailWord_2271068 prefixEnd_2271068 1166149483045225669705555 := by
  unfold tailWord_2271068
  simp only [CollatzResearch.WordTrace]
  refine ⟨41416327468157989189898929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55221769957543985586531905 41416327468157989189898929)
  ·
    refine ⟨31062245601118491892424197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41416327468157989189898929 31062245601118491892424197)
    ·
      refine ⟨5824171050209717229829537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31062245601118491892424197 5824171050209717229829537)
      ·
        refine ⟨4368128287657287922372153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5824171050209717229829537 4368128287657287922372153)
        ·
          refine ⟨3276096215742965941779115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4368128287657287922372153 3276096215742965941779115)
          ·
            refine ⟨4914144323614448912668673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276096215742965941779115 4914144323614448912668673)
            ·
              refine ⟨3685608242710836684501505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4914144323614448912668673 3685608242710836684501505)
              ·
                refine ⟨2764206182033127513376129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3685608242710836684501505 2764206182033127513376129)
                ·
                  refine ⟨2073154636524845635032097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2764206182033127513376129 2073154636524845635032097)
                  ·
                    refine ⟨1554865977393634226274073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2073154636524845635032097 1554865977393634226274073)
                    ·
                      refine ⟨1166149483045225669705555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554865977393634226274073 1166149483045225669705555)
                      ·
                        rfl

theorem cell23_2271068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_2271068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271068 prefixEnd_2271068 := by exact prefixLift 2271068
  have htrace : WordTrace (prefixWord ++ tailWord_2271068) baseStart_2271068 baseEnd_2271068 := by
    simpa [prefixWord, tailWord_2271068, baseEnd_2271068] using wordTrace_append hprefix tailTrace_2271068
  have hstable : (prefixWord ++ tailWord_2271068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271068).length < 2 ^ (prefixWord ++ tailWord_2271068).sum := by decide
  have hdescent : baseEnd_2271068 < baseStart_2271068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271074 : List Nat := [3, 3, 2, 1, 2, 2, 1, 4, 5]
def baseStart_2271074 : Nat := 118140960795 + 2271074 * 2 ^ 59
def prefixEnd_2271074 : Nat := 4983230072969 + 3 ^ 40 * 2271074 * 2
def baseEnd_2271074 : Nat := 129572507103239182914503

theorem tailTrace_2271074 : CollatzResearch.WordTrace tailWord_2271074 prefixEnd_2271074 129572507103239182914503 := by
  unfold tailWord_2271074
  simp only [CollatzResearch.WordTrace]
  refine ⟨20708218443573560351129069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55221915849529494269677517 20708218443573560351129069)
  ·
    refine ⟨7765581916340085131673401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20708218443573560351129069 7765581916340085131673401)
    ·
      refine ⟨5824186437255063848755051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7765581916340085131673401 5824186437255063848755051)
      ·
        refine ⟨8736279655882595773132577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5824186437255063848755051 8736279655882595773132577)
        ·
          refine ⟨6552209741911946829849433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8736279655882595773132577 6552209741911946829849433)
          ·
            refine ⟨4914157306433960122387075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6552209741911946829849433 4914157306433960122387075)
            ·
              refine ⟨7371235959650940183580613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914157306433960122387075 7371235959650940183580613)
              ·
                refine ⟨1382106742434551284421365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7371235959650940183580613 1382106742434551284421365)
                ·
                  refine ⟨129572507103239182914503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1382106742434551284421365 129572507103239182914503)
                  ·
                    rfl

theorem cell23_2271074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_2271074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271074 prefixEnd_2271074 := by exact prefixLift 2271074
  have htrace : WordTrace (prefixWord ++ tailWord_2271074) baseStart_2271074 baseEnd_2271074 := by
    simpa [prefixWord, tailWord_2271074, baseEnd_2271074] using wordTrace_append hprefix tailTrace_2271074
  have hstable : (prefixWord ++ tailWord_2271074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271074).length < 2 ^ (prefixWord ++ tailWord_2271074).sum := by decide
  have hdescent : baseEnd_2271074 < baseStart_2271074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271080 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2271080 : Nat := 118140960795 + 2271080 * 2 ^ 59
def prefixEnd_2271080 : Nat := 4983230072969 + 3 ^ 40 * 2271080 * 2
def baseEnd_2271080 : Nat := 1166155644813079622755499

theorem tailTrace_2271080 : CollatzResearch.WordTrace tailWord_2271080 prefixEnd_2271080 1166155644813079622755499 := by
  unfold tailWord_2271080
  simp only [CollatzResearch.WordTrace]
  refine ⟨41416546306136252214617347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55222061741515002952823129 41416546306136252214617347)
  ·
    refine ⟨62124819459204378321926021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41416546306136252214617347 62124819459204378321926021)
    ·
      refine ⟨11648403648600820935361129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62124819459204378321926021 11648403648600820935361129)
      ·
        refine ⟨8736302736450615701520847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11648403648600820935361129 8736302736450615701520847)
        ·
          refine ⟨13104454104675923552281271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8736302736450615701520847 13104454104675923552281271)
          ·
            refine ⟨19656681157013885328421907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13104454104675923552281271 19656681157013885328421907)
            ·
              refine ⟨29485021735520827992632861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19656681157013885328421907 29485021735520827992632861)
              ·
                refine ⟨11056883150820310497237323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29485021735520827992632861 11056883150820310497237323)
                ·
                  refine ⟨16585324726230465745855985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11056883150820310497237323 16585324726230465745855985)
                  ·
                    refine ⟨12438993544672849309391989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16585324726230465745855985 12438993544672849309391989)
                    ·
                      refine ⟨1166155644813079622755499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12438993544672849309391989 1166155644813079622755499)
                      ·
                        rfl

theorem cell23_2271080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2271080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271080 prefixEnd_2271080 := by exact prefixLift 2271080
  have htrace : WordTrace (prefixWord ++ tailWord_2271080) baseStart_2271080 baseEnd_2271080 := by
    simpa [prefixWord, tailWord_2271080, baseEnd_2271080] using wordTrace_append hprefix tailTrace_2271080
  have hstable : (prefixWord ++ tailWord_2271080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271080).length < 2 ^ (prefixWord ++ tailWord_2271080).sum := by decide
  have hdescent : baseEnd_2271080 < baseStart_2271080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271083 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 2, 8]
def baseStart_2271083 : Nat := 118140960795 + 2271083 * 2 ^ 59
def prefixEnd_2271083 : Nat := 4983230072969 + 3 ^ 40 * 2271083 * 2
def baseEnd_2271083 : Nat := 388719061751681037005995

theorem tailTrace_2271083 : CollatzResearch.WordTrace tailWord_2271083 prefixEnd_2271083 388719061751681037005995 := by
  unfold tailWord_2271083
  simp only [CollatzResearch.WordTrace]
  refine ⟨82833202031261635941593903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55222134687507757294395935 82833202031261635941593903)
  ·
    refine ⟨124249803046892453912390855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82833202031261635941593903 124249803046892453912390855)
    ·
      refine ⟨186374704570338680868586283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124249803046892453912390855 186374704570338680868586283)
      ·
        refine ⟨279562056855508021302879425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186374704570338680868586283 279562056855508021302879425)
        ·
          refine ⟨209671542641631015977159569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279562056855508021302879425 209671542641631015977159569)
          ·
            refine ⟨157253656981223261982869677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209671542641631015977159569 157253656981223261982869677)
            ·
              refine ⟨58970121367958723243576129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157253656981223261982869677 58970121367958723243576129)
              ·
                refine ⟨44227591025969042432682097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58970121367958723243576129 44227591025969042432682097)
                ·
                  refine ⟨33170693269476781824511573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44227591025969042432682097 33170693269476781824511573)
                  ·
                    refine ⟨388719061751681037005995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33170693269476781824511573 388719061751681037005995)
                    ·
                      rfl

theorem cell23_2271083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 8].length) (baseStart_2271083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271083 prefixEnd_2271083 := by exact prefixLift 2271083
  have htrace : WordTrace (prefixWord ++ tailWord_2271083) baseStart_2271083 baseEnd_2271083 := by
    simpa [prefixWord, tailWord_2271083, baseEnd_2271083] using wordTrace_append hprefix tailTrace_2271083
  have hstable : (prefixWord ++ tailWord_2271083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271083).length < 2 ^ (prefixWord ++ tailWord_2271083).sum := by decide
  have hdescent : baseEnd_2271083 < baseStart_2271083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271090 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2271090 : Nat := 118140960795 + 2271090 * 2 ^ 59
def prefixEnd_2271090 : Nat := 4983230072969 + 3 ^ 40 * 2271090 * 2
def baseEnd_2271090 : Nat := 1166160779619624583630453

theorem tailTrace_2271090 : CollatzResearch.WordTrace tailWord_2271090 prefixEnd_2271090 1166160779619624583630453 := by
  unfold tailWord_2271090
  simp only [CollatzResearch.WordTrace]
  refine ⟨20708364335559069034274681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55222304894824184091399149 20708364335559069034274681)
  ·
    refine ⟨15531273251669301775706011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20708364335559069034274681 15531273251669301775706011)
    ·
      refine ⟨23296909877503952663559017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15531273251669301775706011 23296909877503952663559017)
      ·
        refine ⟨17472682408127964497669263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23296909877503952663559017 17472682408127964497669263)
        ·
          refine ⟨26209023612191946746503895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17472682408127964497669263 26209023612191946746503895)
          ·
            refine ⟨39313535418287920119755843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26209023612191946746503895 39313535418287920119755843)
            ·
              refine ⟨58970303127431880179633765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39313535418287920119755843 58970303127431880179633765)
              ·
                refine ⟨11056931836393477533681331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58970303127431880179633765 11056931836393477533681331)
                ·
                  refine ⟨16585397754590216300521997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11056931836393477533681331 16585397754590216300521997)
                  ·
                    refine ⟨6219524157971331112695749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16585397754590216300521997 6219524157971331112695749)
                    ·
                      refine ⟨1166160779619624583630453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6219524157971331112695749 1166160779619624583630453)
                      ·
                        rfl

theorem cell23_2271090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2271090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271090 prefixEnd_2271090 := by exact prefixLift 2271090
  have htrace : WordTrace (prefixWord ++ tailWord_2271090) baseStart_2271090 baseEnd_2271090 := by
    simpa [prefixWord, tailWord_2271090, baseEnd_2271090] using wordTrace_append hprefix tailTrace_2271090
  have hstable : (prefixWord ++ tailWord_2271090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271090).length < 2 ^ (prefixWord ++ tailWord_2271090).sum := by decide
  have hdescent : baseEnd_2271090 < baseStart_2271090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271107 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 4]
def baseStart_2271107 : Nat := 118140960795 + 2271107 * 2 ^ 59
def prefixEnd_2271107 : Nat := 4983230072969 + 3 ^ 40 * 2271107 * 2
def baseEnd_2271107 : Nat := 1166169508790751017117875

theorem tailTrace_2271107 : CollatzResearch.WordTrace tailWord_2271107 prefixEnd_2271107 1166169508790751017117875 := by
  unfold tailWord_2271107
  simp only [CollatzResearch.WordTrace]
  refine ⟨82834077383174688040467575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55222718255449792026978383 82834077383174688040467575)
  ·
    refine ⟨124251116074762032060701363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82834077383174688040467575 124251116074762032060701363)
    ·
      refine ⟨186376674112143048091052045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124251116074762032060701363 186376674112143048091052045)
      ·
        refine ⟨69891252792053643034144517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186376674112143048091052045 69891252792053643034144517)
        ·
          refine ⟨13104609898510058068902097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69891252792053643034144517 13104609898510058068902097)
          ·
            refine ⟨9828457423882543551676573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13104609898510058068902097 9828457423882543551676573)
            ·
              refine ⟨3685671533955953831878715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9828457423882543551676573 3685671533955953831878715)
              ·
                refine ⟨5528507300933930747818073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3685671533955953831878715 5528507300933930747818073)
                ·
                  refine ⟨4146380475700448060863555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5528507300933930747818073 4146380475700448060863555)
                  ·
                    refine ⟨6219570713550672091295333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4146380475700448060863555 6219570713550672091295333)
                    ·
                      refine ⟨1166169508790751017117875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6219570713550672091295333 1166169508790751017117875)
                      ·
                        rfl

theorem cell23_2271107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_2271107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271107 prefixEnd_2271107 := by exact prefixLift 2271107
  have htrace : WordTrace (prefixWord ++ tailWord_2271107) baseStart_2271107 baseEnd_2271107 := by
    simpa [prefixWord, tailWord_2271107, baseEnd_2271107] using wordTrace_append hprefix tailTrace_2271107
  have hstable : (prefixWord ++ tailWord_2271107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271107).length < 2 ^ (prefixWord ++ tailWord_2271107).sum := by decide
  have hdescent : baseEnd_2271107 < baseStart_2271107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271124 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_2271124 : Nat := 118140960795 + 2271124 * 2 ^ 59
def prefixEnd_2271124 : Nat := 4983230072969 + 3 ^ 40 * 2271124 * 2
def baseEnd_2271124 : Nat := 1166178237961877450605297

theorem tailTrace_2271124 : CollatzResearch.WordTrace tailWord_2271124 prefixEnd_2271124 1166178237961877450605297 := by
  unfold tailWord_2271124
  simp only [CollatzResearch.WordTrace]
  refine ⟨41417348712056549971918213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55223131616075399962557617 41417348712056549971918213)
  ·
    refine ⟨7765752883510603119734665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41417348712056549971918213 7765752883510603119734665)
    ·
      refine ⟨5824314662632952339800999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7765752883510603119734665 5824314662632952339800999)
      ·
        refine ⟨8736471993949428509701499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5824314662632952339800999 8736471993949428509701499)
        ·
          refine ⟨13104707990924142764552249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8736471993949428509701499 13104707990924142764552249)
          ·
            refine ⟨9828530993193107073414187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13104707990924142764552249 9828530993193107073414187)
            ·
              refine ⟨14742796489789660610121281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9828530993193107073414187 14742796489789660610121281)
              ·
                refine ⟨11057097367342245457590961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14742796489789660610121281 11057097367342245457590961)
                ·
                  refine ⟨8292823025506684093193221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11057097367342245457590961 8292823025506684093193221)
                  ·
                    refine ⟨1554904317282503267473729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8292823025506684093193221 1554904317282503267473729)
                    ·
                      refine ⟨1166178237961877450605297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554904317282503267473729 1166178237961877450605297)
                      ·
                        rfl

theorem cell23_2271124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_2271124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271124 prefixEnd_2271124 := by exact prefixLift 2271124
  have htrace : WordTrace (prefixWord ++ tailWord_2271124) baseStart_2271124 baseEnd_2271124 := by
    simpa [prefixWord, tailWord_2271124, baseEnd_2271124] using wordTrace_append hprefix tailTrace_2271124
  have hstable : (prefixWord ++ tailWord_2271124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271124).length < 2 ^ (prefixWord ++ tailWord_2271124).sum := by decide
  have hdescent : baseEnd_2271124 < baseStart_2271124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271167 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 1, 5, 2]
def baseStart_2271167 : Nat := 118140960795 + 2271167 * 2 ^ 59
def prefixEnd_2271167 : Nat := 4983230072969 + 3 ^ 40 * 2271167 * 2
def baseEnd_2271167 : Nat := 1166200317630020782367599

theorem tailTrace_2271167 : CollatzResearch.WordTrace tailWord_2271167 prefixEnd_2271167 1166200317630020782367599 := by
  unfold tailWord_2271167
  simp only [CollatzResearch.WordTrace]
  refine ⟨82836265762957318287651755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55224177175304878858434503 82836265762957318287651755)
  ·
    refine ⟨124254398644435977431477633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82836265762957318287651755 124254398644435977431477633)
    ·
      refine ⟨93190798983326983073608225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124254398644435977431477633 93190798983326983073608225)
      ·
        refine ⟨69893099237495237305206169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93190798983326983073608225 69893099237495237305206169)
        ·
          refine ⟨52419824428121427978904627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69893099237495237305206169 52419824428121427978904627)
          ·
            refine ⟨78629736642182141968356941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52419824428121427978904627 78629736642182141968356941)
            ·
              refine ⟨29486151240818303238133853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78629736642182141968356941 29486151240818303238133853)
              ·
                refine ⟨11057306715306863714300195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29486151240818303238133853 11057306715306863714300195)
                ·
                  refine ⟨16585960072960295571450293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11057306715306863714300195 16585960072960295571450293)
                  ·
                    refine ⟨1554933756840027709823465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16585960072960295571450293 1554933756840027709823465)
                    ·
                      refine ⟨1166200317630020782367599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554933756840027709823465 1166200317630020782367599)
                      ·
                        rfl

theorem cell23_2271167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 5, 2].length) (baseStart_2271167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271167 prefixEnd_2271167 := by exact prefixLift 2271167
  have htrace : WordTrace (prefixWord ++ tailWord_2271167) baseStart_2271167 baseEnd_2271167 := by
    simpa [prefixWord, tailWord_2271167, baseEnd_2271167] using wordTrace_append hprefix tailTrace_2271167
  have hstable : (prefixWord ++ tailWord_2271167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271167).length < 2 ^ (prefixWord ++ tailWord_2271167).sum := by decide
  have hdescent : baseEnd_2271167 < baseStart_2271167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271214 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_2271214 : Nat := 118140960795 + 2271214 * 2 ^ 59
def prefixEnd_2271214 : Nat := 4983230072969 + 3 ^ 40 * 2271214 * 2
def baseEnd_2271214 : Nat := 1166224451220782098479883

theorem tailTrace_2271214 : CollatzResearch.WordTrace tailWord_2271214 prefixEnd_2271214 1166224451220782098479883 := by
  unfold tailWord_2271214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10354747499223380664326587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55225319995858030209741797 10354747499223380664326587)
  ·
    refine ⟨15532121248835070996489881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10354747499223380664326587 15532121248835070996489881)
    ·
      refine ⟨11649090936626303247367411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15532121248835070996489881 11649090936626303247367411)
      ·
        refine ⟨17473636404939454871051117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11649090936626303247367411 17473636404939454871051117)
        ·
          refine ⟨6552613651852295576644169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17473636404939454871051117 6552613651852295576644169)
          ·
            refine ⟨4914460238889221682483127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6552613651852295576644169 4914460238889221682483127)
            ·
              refine ⟨7371690358333832523724691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914460238889221682483127 7371690358333832523724691)
              ·
                refine ⟨11057535537500748785587037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7371690358333832523724691 11057535537500748785587037)
                ·
                  refine ⟨4146575826562780794595139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11057535537500748785587037 4146575826562780794595139)
                  ·
                    refine ⟨6219863739844171191892709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4146575826562780794595139 6219863739844171191892709)
                    ·
                      refine ⟨1166224451220782098479883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6219863739844171191892709 1166224451220782098479883)
                      ·
                        rfl

theorem cell23_2271214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_2271214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271214 prefixEnd_2271214 := by exact prefixLift 2271214
  have htrace : WordTrace (prefixWord ++ tailWord_2271214) baseStart_2271214 baseEnd_2271214 := by
    simpa [prefixWord, tailWord_2271214, baseEnd_2271214] using wordTrace_append hprefix tailTrace_2271214
  have hstable : (prefixWord ++ tailWord_2271214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271214).length < 2 ^ (prefixWord ++ tailWord_2271214).sum := by decide
  have hdescent : baseEnd_2271214 < baseStart_2271214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271242 : List Nat := [3, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3]
def baseStart_2271242 : Nat := 118140960795 + 2271242 * 2 ^ 59
def prefixEnd_2271242 : Nat := 4983230072969 + 3 ^ 40 * 2271242 * 2
def baseEnd_2271242 : Nat := 1166238828679107988929755

theorem tailTrace_2271242 : CollatzResearch.WordTrace tailWord_2271242 prefixEnd_2271242 1166238828679107988929755 := by
  unfold tailWord_2271242
  simp only [CollatzResearch.WordTrace]
  refine ⟨20709750309421401524157995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55226000825123737397754653 20709750309421401524157995)
  ·
    refine ⟨31064625464132102286236993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20709750309421401524157995 31064625464132102286236993)
    ·
      refine ⟨23298469098099076714677745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31064625464132102286236993 23298469098099076714677745)
      ·
        refine ⟨17473851823574307536008309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23298469098099076714677745 17473851823574307536008309)
        ·
          refine ⟨1638173608460091331500779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17473851823574307536008309 1638173608460091331500779)
          ·
            refine ⟨2457260412690136997251169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638173608460091331500779 2457260412690136997251169)
            ·
              refine ⟨1842945309517602747938377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2457260412690136997251169 1842945309517602747938377)
              ·
                refine ⟨1382208982138202060953783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1842945309517602747938377 1382208982138202060953783)
                ·
                  refine ⟨2073313473207303091430675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382208982138202060953783 2073313473207303091430675)
                  ·
                    refine ⟨3109970209810954637146013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2073313473207303091430675 3109970209810954637146013)
                    ·
                      refine ⟨1166238828679107988929755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3109970209810954637146013 1166238828679107988929755)
                      ·
                        rfl

theorem cell23_2271242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_2271242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271242 prefixEnd_2271242 := by exact prefixLift 2271242
  have htrace : WordTrace (prefixWord ++ tailWord_2271242) baseStart_2271242 baseEnd_2271242 := by
    simpa [prefixWord, tailWord_2271242, baseEnd_2271242] using wordTrace_append hprefix tailTrace_2271242
  have hstable : (prefixWord ++ tailWord_2271242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271242).length < 2 ^ (prefixWord ++ tailWord_2271242).sum := by decide
  have hdescent : baseEnd_2271242 < baseStart_2271242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271271 : List Nat := [1, 1, 7, 1, 2, 1, 3, 7]
def baseStart_2271271 : Nat := 118140960795 + 2271271 * 2 ^ 59
def prefixEnd_2271271 : Nat := 4983230072969 + 3 ^ 40 * 2271271 * 2
def baseEnd_2271271 : Nat := 43194582208077347239523

theorem tailTrace_2271271 : CollatzResearch.WordTrace tailWord_2271271 prefixEnd_2271271 43194582208077347239523 := by
  unfold tailWord_2271271
  simp only [CollatzResearch.WordTrace]
  refine ⟨82840058954580544049437667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55226705969720362699625111 82840058954580544049437667)
  ·
    refine ⟨124260088431870816074156501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82840058954580544049437667 124260088431870816074156501)
    ·
      refine ⟨2912345822621972251738043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 124260088431870816074156501 2912345822621972251738043)
      ·
        refine ⟨4368518733932958377607065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2912345822621972251738043 4368518733932958377607065)
        ·
          refine ⟨3276389050449718783205299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4368518733932958377607065 3276389050449718783205299)
          ·
            refine ⟨4914583575674578174807949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276389050449718783205299 4914583575674578174807949)
            ·
              refine ⟨1842968840877966815552981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4914583575674578174807949 1842968840877966815552981)
              ·
                refine ⟨43194582208077347239523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1842968840877966815552981 43194582208077347239523)
                ·
                  rfl

theorem cell23_2271271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 7].length) (baseStart_2271271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271271 prefixEnd_2271271 := by exact prefixLift 2271271
  have htrace : WordTrace (prefixWord ++ tailWord_2271271) baseStart_2271271 baseEnd_2271271 := by
    simpa [prefixWord, tailWord_2271271, baseEnd_2271271] using wordTrace_append hprefix tailTrace_2271271
  have hstable : (prefixWord ++ tailWord_2271271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271271).length < 2 ^ (prefixWord ++ tailWord_2271271).sum := by decide
  have hdescent : baseEnd_2271271 < baseStart_2271271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271325 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2271325 : Nat := 118140960795 + 2271325 * 2 ^ 59
def prefixEnd_2271325 : Nat := 4983230072969 + 3 ^ 40 * 2271325 * 2
def baseEnd_2271325 : Nat := 1166281447573431164191873

theorem tailTrace_2271325 : CollatzResearch.WordTrace tailWord_2271325 prefixEnd_2271325 1166281447573431164191873 := by
  unfold tailWord_2271325
  simp only [CollatzResearch.WordTrace]
  refine ⟨82842028496384911271903429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55228018997589940847935619 82842028496384911271903429)
  ·
    refine ⟨15532880343072170863481893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82842028496384911271903429 15532880343072170863481893)
    ·
      refine ⟨2912415064326032036902855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15532880343072170863481893 2912415064326032036902855)
      ·
        refine ⟨4368622596489048055354283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2912415064326032036902855 4368622596489048055354283)
        ·
          refine ⟨6552933894733572083031425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368622596489048055354283 6552933894733572083031425)
          ·
            refine ⟨4914700421050179062273569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6552933894733572083031425 4914700421050179062273569)
            ·
              refine ⟨3686025315787634296705177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4914700421050179062273569 3686025315787634296705177)
              ·
                refine ⟨2764518986840725722528883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3686025315787634296705177 2764518986840725722528883)
                ·
                  refine ⟨4146778480261088583793325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764518986840725722528883 4146778480261088583793325)
                  ·
                    refine ⟨1555041930097908218922497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4146778480261088583793325 1555041930097908218922497)
                    ·
                      refine ⟨1166281447573431164191873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555041930097908218922497 1166281447573431164191873)
                      ·
                        rfl

theorem cell23_2271325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2271325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271325 prefixEnd_2271325 := by exact prefixLift 2271325
  have htrace : WordTrace (prefixWord ++ tailWord_2271325) baseStart_2271325 baseEnd_2271325 := by
    simpa [prefixWord, tailWord_2271325, baseEnd_2271325] using wordTrace_append hprefix tailTrace_2271325
  have hstable : (prefixWord ++ tailWord_2271325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271325).length < 2 ^ (prefixWord ++ tailWord_2271325).sum := by decide
  have hdescent : baseEnd_2271325 < baseStart_2271325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271361 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 7]
def baseStart_2271361 : Nat := 118140960795 + 2271361 * 2 ^ 59
def prefixEnd_2271361 : Nat := 4983230072969 + 3 ^ 40 * 2271361 * 2
def baseEnd_2271361 : Nat := 129588881430777002593523

theorem tailTrace_2271361 : CollatzResearch.WordTrace tailWord_2271361 prefixEnd_2271361 129588881430777002593523 := by
  unfold tailWord_2271361
  simp only [CollatzResearch.WordTrace]
  refine ⟨82843341524254489420213937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55228894349502992946809291 82843341524254489420213937)
  ·
    refine ⟨62132506143190867065160453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82843341524254489420213937 62132506143190867065160453)
    ·
      refine ⟨11649844901848287574717585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62132506143190867065160453 11649844901848287574717585)
      ·
        refine ⟨8737383676386215681038189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11649844901848287574717585 8737383676386215681038189)
        ·
          refine ⟨3276518878644830880389321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8737383676386215681038189 3276518878644830880389321)
          ·
            refine ⟨2457389158983623160291991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3276518878644830880389321 2457389158983623160291991)
            ·
              refine ⟨3686083738475434740437987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2457389158983623160291991 3686083738475434740437987)
              ·
                refine ⟨5529125607713152110656981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3686083738475434740437987 5529125607713152110656981)
                ·
                  refine ⟨129588881430777002593523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5529125607713152110656981 129588881430777002593523)
                  ·
                    rfl

theorem cell23_2271361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 7].length) (baseStart_2271361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271361 prefixEnd_2271361 := by exact prefixLift 2271361
  have htrace : WordTrace (prefixWord ++ tailWord_2271361) baseStart_2271361 baseEnd_2271361 := by
    simpa [prefixWord, tailWord_2271361, baseEnd_2271361] using wordTrace_append hprefix tailTrace_2271361
  have hstable : (prefixWord ++ tailWord_2271361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271361).length < 2 ^ (prefixWord ++ tailWord_2271361).sum := by decide
  have hdescent : baseEnd_2271361 < baseStart_2271361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271367 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_2271367 : Nat := 118140960795 + 2271367 * 2 ^ 59
def prefixEnd_2271367 : Nat := 4983230072969 + 3 ^ 40 * 2271367 * 2
def baseEnd_2271367 : Nat := 1166303013760919999866679

theorem tailTrace_2271367 : CollatzResearch.WordTrace tailWord_2271367 prefixEnd_2271367 1166303013760919999866679 := by
  unfold tailWord_2271367
  simp only [CollatzResearch.WordTrace]
  refine ⟨82843560362232752444932355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55229040241488501629954903 82843560362232752444932355)
  ·
    refine ⟨124265340543349128667398533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82843560362232752444932355 124265340543349128667398533)
    ·
      refine ⟨23299751351877961625137225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124265340543349128667398533 23299751351877961625137225)
      ·
        refine ⟨17474813513908471218852919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23299751351877961625137225 17474813513908471218852919)
        ·
          refine ⟨26212220270862706828279379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17474813513908471218852919 26212220270862706828279379)
          ·
            refine ⟨39318330406294060242419069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26212220270862706828279379 39318330406294060242419069)
            ·
              refine ⟨14744373902360272590907151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39318330406294060242419069 14744373902360272590907151)
              ·
                refine ⟨22116560853540408886360727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14744373902360272590907151 22116560853540408886360727)
                ·
                  refine ⟨33174841280310613329541091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22116560853540408886360727 33174841280310613329541091)
                  ·
                    refine ⟨49762261920465919994311637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33174841280310613329541091 49762261920465919994311637)
                    ·
                      refine ⟨1166303013760919999866679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49762261920465919994311637 1166303013760919999866679)
                      ·
                        rfl

theorem cell23_2271367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_2271367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271367 prefixEnd_2271367 := by exact prefixLift 2271367
  have htrace : WordTrace (prefixWord ++ tailWord_2271367) baseStart_2271367 baseEnd_2271367 := by
    simpa [prefixWord, tailWord_2271367, baseEnd_2271367] using wordTrace_append hprefix tailTrace_2271367
  have hstable : (prefixWord ++ tailWord_2271367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271367).length < 2 ^ (prefixWord ++ tailWord_2271367).sum := by decide
  have hdescent : baseEnd_2271367 < baseStart_2271367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271391 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 2, 5]
def baseStart_2271391 : Nat := 118140960795 + 2271391 * 2 ^ 59
def prefixEnd_2271391 : Nat := 4983230072969 + 3 ^ 40 * 2271391 * 2
def baseEnd_2271391 : Nat := 388771779098875968655523

theorem tailTrace_2271391 : CollatzResearch.WordTrace tailWord_2271391 prefixEnd_2271391 388771779098875968655523 := by
  unfold tailWord_2271391
  simp only [CollatzResearch.WordTrace]
  refine ⟨82844435714145804543806027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55229623809430536362537351 82844435714145804543806027)
  ·
    refine ⟨124266653571218706815709041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82844435714145804543806027 124266653571218706815709041)
    ·
      refine ⟨93199990178414030111781781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124266653571218706815709041 93199990178414030111781781)
      ·
        refine ⟨4368749539613157661489771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93199990178414030111781781 4368749539613157661489771)
        ·
          refine ⟨6553124309419736492234657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368749539613157661489771 6553124309419736492234657)
          ·
            refine ⟨4914843232064802369175993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6553124309419736492234657 4914843232064802369175993)
            ·
              refine ⟨3686132424048601776881995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4914843232064802369175993 3686132424048601776881995)
              ·
                refine ⟨5529198636072902665322993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3686132424048601776881995 5529198636072902665322993)
                ·
                  refine ⟨4146898977054676998992245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5529198636072902665322993 4146898977054676998992245)
                  ·
                    refine ⟨388771779098875968655523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4146898977054676998992245 388771779098875968655523)
                    ·
                      rfl

theorem cell23_2271391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 5].length) (baseStart_2271391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271391 prefixEnd_2271391 := by exact prefixLift 2271391
  have htrace : WordTrace (prefixWord ++ tailWord_2271391) baseStart_2271391 baseEnd_2271391 := by
    simpa [prefixWord, tailWord_2271391, baseEnd_2271391] using wordTrace_append hprefix tailTrace_2271391
  have hstable : (prefixWord ++ tailWord_2271391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271391).length < 2 ^ (prefixWord ++ tailWord_2271391).sum := by decide
  have hdescent : baseEnd_2271391 < baseStart_2271391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271407 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_2271407 : Nat := 118140960795 + 2271407 * 2 ^ 59
def prefixEnd_2271407 : Nat := 4983230072969 + 3 ^ 40 * 2271407 * 2
def baseEnd_2271407 : Nat := 1166323552987099843366495

theorem tailTrace_2271407 : CollatzResearch.WordTrace tailWord_2271407 prefixEnd_2271407 1166323552987099843366495 := by
  unfold tailWord_2271407
  simp only [CollatzResearch.WordTrace]
  refine ⟨82845019282087839276388475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55230012854725226184258983 82845019282087839276388475)
  ·
    refine ⟨124267528923131758914582713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82845019282087839276388475 124267528923131758914582713)
    ·
      refine ⟨93200646692348819185937035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124267528923131758914582713 93200646692348819185937035)
      ·
        refine ⟨139800970038523228778905553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93200646692348819185937035 139800970038523228778905553)
        ·
          refine ⟨104850727528892421584179165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139800970038523228778905553 104850727528892421584179165)
          ·
            refine ⟨39319022823334658094067187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104850727528892421584179165 39319022823334658094067187)
            ·
              refine ⟨58978534235001987141100781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39319022823334658094067187 58978534235001987141100781)
              ·
                refine ⟨22116950338125745177912793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58978534235001987141100781 22116950338125745177912793)
                ·
                  refine ⟨16587712753594308883434595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22116950338125745177912793 16587712753594308883434595)
                  ·
                    refine ⟨24881569130391463325151893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16587712753594308883434595 24881569130391463325151893)
                    ·
                      refine ⟨1166323552987099843366495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24881569130391463325151893 1166323552987099843366495)
                      ·
                        rfl

theorem cell23_2271407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_2271407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271407 prefixEnd_2271407 := by exact prefixLift 2271407
  have htrace : WordTrace (prefixWord ++ tailWord_2271407) baseStart_2271407 baseEnd_2271407 := by
    simpa [prefixWord, tailWord_2271407, baseEnd_2271407] using wordTrace_append hprefix tailTrace_2271407
  have hstable : (prefixWord ++ tailWord_2271407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271407).length < 2 ^ (prefixWord ++ tailWord_2271407).sum := by decide
  have hdescent : baseEnd_2271407 < baseStart_2271407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271412 : List Nat := [2, 5, 3, 1, 1, 1, 1, 4, 5]
def baseStart_2271412 : Nat := 118140960795 + 2271412 * 2 ^ 59
def prefixEnd_2271412 : Nat := 4983230072969 + 3 ^ 40 * 2271412 * 2
def baseEnd_2271412 : Nat := 129591791154485813755997

theorem tailTrace_2271412 : CollatzResearch.WordTrace tailWord_2271412 prefixEnd_2271412 129591791154485813755997 := by
  unfold tailWord_2271412
  simp only [CollatzResearch.WordTrace]
  refine ⟨41422600823534862565160245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55230134431379816753546993 41422600823534862565160245)
  ·
    refine ⟨3883368827206393365483773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41422600823534862565160245 3883368827206393365483773)
    ·
      refine ⟨1456263310202397512056415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3883368827206393365483773 1456263310202397512056415)
      ·
        refine ⟨2184394965303596268084623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456263310202397512056415 2184394965303596268084623)
        ·
          refine ⟨3276592447955394402126935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184394965303596268084623 3276592447955394402126935)
          ·
            refine ⟨4914888671933091603190403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276592447955394402126935 4914888671933091603190403)
            ·
              refine ⟨7372333007899637404785605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914888671933091603190403 7372333007899637404785605)
              ·
                refine ⟨1382312438981182013397301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7372333007899637404785605 1382312438981182013397301)
                ·
                  refine ⟨129591791154485813755997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1382312438981182013397301 129591791154485813755997)
                  ·
                    rfl

theorem cell23_2271412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_2271412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271412 prefixEnd_2271412 := by exact prefixLift 2271412
  have htrace : WordTrace (prefixWord ++ tailWord_2271412) baseStart_2271412 baseEnd_2271412 := by
    simpa [prefixWord, tailWord_2271412, baseEnd_2271412] using wordTrace_append hprefix tailTrace_2271412
  have hstable : (prefixWord ++ tailWord_2271412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271412).length < 2 ^ (prefixWord ++ tailWord_2271412).sum := by decide
  have hdescent : baseEnd_2271412 < baseStart_2271412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271428 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_2271428 : Nat := 118140960795 + 2271428 * 2 ^ 59
def prefixEnd_2271428 : Nat := 4983230072969 + 3 ^ 40 * 2271428 * 2
def baseEnd_2271428 : Nat := 1166334336080844261203899

theorem tailTrace_2271428 : CollatzResearch.WordTrace tailWord_2271428 prefixEnd_2271428 1166334336080844261203899 := by
  unfold tailWord_2271428
  simp only [CollatzResearch.WordTrace]
  refine ⟨41422892607505879931451469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55230523476674506575268625 41422892607505879931451469)
  ·
    refine ⟨15533584727814704974294301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41422892607505879931451469 15533584727814704974294301)
    ·
      refine ⟨5825094272930514365360363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15533584727814704974294301 5825094272930514365360363)
      ·
        refine ⟨8737641409395771548040545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5825094272930514365360363 8737641409395771548040545)
        ·
          refine ⟨6553231057046828661030409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8737641409395771548040545 6553231057046828661030409)
          ·
            refine ⟨4914923292785121495772807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6553231057046828661030409 4914923292785121495772807)
            ·
              refine ⟨7372384939177682243659211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914923292785121495772807 7372384939177682243659211)
              ·
                refine ⟨11058577408766523365488817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7372384939177682243659211 11058577408766523365488817)
                ·
                  refine ⟨8293933056574892524116613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11058577408766523365488817 8293933056574892524116613)
                  ·
                    refine ⟨1555112448107792348271865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8293933056574892524116613 1555112448107792348271865)
                    ·
                      refine ⟨1166334336080844261203899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555112448107792348271865 1166334336080844261203899)
                      ·
                        rfl

theorem cell23_2271428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_2271428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271428 prefixEnd_2271428 := by exact prefixLift 2271428
  have htrace : WordTrace (prefixWord ++ tailWord_2271428) baseStart_2271428 baseEnd_2271428 := by
    simpa [prefixWord, tailWord_2271428, baseEnd_2271428] using wordTrace_append hprefix tailTrace_2271428
  have hstable : (prefixWord ++ tailWord_2271428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271428).length < 2 ^ (prefixWord ++ tailWord_2271428).sum := by decide
  have hdescent : baseEnd_2271428 < baseStart_2271428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271434 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 6]
def baseStart_2271434 : Nat := 118140960795 + 2271434 * 2 ^ 59
def prefixEnd_2271434 : Nat := 4983230072969 + 3 ^ 40 * 2271434 * 2
def baseEnd_2271434 : Nat := 129593046329419026414319

theorem tailTrace_2271434 : CollatzResearch.WordTrace tailWord_2271434 prefixEnd_2271434 129593046329419026414319 := by
  unfold tailWord_2271434
  simp only [CollatzResearch.WordTrace]
  refine ⟨20711501013247505721905339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55230669368660015258414237 20711501013247505721905339)
  ·
    refine ⟨31067251519871258582858009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20711501013247505721905339 31067251519871258582858009)
    ·
      refine ⟨23300438639903443937143507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31067251519871258582858009 23300438639903443937143507)
      ·
        refine ⟨34950657959855165905715261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23300438639903443937143507 34950657959855165905715261)
        ·
          refine ⟨13106496734945687214643223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34950657959855165905715261 13106496734945687214643223)
          ·
            refine ⟨19659745102418530821964835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13106496734945687214643223 19659745102418530821964835)
            ·
              refine ⟨29489617653627796232947253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19659745102418530821964835 29489617653627796232947253)
              ·
                refine ⟨2764651655027605896838805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29489617653627796232947253 2764651655027605896838805)
                ·
                  refine ⟨129593046329419026414319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2764651655027605896838805 129593046329419026414319)
                  ·
                    rfl

theorem cell23_2271434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_2271434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271434 prefixEnd_2271434 := by exact prefixLift 2271434
  have htrace : WordTrace (prefixWord ++ tailWord_2271434) baseStart_2271434 baseEnd_2271434 := by
    simpa [prefixWord, tailWord_2271434, baseEnd_2271434] using wordTrace_append hprefix tailTrace_2271434
  have hstable : (prefixWord ++ tailWord_2271434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271434).length < 2 ^ (prefixWord ++ tailWord_2271434).sum := by decide
  have hdescent : baseEnd_2271434 < baseStart_2271434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271445 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 2, 1, 4]
def baseStart_2271445 : Nat := 118140960795 + 2271445 * 2 ^ 59
def prefixEnd_2271445 : Nat := 4983230072969 + 3 ^ 40 * 2271445 * 2
def baseEnd_2271445 : Nat := 1166343065251970694691321

theorem tailTrace_2271445 : CollatzResearch.WordTrace tailWord_2271445 prefixEnd_2271445 1166343065251970694691321 := by
  unfold tailWord_2271445
  simp only [CollatzResearch.WordTrace]
  refine ⟨82846405255950171766271789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55230936837300114510847859 82846405255950171766271789)
  ·
    refine ⟨31067401970981314412351921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82846405255950171766271789 31067401970981314412351921)
    ·
      refine ⟨23300551478235985809263941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31067401970981314412351921 23300551478235985809263941)
      ·
        refine ⟨4368853402169247339236989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23300551478235985809263941 4368853402169247339236989)
        ·
          refine ⟨1638320025813467752213871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4368853402169247339236989 1638320025813467752213871)
          ·
            refine ⟨2457480038720201628320807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638320025813467752213871 2457480038720201628320807)
            ·
              refine ⟨3686220058080302442481211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2457480038720201628320807 3686220058080302442481211)
              ·
                refine ⟨5529330087120453663721817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3686220058080302442481211 5529330087120453663721817)
                ·
                  refine ⟨4146997565340340247791363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5529330087120453663721817 4146997565340340247791363)
                  ·
                    refine ⟨6220496348010510371687045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4146997565340340247791363 6220496348010510371687045)
                    ·
                      refine ⟨1166343065251970694691321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6220496348010510371687045 1166343065251970694691321)
                      ·
                        rfl

theorem cell23_2271445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_2271445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271445 prefixEnd_2271445 := by exact prefixLift 2271445
  have htrace : WordTrace (prefixWord ++ tailWord_2271445) baseStart_2271445 baseEnd_2271445 := by
    simpa [prefixWord, tailWord_2271445, baseEnd_2271445] using wordTrace_append hprefix tailTrace_2271445
  have hstable : (prefixWord ++ tailWord_2271445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271445).length < 2 ^ (prefixWord ++ tailWord_2271445).sum := by decide
  have hdescent : baseEnd_2271445 < baseStart_2271445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271448 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 2, 2, 3]
def baseStart_2271448 : Nat := 118140960795 + 2271448 * 2 ^ 59
def prefixEnd_2271448 : Nat := 4983230072969 + 3 ^ 40 * 2271448 * 2
def baseEnd_2271448 : Nat := 1166344605693934182953807

theorem tailTrace_2271448 : CollatzResearch.WordTrace tailWord_2271448 prefixEnd_2271448 1166344605693934182953807 := by
  unfold tailWord_2271448
  simp only [CollatzResearch.WordTrace]
  refine ⟨41423257337469651639315499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55231009783292868852420665 41423257337469651639315499)
  ·
    refine ⟨62134886006204477458973249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41423257337469651639315499 62134886006204477458973249)
    ·
      refine ⟨46601164504653358094229937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62134886006204477458973249 46601164504653358094229937)
      ·
        refine ⟨34950873378490018570672453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46601164504653358094229937 34950873378490018570672453)
        ·
          refine ⟨6553288758466878482001085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34950873378490018570672453 6553288758466878482001085)
          ·
            refine ⟨2457483284425079430750407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6553288758466878482001085 2457483284425079430750407)
            ·
              refine ⟨3686224926637619146125611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2457483284425079430750407 3686224926637619146125611)
              ·
                refine ⟨5529337389956428719188417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3686224926637619146125611 5529337389956428719188417)
                ·
                  refine ⟨4147003042467321539391313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5529337389956428719188417 4147003042467321539391313)
                  ·
                    refine ⟨3110252281850491154543485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4147003042467321539391313 3110252281850491154543485)
                    ·
                      refine ⟨1166344605693934182953807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3110252281850491154543485 1166344605693934182953807)
                      ·
                        rfl

theorem cell23_2271448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_2271448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271448 prefixEnd_2271448 := by exact prefixLift 2271448
  have htrace : WordTrace (prefixWord ++ tailWord_2271448) baseStart_2271448 baseEnd_2271448 := by
    simpa [prefixWord, tailWord_2271448, baseEnd_2271448] using wordTrace_append hprefix tailTrace_2271448
  have hstable : (prefixWord ++ tailWord_2271448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271448).length < 2 ^ (prefixWord ++ tailWord_2271448).sum := by decide
  have hdescent : baseEnd_2271448 < baseStart_2271448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271478 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_2271478 : Nat := 118140960795 + 2271478 * 2 ^ 59
def prefixEnd_2271478 : Nat := 4983230072969 + 3 ^ 40 * 2271478 * 2
def baseEnd_2271478 : Nat := 1166360010113569065578669

theorem tailTrace_2271478 : CollatzResearch.WordTrace tailWord_2271478 prefixEnd_2271478 1166360010113569065578669 := by
  unfold tailWord_2271478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5177975554051913650138943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55231739243220412268148725 5177975554051913650138943)
  ·
    refine ⟨7766963331077870475208415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5177975554051913650138943 7766963331077870475208415)
    ·
      refine ⟨11650444996616805712812623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7766963331077870475208415 11650444996616805712812623)
      ·
        refine ⟨17475667494925208569218935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11650444996616805712812623 17475667494925208569218935)
        ·
          refine ⟨26213501242387812853828403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17475667494925208569218935 26213501242387812853828403)
          ·
            refine ⟨39320251863581719280742605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26213501242387812853828403 39320251863581719280742605)
            ·
              refine ⟨14745094448843144730278477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39320251863581719280742605 14745094448843144730278477)
              ·
                refine ⟨5529410418316179273854429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14745094448843144730278477 5529410418316179273854429)
                ·
                  refine ⟨2073528906868567227695411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5529410418316179273854429 2073528906868567227695411)
                  ·
                    refine ⟨3110293360302850841543117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2073528906868567227695411 3110293360302850841543117)
                    ·
                      refine ⟨1166360010113569065578669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3110293360302850841543117 1166360010113569065578669)
                      ·
                        rfl

theorem cell23_2271478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_2271478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271478 prefixEnd_2271478 := by exact prefixLift 2271478
  have htrace : WordTrace (prefixWord ++ tailWord_2271478) baseStart_2271478 baseEnd_2271478 := by
    simpa [prefixWord, tailWord_2271478, baseEnd_2271478] using wordTrace_append hprefix tailTrace_2271478
  have hstable : (prefixWord ++ tailWord_2271478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271478).length < 2 ^ (prefixWord ++ tailWord_2271478).sum := by decide
  have hdescent : baseEnd_2271478 < baseStart_2271478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271511 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 4, 4]
def baseStart_2271511 : Nat := 118140960795 + 2271511 * 2 ^ 59
def prefixEnd_2271511 : Nat := 4983230072969 + 3 ^ 40 * 2271511 * 2
def baseEnd_2271511 : Nat := 388792318325055812155339

theorem tailTrace_2271511 : CollatzResearch.WordTrace tailWord_2271511 prefixEnd_2271511 388792318325055812155339 := by
  unfold tailWord_2271511
  simp only [CollatzResearch.WordTrace]
  refine ⟨82848812473711065038174387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55232541649140710025449591 82848812473711065038174387)
  ·
    refine ⟨124273218710566597557261581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82848812473711065038174387 124273218710566597557261581)
    ·
      refine ⟨46602457016462474083973093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124273218710566597557261581 46602457016462474083973093)
      ·
        refine ⟨8737960690586713890744955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46602457016462474083973093 8737960690586713890744955)
        ·
          refine ⟨13106941035880070836117433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8737960690586713890744955 13106941035880070836117433)
          ·
            refine ⟨9830205776910053127088075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13106941035880070836117433 9830205776910053127088075)
            ·
              refine ⟨14745308665365079690632113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9830205776910053127088075 14745308665365079690632113)
              ·
                refine ⟨11058981499023809767974085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14745308665365079690632113 11058981499023809767974085)
                ·
                  refine ⟨2073559031066964331495141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11058981499023809767974085 2073559031066964331495141)
                  ·
                    refine ⟨388792318325055812155339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2073559031066964331495141 388792318325055812155339)
                    ·
                      rfl

theorem cell23_2271511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_2271511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271511 prefixEnd_2271511 := by exact prefixLift 2271511
  have htrace : WordTrace (prefixWord ++ tailWord_2271511) baseStart_2271511 baseEnd_2271511 := by
    simpa [prefixWord, tailWord_2271511, baseEnd_2271511] using wordTrace_append hprefix tailTrace_2271511
  have hstable : (prefixWord ++ tailWord_2271511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271511).length < 2 ^ (prefixWord ++ tailWord_2271511).sum := by decide
  have hdescent : baseEnd_2271511 < baseStart_2271511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271524 : List Nat := [2, 3, 1, 3, 1, 2, 11]
def baseStart_2271524 : Nat := 118140960795 + 2271524 * 2 ^ 59
def prefixEnd_2271524 : Nat := 4983230072969 + 3 ^ 40 * 2271524 * 2
def baseEnd_2271524 : Nat := 14399797903995998587697

theorem tailTrace_2271524 : CollatzResearch.WordTrace tailWord_2271524 prefixEnd_2271524 14399797903995998587697 := by
  unfold tailWord_2271524
  simp only [CollatzResearch.WordTrace]
  refine ⟨41424643311331984129198813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55232857748442645505598417 41424643311331984129198813)
  ·
    refine ⟨15534241241749494048449555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41424643311331984129198813 15534241241749494048449555)
    ·
      refine ⟨23301361862624241072674333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15534241241749494048449555 23301361862624241072674333)
      ·
        refine ⟨8738010698484090402252875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23301361862624241072674333 8738010698484090402252875)
        ·
          refine ⟨13107016047726135603379313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8738010698484090402252875 13107016047726135603379313)
          ·
            refine ⟨9830262035794601702534485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13107016047726135603379313 9830262035794601702534485)
            ·
              refine ⟨14399797903995998587697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9830262035794601702534485 14399797903995998587697)
              ·
                rfl

theorem cell23_2271524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 11].length) (baseStart_2271524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271524 prefixEnd_2271524 := by exact prefixLift 2271524
  have htrace : WordTrace (prefixWord ++ tailWord_2271524) baseStart_2271524 baseEnd_2271524 := by
    simpa [prefixWord, tailWord_2271524, baseEnd_2271524] using wordTrace_append hprefix tailTrace_2271524
  have hstable : (prefixWord ++ tailWord_2271524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271524).length < 2 ^ (prefixWord ++ tailWord_2271524).sum := by decide
  have hdescent : baseEnd_2271524 < baseStart_2271524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271535 : List Nat := [1, 1, 2, 1, 2, 1, 4, 6, 1, 2, 2]
def baseStart_2271535 : Nat := 118140960795 + 2271535 * 2 ^ 59
def prefixEnd_2271535 : Nat := 4983230072969 + 3 ^ 40 * 2271535 * 2
def baseEnd_2271535 : Nat := 1166389278510875342565907

theorem tailTrace_2271535 : CollatzResearch.WordTrace tailWord_2271535 prefixEnd_2271535 1166389278510875342565907 := by
  unfold tailWord_2271535
  simp only [CollatzResearch.WordTrace]
  refine ⟨82849687825624117137048059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55233125217082744758032039 82849687825624117137048059)
  ·
    refine ⟨124274531738436175705572089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82849687825624117137048059 124274531738436175705572089)
    ·
      refine ⟨93205898803827131779179067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124274531738436175705572089 93205898803827131779179067)
      ·
        refine ⟨139808848205740697668768601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93205898803827131779179067 139808848205740697668768601)
        ·
          refine ⟨104856636154305523251576451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139808848205740697668768601 104856636154305523251576451)
          ·
            refine ⟨157284954231458284877364677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104856636154305523251576451 157284954231458284877364677)
            ·
              refine ⟨29490928918398428414505877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157284954231458284877364677 29490928918398428414505877)
              ·
                refine ⟨1382387293049926331929963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29490928918398428414505877 1382387293049926331929963)
                ·
                  refine ⟨2073580939574889497894945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382387293049926331929963 2073580939574889497894945)
                  ·
                    refine ⟨1555185704681167123421209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2073580939574889497894945 1555185704681167123421209)
                    ·
                      refine ⟨1166389278510875342565907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555185704681167123421209 1166389278510875342565907)
                      ·
                        rfl

theorem cell23_2271535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 1, 2, 2].length) (baseStart_2271535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271535 prefixEnd_2271535 := by exact prefixLift 2271535
  have htrace : WordTrace (prefixWord ++ tailWord_2271535) baseStart_2271535 baseEnd_2271535 := by
    simpa [prefixWord, tailWord_2271535, baseEnd_2271535] using wordTrace_append hprefix tailTrace_2271535
  have hstable : (prefixWord ++ tailWord_2271535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271535).length < 2 ^ (prefixWord ++ tailWord_2271535).sum := by decide
  have hdescent : baseEnd_2271535 < baseStart_2271535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271545 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 2, 4]
def baseStart_2271545 : Nat := 118140960795 + 2271545 * 2 ^ 59
def prefixEnd_2271545 : Nat := 4983230072969 + 3 ^ 40 * 2271545 * 2
def baseEnd_2271545 : Nat := 388798137772473434480287

theorem tailTrace_2271545 : CollatzResearch.WordTrace tailWord_2271545 prefixEnd_2271545 388798137772473434480287 := by
  unfold tailWord_2271545
  simp only [CollatzResearch.WordTrace]
  refine ⟨82850052555587888844912089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55233368370391925896608059 82850052555587888844912089)
  ·
    refine ⟨62137539416690916633684067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82850052555587888844912089 62137539416690916633684067)
    ·
      refine ⟨93206309125036374950526101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62137539416690916633684067 93206309125036374950526101)
      ·
        refine ⟨4369045740236080075805911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93206309125036374950526101 4369045740236080075805911)
        ·
          refine ⟨6553568610354120113708867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4369045740236080075805911 6553568610354120113708867)
          ·
            refine ⟨9830352915531180170563301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6553568610354120113708867 9830352915531180170563301)
            ·
              refine ⟨1843191171662096281980619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9830352915531180170563301 1843191171662096281980619)
              ·
                refine ⟨2764786757493144422970929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843191171662096281980619 2764786757493144422970929)
                ·
                  refine ⟨2073590068119858317228197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2764786757493144422970929 2073590068119858317228197)
                  ·
                    refine ⟨388798137772473434480287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2073590068119858317228197 388798137772473434480287)
                    ·
                      rfl

theorem cell23_2271545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 2, 4].length) (baseStart_2271545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271545 prefixEnd_2271545 := by exact prefixLift 2271545
  have htrace : WordTrace (prefixWord ++ tailWord_2271545) baseStart_2271545 baseEnd_2271545 := by
    simpa [prefixWord, tailWord_2271545, baseEnd_2271545] using wordTrace_append hprefix tailTrace_2271545
  have hstable : (prefixWord ++ tailWord_2271545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271545).length < 2 ^ (prefixWord ++ tailWord_2271545).sum := by decide
  have hdescent : baseEnd_2271545 < baseStart_2271545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271551 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 3]
def baseStart_2271551 : Nat := 118140960795 + 2271551 * 2 ^ 59
def prefixEnd_2271551 : Nat := 4983230072969 + 3 ^ 40 * 2271551 * 2
def baseEnd_2271551 : Nat := 1166397494201347279965833

theorem tailTrace_2271551 : CollatzResearch.WordTrace tailWord_2271551 prefixEnd_2271551 1166397494201347279965833 := by
  unfold tailWord_2271551
  simp only [CollatzResearch.WordTrace]
  refine ⟨82850271393566151869630507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55233514262377434579753671 82850271393566151869630507)
  ·
    refine ⟨124275407090349227804445761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82850271393566151869630507 124275407090349227804445761)
    ·
      refine ⟨93206555317761920853334321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124275407090349227804445761 93206555317761920853334321)
      ·
        refine ⟨69904916488321440640000741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93206555317761920853334321 69904916488321440640000741)
        ·
          refine ⟨13107171841560270120000139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69904916488321440640000741 13107171841560270120000139)
          ·
            refine ⟨19660757762340405180000209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13107171841560270120000139 19660757762340405180000209)
            ·
              refine ⟨14745568321755303885000157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19660757762340405180000209 14745568321755303885000157)
              ·
                refine ⟨5529588120658238956875059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14745568321755303885000157 5529588120658238956875059)
                ·
                  refine ⟨8294382180987358435312589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5529588120658238956875059 8294382180987358435312589)
                  ·
                    refine ⟨3110393317870259413242221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8294382180987358435312589 3110393317870259413242221)
                    ·
                      refine ⟨1166397494201347279965833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3110393317870259413242221 1166397494201347279965833)
                      ·
                        rfl

theorem cell23_2271551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_2271551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271551 prefixEnd_2271551 := by exact prefixLift 2271551
  have htrace : WordTrace (prefixWord ++ tailWord_2271551) baseStart_2271551 baseEnd_2271551 := by
    simpa [prefixWord, tailWord_2271551, baseEnd_2271551] using wordTrace_append hprefix tailTrace_2271551
  have hstable : (prefixWord ++ tailWord_2271551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271551).length < 2 ^ (prefixWord ++ tailWord_2271551).sum := by decide
  have hdescent : baseEnd_2271551 < baseStart_2271551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271586 : List Nat := [3, 3, 2, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_2271586 : Nat := 118140960795 + 2271586 * 2 ^ 59
def prefixEnd_2271586 : Nat := 4983230072969 + 3 ^ 40 * 2271586 * 2
def baseEnd_2271586 : Nat := 1166415466024254643028173

theorem tailTrace_2271586 : CollatzResearch.WordTrace tailWord_2271586 prefixEnd_2271586 1166415466024254643028173 := by
  unfold tailWord_2271586
  simp only [CollatzResearch.WordTrace]
  refine ⟨20712886987109838211788653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55234365298959568564769741 20712886987109838211788653)
  ·
    refine ⟨7767332620166189329420745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20712886987109838211788653 7767332620166189329420745)
    ·
      refine ⟨5825499465124641997065559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7767332620166189329420745 5825499465124641997065559)
      ·
        refine ⟨8738249197686962995598339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5825499465124641997065559 8738249197686962995598339)
        ·
          refine ⟨13107373796530444493397509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8738249197686962995598339 13107373796530444493397509)
          ·
            refine ⟨2457632586849458342512033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13107373796530444493397509 2457632586849458342512033)
            ·
              refine ⟨1843224440137093756884025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2457632586849458342512033 1843224440137093756884025)
              ·
                refine ⟨1382418330102820317663019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1843224440137093756884025 1382418330102820317663019)
                ·
                  refine ⟨2073627495154230476494529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382418330102820317663019 2073627495154230476494529)
                  ·
                    refine ⟨1555220621365672857370897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2073627495154230476494529 1555220621365672857370897)
                    ·
                      refine ⟨1166415466024254643028173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555220621365672857370897 1166415466024254643028173)
                      ·
                        rfl

theorem cell23_2271586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_2271586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271586 prefixEnd_2271586 := by exact prefixLift 2271586
  have htrace : WordTrace (prefixWord ++ tailWord_2271586) baseStart_2271586 baseEnd_2271586 := by
    simpa [prefixWord, tailWord_2271586, baseEnd_2271586] using wordTrace_append hprefix tailTrace_2271586
  have hstable : (prefixWord ++ tailWord_2271586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271586).length < 2 ^ (prefixWord ++ tailWord_2271586).sum := by decide
  have hdescent : baseEnd_2271586 < baseStart_2271586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271591 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2271591 : Nat := 118140960795 + 2271591 * 2 ^ 59
def prefixEnd_2271591 : Nat := 4983230072969 + 3 ^ 40 * 2271591 * 2
def baseEnd_2271591 : Nat := 1166418033427527123465649

theorem tailTrace_2271591 : CollatzResearch.WordTrace tailWord_2271591 prefixEnd_2271591 1166418033427527123465649 := by
  unfold tailWord_2271591
  simp only [CollatzResearch.WordTrace]
  refine ⟨82851730313421238701086627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55234486875614159134057751 82851730313421238701086627)
  ·
    refine ⟨124277595470131858051629941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82851730313421238701086627 124277595470131858051629941)
    ·
      refine ⟨11651024575324861692340307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124277595470131858051629941 11651024575324861692340307)
      ·
        refine ⟨17476536862987292538510461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11651024575324861692340307 17476536862987292538510461)
        ·
          refine ⟨6553701323620234701941423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17476536862987292538510461 6553701323620234701941423)
          ·
            refine ⟨9830551985430352052912135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6553701323620234701941423 9830551985430352052912135)
            ·
              refine ⟨14745827978145528079368203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9830551985430352052912135 14745827978145528079368203)
              ·
                refine ⟨22118741967218292119052305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14745827978145528079368203 22118741967218292119052305)
                ·
                  refine ⟨16589056475413719089289229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22118741967218292119052305 16589056475413719089289229)
                  ·
                    refine ⟨6220896178280144658483461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16589056475413719089289229 6220896178280144658483461)
                    ·
                      refine ⟨1166418033427527123465649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6220896178280144658483461 1166418033427527123465649)
                      ·
                        rfl

theorem cell23_2271591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2271591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271591 prefixEnd_2271591 := by exact prefixLift 2271591
  have htrace : WordTrace (prefixWord ++ tailWord_2271591) baseStart_2271591 baseEnd_2271591 := by
    simpa [prefixWord, tailWord_2271591, baseEnd_2271591] using wordTrace_append hprefix tailTrace_2271591
  have hstable : (prefixWord ++ tailWord_2271591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271591).length < 2 ^ (prefixWord ++ tailWord_2271591).sum := by decide
  have hdescent : baseEnd_2271591 < baseStart_2271591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271641 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 4, 3, 3]
def baseStart_2271641 : Nat := 118140960795 + 2271641 * 2 ^ 59
def prefixEnd_2271641 : Nat := 4983230072969 + 3 ^ 40 * 2271641 * 2
def baseEnd_2271641 : Nat := 1166443707460251927840419

theorem tailTrace_2271641 : CollatzResearch.WordTrace tailWord_2271641 prefixEnd_2271641 1166443707460251927840419 := by
  unfold tailWord_2271641
  simp only [CollatzResearch.WordTrace]
  refine ⟨82853553963240097240406777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55235702642160064826937851 82853553963240097240406777)
  ·
    refine ⟨62140165472430072930305083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82853553963240097240406777 62140165472430072930305083)
    ·
      refine ⟨93210248208645109395457625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62140165472430072930305083 93210248208645109395457625)
      ·
        refine ⟨69907686156483832046593219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93210248208645109395457625 69907686156483832046593219)
        ·
          refine ⟨104861529234725748069889829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69907686156483832046593219 104861529234725748069889829)
          ·
            refine ⟨19661536731511077763104343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104861529234725748069889829 19661536731511077763104343)
            ·
              refine ⟨29492305097266616644656515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19661536731511077763104343 29492305097266616644656515)
              ·
                refine ⟨44238457645899924966984773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29492305097266616644656515 44238457645899924966984773)
                ·
                  refine ⟨8294710808606235931309645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44238457645899924966984773 8294710808606235931309645)
                  ·
                    refine ⟨3110516553227338474241117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8294710808606235931309645 3110516553227338474241117)
                    ·
                      refine ⟨1166443707460251927840419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3110516553227338474241117 1166443707460251927840419)
                      ·
                        rfl

theorem cell23_2271641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_2271641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271641 prefixEnd_2271641 := by exact prefixLift 2271641
  have htrace : WordTrace (prefixWord ++ tailWord_2271641) baseStart_2271641 baseEnd_2271641 := by
    simpa [prefixWord, tailWord_2271641, baseEnd_2271641] using wordTrace_append hprefix tailTrace_2271641
  have hstable : (prefixWord ++ tailWord_2271641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271641).length < 2 ^ (prefixWord ++ tailWord_2271641).sum := by decide
  have hdescent : baseEnd_2271641 < baseStart_2271641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271642 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2]
def baseStart_2271642 : Nat := 118140960795 + 2271642 * 2 ^ 59
def prefixEnd_2271642 : Nat := 4983230072969 + 3 ^ 40 * 2271642 * 2
def baseEnd_2271642 : Nat := 1166444220940906423927915

theorem tailTrace_2271642 : CollatzResearch.WordTrace tailWord_2271642 prefixEnd_2271642 1166444220940906423927915 := by
  unfold tailWord_2271642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20713397609059118602798295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55235726957490982940795453 20713397609059118602798295)
  ·
    refine ⟨31070096413588677904197443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20713397609059118602798295 31070096413588677904197443)
    ·
      refine ⟨46605144620383016856296165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31070096413588677904197443 46605144620383016856296165)
      ·
        refine ⟨8738464616321815660555531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46605144620383016856296165 8738464616321815660555531)
        ·
          refine ⟨13107696924482723490833297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8738464616321815660555531 13107696924482723490833297)
          ·
            refine ⟨9830772693362042618124973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13107696924482723490833297 9830772693362042618124973)
            ·
              refine ⟨3686539760010765981796865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9830772693362042618124973 3686539760010765981796865)
              ·
                refine ⟨2764904820008074486347649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3686539760010765981796865 2764904820008074486347649)
                ·
                  refine ⟨2073678615006055864760737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2764904820008074486347649 2073678615006055864760737)
                  ·
                    refine ⟨1555258961254541898570553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2073678615006055864760737 1555258961254541898570553)
                    ·
                      refine ⟨1166444220940906423927915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555258961254541898570553 1166444220940906423927915)
                      ·
                        rfl

theorem cell23_2271642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_2271642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271642 prefixEnd_2271642 := by exact prefixLift 2271642
  have htrace : WordTrace (prefixWord ++ tailWord_2271642) baseStart_2271642 baseEnd_2271642 := by
    simpa [prefixWord, tailWord_2271642, baseEnd_2271642] using wordTrace_append hprefix tailTrace_2271642
  have hstable : (prefixWord ++ tailWord_2271642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271642).length < 2 ^ (prefixWord ++ tailWord_2271642).sum := by decide
  have hdescent : baseEnd_2271642 < baseStart_2271642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271648 : List Nat := [2, 1, 1, 4, 1, 3, 2, 4, 5]
def baseStart_2271648 : Nat := 118140960795 + 2271648 * 2 ^ 59
def prefixEnd_2271648 : Nat := 4983230072969 + 3 ^ 40 * 2271648 * 2
def baseEnd_2271648 : Nat := 129605255758314822272543

theorem tailTrace_2271648 : CollatzResearch.WordTrace tailWord_2271648 prefixEnd_2271648 129605255758314822272543 := by
  unfold tailWord_2271648
  simp only [CollatzResearch.WordTrace]
  refine ⟨41426904637107368717955799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55235872849476491623941065 41426904637107368717955799)
  ·
    refine ⟨62140356955661053076933699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41426904637107368717955799 62140356955661053076933699)
    ·
      refine ⟨93210535433491579615400549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62140356955661053076933699 93210535433491579615400549)
      ·
        refine ⟨17476975393779671177887603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93210535433491579615400549 17476975393779671177887603)
        ·
          refine ⟨26215463090669506766831405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17476975393779671177887603 26215463090669506766831405)
          ·
            refine ⟨9830798659001065037561777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26215463090669506766831405 9830798659001065037561777)
            ·
              refine ⟨7373098994250798778171333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9830798659001065037561777 7373098994250798778171333)
              ·
                refine ⟨1382456061422024770907125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7373098994250798778171333 1382456061422024770907125)
                ·
                  refine ⟨129605255758314822272543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1382456061422024770907125 129605255758314822272543)
                  ·
                    rfl

theorem cell23_2271648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 5].length) (baseStart_2271648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271648 prefixEnd_2271648 := by exact prefixLift 2271648
  have htrace : WordTrace (prefixWord ++ tailWord_2271648) baseStart_2271648 baseEnd_2271648 := by
    simpa [prefixWord, tailWord_2271648, baseEnd_2271648] using wordTrace_append hprefix tailTrace_2271648
  have hstable : (prefixWord ++ tailWord_2271648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271648).length < 2 ^ (prefixWord ++ tailWord_2271648).sum := by decide
  have hdescent : baseEnd_2271648 < baseStart_2271648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271765 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_2271765 : Nat := 118140960795 + 2271765 * 2 ^ 59
def prefixEnd_2271765 : Nat := 4983230072969 + 3 ^ 40 * 2271765 * 2
def baseEnd_2271765 : Nat := 1166507379061409442689849

theorem tailTrace_2271765 : CollatzResearch.WordTrace tailWord_2271765 prefixEnd_2271765 1166507379061409442689849 := by
  unfold tailWord_2271765
  simp only [CollatzResearch.WordTrace]
  refine ⟨82858076614790866417920749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55238717743193910945280499 82858076614790866417920749)
  ·
    refine ⟨31071778730546574906720281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82858076614790866417920749 31071778730546574906720281)
    ·
      refine ⟨23303834047909931180040211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31071778730546574906720281 23303834047909931180040211)
      ·
        refine ⟨34955751071864896770060317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23303834047909931180040211 34955751071864896770060317)
        ·
          refine ⟨13108406651949336288772619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34955751071864896770060317 13108406651949336288772619)
          ·
            refine ⟨19662609977924004433158929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13108406651949336288772619 19662609977924004433158929)
            ·
              refine ⟨14746957483443003324869197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19662609977924004433158929 14746957483443003324869197)
              ·
                refine ⟨5530109056291126246825949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14746957483443003324869197 5530109056291126246825949)
                ·
                  refine ⟨2073790896109172342559731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5530109056291126246825949 2073790896109172342559731)
                  ·
                    refine ⟨3110686344163758513839597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2073790896109172342559731 3110686344163758513839597)
                    ·
                      refine ⟨1166507379061409442689849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3110686344163758513839597 1166507379061409442689849)
                      ·
                        rfl

theorem cell23_2271765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_2271765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271765 prefixEnd_2271765 := by exact prefixLift 2271765
  have htrace : WordTrace (prefixWord ++ tailWord_2271765) baseStart_2271765 baseEnd_2271765 := by
    simpa [prefixWord, tailWord_2271765, baseEnd_2271765] using wordTrace_append hprefix tailTrace_2271765
  have hstable : (prefixWord ++ tailWord_2271765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271765).length < 2 ^ (prefixWord ++ tailWord_2271765).sum := by decide
  have hdescent : baseEnd_2271765 < baseStart_2271765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271768 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 3, 5]
def baseStart_2271768 : Nat := 118140960795 + 2271768 * 2 ^ 59
def prefixEnd_2271768 : Nat := 4983230072969 + 3 ^ 40 * 2271768 * 2
def baseEnd_2271768 : Nat := 388836306501124310317445

theorem tailTrace_2271768 : CollatzResearch.WordTrace tailWord_2271768 prefixEnd_2271768 388836306501124310317445 := by
  unfold tailWord_2271768
  simp only [CollatzResearch.WordTrace]
  refine ⟨41429093016889998965139979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55238790689186665286853305 41429093016889998965139979)
  ·
    refine ⟨62143639525334998447709969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41429093016889998965139979 62143639525334998447709969)
    ·
      refine ⟨46607729644001248835782477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62143639525334998447709969 46607729644001248835782477)
      ·
        refine ⟨17477898616500468313418429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46607729644001248835782477 17477898616500468313418429)
        ·
          refine ⟨6554211981187675617531911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17477898616500468313418429 6554211981187675617531911)
          ·
            refine ⟨9831317971781513426297867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6554211981187675617531911 9831317971781513426297867)
            ·
              refine ⟨14746976957672270139446801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9831317971781513426297867 14746976957672270139446801)
              ·
                refine ⟨11060232718254202604585101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14746976957672270139446801 11060232718254202604585101)
                ·
                  refine ⟨4147587269345325976719413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11060232718254202604585101 4147587269345325976719413)
                  ·
                    refine ⟨388836306501124310317445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4147587269345325976719413 388836306501124310317445)
                    ·
                      rfl

theorem cell23_2271768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_2271768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271768 prefixEnd_2271768 := by exact prefixLift 2271768
  have htrace : WordTrace (prefixWord ++ tailWord_2271768) baseStart_2271768 baseEnd_2271768 := by
    simpa [prefixWord, tailWord_2271768, baseEnd_2271768] using wordTrace_append hprefix tailTrace_2271768
  have hstable : (prefixWord ++ tailWord_2271768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271768).length < 2 ^ (prefixWord ++ tailWord_2271768).sum := by decide
  have hdescent : baseEnd_2271768 < baseStart_2271768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271802 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 1, 5]
def baseStart_2271802 : Nat := 118140960795 + 2271802 * 2 ^ 59
def prefixEnd_2271802 : Nat := 4983230072969 + 3 ^ 40 * 2271802 * 2
def baseEnd_2271802 : Nat := 388842125948541932642393

theorem tailTrace_2271802 : CollatzResearch.WordTrace tailWord_2271802 prefixEnd_2271802 388842125948541932642393 := by
  unfold tailWord_2271802
  simp only [CollatzResearch.WordTrace]
  refine ⟨20714856528914205434254415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55239617410437881158011773 20714856528914205434254415)
  ·
    refine ⟨31072284793371308151381623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20714856528914205434254415 31072284793371308151381623)
    ·
      refine ⟨46608427190056962227072435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31072284793371308151381623 46608427190056962227072435)
      ·
        refine ⟨69912640785085443340608653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46608427190056962227072435 69912640785085443340608653)
        ·
          refine ⟨26217240294407041252728245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69912640785085443340608653 26217240294407041252728245)
          ·
            refine ⟨2457866277600660117443273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26217240294407041252728245 2457866277600660117443273)
            ·
              refine ⟨1843399708200495088082455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2457866277600660117443273 1843399708200495088082455)
              ·
                refine ⟨2765099562300742632123683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843399708200495088082455 2765099562300742632123683)
                ·
                  refine ⟨4147649343451113948185525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765099562300742632123683 4147649343451113948185525)
                  ·
                    refine ⟨388842125948541932642393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4147649343451113948185525 388842125948541932642393)
                    ·
                      rfl

theorem cell23_2271802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_2271802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271802 prefixEnd_2271802 := by exact prefixLift 2271802
  have htrace : WordTrace (prefixWord ++ tailWord_2271802) baseStart_2271802 baseEnd_2271802 := by
    simpa [prefixWord, tailWord_2271802, baseEnd_2271802] using wordTrace_append hprefix tailTrace_2271802
  have hstable : (prefixWord ++ tailWord_2271802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271802).length < 2 ^ (prefixWord ++ tailWord_2271802).sum := by decide
  have hdescent : baseEnd_2271802 < baseStart_2271802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271815 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 4, 4]
def baseStart_2271815 : Nat := 118140960795 + 2271815 * 2 ^ 59
def prefixEnd_2271815 : Nat := 4983230072969 + 3 ^ 40 * 2271815 * 2
def baseEnd_2271815 : Nat := 388844351031378082354873

theorem tailTrace_2271815 : CollatzResearch.WordTrace tailWord_2271815 prefixEnd_2271815 388844351031378082354873 := by
  unfold tailWord_2271815
  simp only [CollatzResearch.WordTrace]
  refine ⟨82859900264609724957240899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55239933509739816638160599 82859900264609724957240899)
  ·
    refine ⟨124289850396914587435861349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82859900264609724957240899 124289850396914587435861349)
    ·
      refine ⟨23304346949421485144224003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124289850396914587435861349 23304346949421485144224003)
      ·
        refine ⟨34956520424132227716336005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23304346949421485144224003 34956520424132227716336005)
        ·
          refine ⟨6554347579524792696813001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34956520424132227716336005 6554347579524792696813001)
          ·
            refine ⟨4915760684643594522609751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6554347579524792696813001 4915760684643594522609751)
            ·
              refine ⟨7373641026965391783914627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4915760684643594522609751 7373641026965391783914627)
              ·
                refine ⟨11060461540448087675871941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7373641026965391783914627 11060461540448087675871941)
                ·
                  refine ⟨2073836538834016439225989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11060461540448087675871941 2073836538834016439225989)
                  ·
                    refine ⟨388844351031378082354873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2073836538834016439225989 388844351031378082354873)
                    ·
                      rfl

theorem cell23_2271815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_2271815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271815 prefixEnd_2271815 := by exact prefixLift 2271815
  have htrace : WordTrace (prefixWord ++ tailWord_2271815) baseStart_2271815 baseEnd_2271815 := by
    simpa [prefixWord, tailWord_2271815, baseEnd_2271815] using wordTrace_append hprefix tailTrace_2271815
  have hstable : (prefixWord ++ tailWord_2271815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271815).length < 2 ^ (prefixWord ++ tailWord_2271815).sum := by decide
  have hdescent : baseEnd_2271815 < baseStart_2271815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271822 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2]
def baseStart_2271822 : Nat := 118140960795 + 2271822 * 2 ^ 59
def prefixEnd_2271822 : Nat := 4983230072969 + 3 ^ 40 * 2271822 * 2
def baseEnd_2271822 : Nat := 1166536647458715719677087

theorem tailTrace_2271822 : CollatzResearch.WordTrace tailWord_2271822 prefixEnd_2271822 1166536647458715719677087 := by
  unfold tailWord_2271822
  simp only [CollatzResearch.WordTrace]
  refine ⟨10357519446948045644093215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55240103717056243435163813 10357519446948045644093215)
  ·
    refine ⟨15536279170422068466139823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10357519446948045644093215 15536279170422068466139823)
    ·
      refine ⟨23304418755633102699209735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15536279170422068466139823 23304418755633102699209735)
      ·
        refine ⟨34956628133449654048814603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23304418755633102699209735 34956628133449654048814603)
        ·
          refine ⟨52434942200174481073221905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34956628133449654048814603 52434942200174481073221905)
          ·
            refine ⟨39326206650130860804916429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52434942200174481073221905 39326206650130860804916429)
            ·
              refine ⟨14747327493799072801843661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39326206650130860804916429 14747327493799072801843661)
              ·
                refine ⟨5530247810174652300691373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14747327493799072801843661 5530247810174652300691373)
                ·
                  refine ⟨2073842928815494612759265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5530247810174652300691373 2073842928815494612759265)
                  ·
                    refine ⟨1555382196611620959569449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2073842928815494612759265 1555382196611620959569449)
                    ·
                      refine ⟨1166536647458715719677087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555382196611620959569449 1166536647458715719677087)
                      ·
                        rfl

theorem cell23_2271822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_2271822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271822 prefixEnd_2271822 := by exact prefixLift 2271822
  have htrace : WordTrace (prefixWord ++ tailWord_2271822) baseStart_2271822 baseEnd_2271822 := by
    simpa [prefixWord, tailWord_2271822, baseEnd_2271822] using wordTrace_append hprefix tailTrace_2271822
  have hstable : (prefixWord ++ tailWord_2271822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271822).length < 2 ^ (prefixWord ++ tailWord_2271822).sum := by decide
  have hdescent : baseEnd_2271822 < baseStart_2271822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271855 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 4, 1, 3]
def baseStart_2271855 : Nat := 118140960795 + 2271855 * 2 ^ 59
def prefixEnd_2271855 : Nat := 4983230072969 + 3 ^ 40 * 2271855 * 2
def baseEnd_2271855 : Nat := 1166553592320314090564435

theorem tailTrace_2271855 : CollatzResearch.WordTrace tailWord_2271855 prefixEnd_2271855 1166553592320314090564435 := by
  unfold tailWord_2271855
  simp only [CollatzResearch.WordTrace]
  refine ⟨82861359184464811788697019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55240906122976541192464679 82861359184464811788697019)
  ·
    refine ⟨124292038776697217683045529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82861359184464811788697019 124292038776697217683045529)
    ·
      refine ⟨93219029082522913262284147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124292038776697217683045529 93219029082522913262284147)
      ·
        refine ⟨139828543623784369893426221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93219029082522913262284147 139828543623784369893426221)
        ·
          refine ⟨52435703858919138710034833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139828543623784369893426221 52435703858919138710034833)
          ·
            refine ⟨39326777894189354032526125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52435703858919138710034833 39326777894189354032526125)
            ·
              refine ⟨14747541710321007762197297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39326777894189354032526125 14747541710321007762197297)
              ·
                refine ⟨11060656282740755821647973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14747541710321007762197297 11060656282740755821647973)
                ·
                  refine ⟨2073873053013891716558995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11060656282740755821647973 2073873053013891716558995)
                  ·
                    refine ⟨3110809579520837574838493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2073873053013891716558995 3110809579520837574838493)
                    ·
                      refine ⟨1166553592320314090564435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3110809579520837574838493 1166553592320314090564435)
                      ·
                        rfl

theorem cell23_2271855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 1, 3].length) (baseStart_2271855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271855 prefixEnd_2271855 := by exact prefixLift 2271855
  have htrace : WordTrace (prefixWord ++ tailWord_2271855) baseStart_2271855 baseEnd_2271855 := by
    simpa [prefixWord, tailWord_2271855, baseEnd_2271855] using wordTrace_append hprefix tailTrace_2271855
  have hstable : (prefixWord ++ tailWord_2271855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271855).length < 2 ^ (prefixWord ++ tailWord_2271855).sum := by decide
  have hdescent : baseEnd_2271855 < baseStart_2271855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271862 : List Nat := [5, 1, 1, 2, 4, 1, 9]
def baseStart_2271862 : Nat := 118140960795 + 2271862 * 2 ^ 59
def prefixEnd_2271862 : Nat := 4983230072969 + 3 ^ 40 * 2271862 * 2
def baseEnd_2271862 : Nat := 14401940576356735347863

theorem tailTrace_2271862 : CollatzResearch.WordTrace tailWord_2271862 prefixEnd_2271862 14401940576356735347863 := by
  unfold tailWord_2271862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5178850905964965749012615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55241076330292967989467893 5178850905964965749012615)
  ·
    refine ⟨7768276358947448623518923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5178850905964965749012615 7768276358947448623518923)
    ·
      refine ⟨11652414538421172935278385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7768276358947448623518923 11652414538421172935278385)
      ·
        refine ⟨8739310903815879701458789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11652414538421172935278385 8739310903815879701458789)
        ·
          refine ⟨1638620794465477444023523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8739310903815879701458789 1638620794465477444023523)
          ·
            refine ⟨2457931191698216166035285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638620794465477444023523 2457931191698216166035285)
            ·
              refine ⟨14401940576356735347863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2457931191698216166035285 14401940576356735347863)
              ·
                rfl

theorem cell23_2271862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 9].length) (baseStart_2271862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271862 prefixEnd_2271862 := by exact prefixLift 2271862
  have htrace : WordTrace (prefixWord ++ tailWord_2271862) baseStart_2271862 baseEnd_2271862 := by
    simpa [prefixWord, tailWord_2271862, baseEnd_2271862] using wordTrace_append hprefix tailTrace_2271862
  have hstable : (prefixWord ++ tailWord_2271862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271862).length < 2 ^ (prefixWord ++ tailWord_2271862).sum := by decide
  have hdescent : baseEnd_2271862 < baseStart_2271862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271985 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_2271985 : Nat := 118140960795 + 2271985 * 2 ^ 59
def prefixEnd_2271985 : Nat := 4983230072969 + 3 ^ 40 * 2271985 * 2
def baseEnd_2271985 : Nat := 1166620344805398581938837

theorem tailTrace_2271985 : CollatzResearch.WordTrace tailWord_2271985 prefixEnd_2271985 1166620344805398581938837 := by
  unfold tailWord_2271985
  simp only [CollatzResearch.WordTrace]
  refine ⟨82866100673993843990929409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55244067115995895993952939 82866100673993843990929409)
  ·
    refine ⟨62149575505495382993197057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82866100673993843990929409 62149575505495382993197057)
    ·
      refine ⟨46612181629121537244897793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62149575505495382993197057 46612181629121537244897793)
      ·
        refine ⟨34959136221841152933673345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46612181629121537244897793 34959136221841152933673345)
        ·
          refine ⟨26219352166380864700255009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34959136221841152933673345 26219352166380864700255009)
          ·
            refine ⟨19664514124785648525191257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26219352166380864700255009 19664514124785648525191257)
            ·
              refine ⟨14748385593589236393893443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19664514124785648525191257 14748385593589236393893443)
              ·
                refine ⟨22122578390383854590840165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14748385593589236393893443 22122578390383854590840165)
                ·
                  refine ⟨4147983448196972735782531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22122578390383854590840165 4147983448196972735782531)
                  ·
                    refine ⟨6221975172295459103673797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4147983448196972735782531 6221975172295459103673797)
                    ·
                      refine ⟨1166620344805398581938837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6221975172295459103673797 1166620344805398581938837)
                      ·
                        rfl

theorem cell23_2271985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_2271985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2271985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2271985 prefixEnd_2271985 := by exact prefixLift 2271985
  have htrace : WordTrace (prefixWord ++ tailWord_2271985) baseStart_2271985 baseEnd_2271985 := by
    simpa [prefixWord, tailWord_2271985, baseEnd_2271985] using wordTrace_append hprefix tailTrace_2271985
  have hstable : (prefixWord ++ tailWord_2271985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271985).length < 2 ^ (prefixWord ++ tailWord_2271985).sum := by decide
  have hdescent : baseEnd_2271985 < baseStart_2271985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272002 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2272002 : Nat := 118140960795 + 2272002 * 2 ^ 59
def prefixEnd_2272002 : Nat := 4983230072969 + 3 ^ 40 * 2272002 * 2
def baseEnd_2272002 : Nat := 1166629073976525015426259

theorem tailTrace_2272002 : CollatzResearch.WordTrace tailWord_2272002 prefixEnd_2272002 1166629073976525015426259 := by
  unfold tailWord_2272002
  simp only [CollatzResearch.WordTrace]
  refine ⟨20716680178733063973574565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55244480476621503929532173 20716680178733063973574565)
  ·
    refine ⟨3884377533512449495045231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20716680178733063973574565 3884377533512449495045231)
    ·
      refine ⟨5826566300268674242567847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3884377533512449495045231 5826566300268674242567847)
      ·
        refine ⟨8739849450403011363851771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5826566300268674242567847 8739849450403011363851771)
        ·
          refine ⟨13109774175604517045777657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8739849450403011363851771 13109774175604517045777657)
          ·
            refine ⟨9832330631703387784333243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13109774175604517045777657 9832330631703387784333243)
            ·
              refine ⟨14748495947555081676499865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9832330631703387784333243 14748495947555081676499865)
              ·
                refine ⟨11061371960666311257374899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14748495947555081676499865 11061371960666311257374899)
                ·
                  refine ⟨16592057940999466886062349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11061371960666311257374899 16592057940999466886062349)
                  ·
                    refine ⟨6222021727874800082273381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16592057940999466886062349 6222021727874800082273381)
                    ·
                      refine ⟨1166629073976525015426259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6222021727874800082273381 1166629073976525015426259)
                      ·
                        rfl

theorem cell23_2272002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2272002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272002 prefixEnd_2272002 := by exact prefixLift 2272002
  have htrace : WordTrace (prefixWord ++ tailWord_2272002) baseStart_2272002 baseEnd_2272002 := by
    simpa [prefixWord, tailWord_2272002, baseEnd_2272002] using wordTrace_append hprefix tailTrace_2272002
  have hstable : (prefixWord ++ tailWord_2272002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272002).length < 2 ^ (prefixWord ++ tailWord_2272002).sum := by decide
  have hdescent : baseEnd_2272002 < baseStart_2272002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272046 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2272046 : Nat := 118140960795 + 2272046 * 2 ^ 59
def prefixEnd_2272046 : Nat := 4983230072969 + 3 ^ 40 * 2272046 * 2
def baseEnd_2272046 : Nat := 388883889041774281092019

theorem tailTrace_2272046 : CollatzResearch.WordTrace tailWord_2272046 prefixEnd_2272046 388883889041774281092019 := by
  unfold tailWord_2272046
  simp only [CollatzResearch.WordTrace]
  refine ⟨10358540690846606426112499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55245550351181900939266661 10358540690846606426112499)
  ·
    refine ⟨15537811036269909639168749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10358540690846606426112499 15537811036269909639168749)
    ·
      refine ⟨5826679138601216114688281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15537811036269909639168749 5826679138601216114688281)
      ·
        refine ⟨4370009353950912086016211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5826679138601216114688281 4370009353950912086016211)
        ·
          refine ⟨6555014030926368129024317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370009353950912086016211 6555014030926368129024317)
          ·
            refine ⟨2458130261597388048384119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6555014030926368129024317 2458130261597388048384119)
            ·
              refine ⟨3687195392396082072576179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458130261597388048384119 3687195392396082072576179)
              ·
                refine ⟨5530793088594123108864269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3687195392396082072576179 5530793088594123108864269)
                ·
                  refine ⟨2074047408222796165824101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5530793088594123108864269 2074047408222796165824101)
                  ·
                    refine ⟨388883889041774281092019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2074047408222796165824101 388883889041774281092019)
                    ·
                      rfl

theorem cell23_2272046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2272046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272046 prefixEnd_2272046 := by exact prefixLift 2272046
  have htrace : WordTrace (prefixWord ++ tailWord_2272046) baseStart_2272046 baseEnd_2272046 := by
    simpa [prefixWord, tailWord_2272046, baseEnd_2272046] using wordTrace_append hprefix tailTrace_2272046
  have hstable : (prefixWord ++ tailWord_2272046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272046).length < 2 ^ (prefixWord ++ tailWord_2272046).sum := by decide
  have hdescent : baseEnd_2272046 < baseStart_2272046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272055 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 3, 5]
def baseStart_2272055 : Nat := 118140960795 + 2272055 * 2 ^ 59
def prefixEnd_2272055 : Nat := 4983230072969 + 3 ^ 40 * 2272055 * 2
def baseEnd_2272055 : Nat := 388885429483737769354505

theorem tailTrace_2272055 : CollatzResearch.WordTrace tailWord_2272055 prefixEnd_2272055 388885429483737769354505 := by
  unfold tailWord_2272055
  simp only [CollatzResearch.WordTrace]
  refine ⟨82868653783740245945977619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55245769189160163963985079 82868653783740245945977619)
  ·
    refine ⟨124302980675610368918966429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82868653783740245945977619 124302980675610368918966429)
    ·
      refine ⟨46613617753353888344612411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124302980675610368918966429 46613617753353888344612411)
      ·
        refine ⟨69920426630030832516918617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46613617753353888344612411 69920426630030832516918617)
        ·
          refine ⟨52440319972523124387688963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69920426630030832516918617 52440319972523124387688963)
          ·
            refine ⟨78660479958784686581533445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52440319972523124387688963 78660479958784686581533445)
            ·
              refine ⟨14748839992272128734037521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78660479958784686581533445 14748839992272128734037521)
              ·
                refine ⟨11061629994204096550528141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14748839992272128734037521 11061629994204096550528141)
                ·
                  refine ⟨4148111247826536206448053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11061629994204096550528141 4148111247826536206448053)
                  ·
                    refine ⟨388885429483737769354505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4148111247826536206448053 388885429483737769354505)
                    ·
                      rfl

theorem cell23_2272055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_2272055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272055 prefixEnd_2272055 := by exact prefixLift 2272055
  have htrace : WordTrace (prefixWord ++ tailWord_2272055) baseStart_2272055 baseEnd_2272055 := by
    simpa [prefixWord, tailWord_2272055, baseEnd_2272055] using wordTrace_append hprefix tailTrace_2272055
  have hstable : (prefixWord ++ tailWord_2272055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272055).length < 2 ^ (prefixWord ++ tailWord_2272055).sum := by decide
  have hdescent : baseEnd_2272055 < baseStart_2272055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272089 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 1, 5]
def baseStart_2272089 : Nat := 118140960795 + 2272089 * 2 ^ 59
def prefixEnd_2272089 : Nat := 4983230072969 + 3 ^ 40 * 2272089 * 2
def baseEnd_2272089 : Nat := 388891248931155391679453

theorem tailTrace_2272089 : CollatzResearch.WordTrace tailWord_2272089 prefixEnd_2272089 388891248931155391679453 := by
  unfold tailWord_2272089
  simp only [CollatzResearch.WordTrace]
  refine ⟨82869893865617069752715321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55246595910411379835143547 82869893865617069752715321)
  ·
    refine ⟨62152420399212802314536491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82869893865617069752715321 62152420399212802314536491)
    ·
      refine ⟨93228630598819203471804737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62152420399212802314536491 93228630598819203471804737)
      ·
        refine ⟨69921472949114402603853553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93228630598819203471804737 69921472949114402603853553)
        ·
          refine ⟨52441104711835801952890165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69921472949114402603853553 52441104711835801952890165)
          ·
            refine ⟨4916353566734606433083453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52441104711835801952890165 4916353566734606433083453)
            ·
              refine ⟨1843632587525477412406295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4916353566734606433083453 1843632587525477412406295)
              ·
                refine ⟨2765448881288216118609443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843632587525477412406295 2765448881288216118609443)
                ·
                  refine ⟨4148173321932324177914165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765448881288216118609443 4148173321932324177914165)
                  ·
                    refine ⟨388891248931155391679453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4148173321932324177914165 388891248931155391679453)
                    ·
                      rfl

theorem cell23_2272089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 5].length) (baseStart_2272089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272089 prefixEnd_2272089 := by exact prefixLift 2272089
  have htrace : WordTrace (prefixWord ++ tailWord_2272089) baseStart_2272089 baseEnd_2272089 := by
    simpa [prefixWord, tailWord_2272089, baseEnd_2272089] using wordTrace_append hprefix tailTrace_2272089
  have hstable : (prefixWord ++ tailWord_2272089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272089).length < 2 ^ (prefixWord ++ tailWord_2272089).sum := by decide
  have hdescent : baseEnd_2272089 < baseStart_2272089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272103 : List Nat := [1, 1, 5, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_2272103 : Nat := 118140960795 + 2272103 * 2 ^ 59
def prefixEnd_2272103 : Nat := 4983230072969 + 3 ^ 40 * 2272103 * 2
def baseEnd_2272103 : Nat := 1166680935522629120263295

theorem tailTrace_2272103 : CollatzResearch.WordTrace tailWord_2272103 prefixEnd_2272103 1166680935522629120263295 := by
  unfold tailWord_2272103
  simp only [CollatzResearch.WordTrace]
  refine ⟨82870404487566350143724963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55246936325044233429149975 82870404487566350143724963)
  ·
    refine ⟨124305606731349525215587445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82870404487566350143724963 124305606731349525215587445)
    ·
      refine ⟨11653650631064017988961323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124305606731349525215587445 11653650631064017988961323)
      ·
        refine ⟨17480475946596026983441985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11653650631064017988961323 17480475946596026983441985)
        ·
          refine ⟨13110356959947020237581489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17480475946596026983441985 13110356959947020237581489)
          ·
            refine ⟨9832767719960265178186117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13110356959947020237581489 9832767719960265178186117)
            ·
              refine ⟨1843643947492549720909897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9832767719960265178186117 1843643947492549720909897)
              ·
                refine ⟨1382732960619412290682423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1843643947492549720909897 1382732960619412290682423)
                ·
                  refine ⟨2074099440929118436023635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382732960619412290682423 2074099440929118436023635)
                  ·
                    refine ⟨3111149161393677654035453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2074099440929118436023635 3111149161393677654035453)
                    ·
                      refine ⟨1166680935522629120263295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3111149161393677654035453 1166680935522629120263295)
                      ·
                        rfl

theorem cell23_2272103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_2272103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272103 prefixEnd_2272103 := by exact prefixLift 2272103
  have htrace : WordTrace (prefixWord ++ tailWord_2272103) baseStart_2272103 baseEnd_2272103 := by
    simpa [prefixWord, tailWord_2272103, baseEnd_2272103] using wordTrace_append hprefix tailTrace_2272103
  have hstable : (prefixWord ++ tailWord_2272103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272103).length < 2 ^ (prefixWord ++ tailWord_2272103).sum := by decide
  have hdescent : baseEnd_2272103 < baseStart_2272103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272112 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 3]
def baseStart_2272112 : Nat := 118140960795 + 2272112 * 2 ^ 59
def prefixEnd_2272112 : Nat := 4983230072969 + 3 ^ 40 * 2272112 * 2
def baseEnd_2272112 : Nat := 1166685556848519585050753

theorem tailTrace_2272112 : CollatzResearch.WordTrace tailWord_2272112 prefixEnd_2272112 1166685556848519585050753 := by
  unfold tailWord_2272112
  simp only [CollatzResearch.WordTrace]
  refine ⟨41435366372266872340401295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55247155163022496453868393 41435366372266872340401295)
  ·
    refine ⟨62153049558400308510601943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41435366372266872340401295 62153049558400308510601943)
    ·
      refine ⟨93229574337600462765902915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62153049558400308510601943 93229574337600462765902915)
      ·
        refine ⟨139844361506400694148854373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93229574337600462765902915 139844361506400694148854373)
        ·
          refine ⟨26220817782450130152910195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139844361506400694148854373 26220817782450130152910195)
          ·
            refine ⟨39331226673675195229365293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26220817782450130152910195 39331226673675195229365293)
            ·
              refine ⟨14749210002628198211011985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39331226673675195229365293 14749210002628198211011985)
              ·
                refine ⟨11061907501971148658258989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14749210002628198211011985 11061907501971148658258989)
                ·
                  refine ⟨4148215313239180746847121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11061907501971148658258989 4148215313239180746847121)
                  ·
                    refine ⟨3111161484929385560135341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4148215313239180746847121 3111161484929385560135341)
                    ·
                      refine ⟨1166685556848519585050753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3111161484929385560135341 1166685556848519585050753)
                      ·
                        rfl

theorem cell23_2272112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 3].length) (baseStart_2272112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272112 prefixEnd_2272112 := by exact prefixLift 2272112
  have htrace : WordTrace (prefixWord ++ tailWord_2272112) baseStart_2272112 baseEnd_2272112 := by
    simpa [prefixWord, tailWord_2272112, baseEnd_2272112] using wordTrace_append hprefix tailTrace_2272112
  have hstable : (prefixWord ++ tailWord_2272112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272112).length < 2 ^ (prefixWord ++ tailWord_2272112).sum := by decide
  have hdescent : baseEnd_2272112 < baseStart_2272112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272115 : List Nat := [1, 1, 1, 2, 2, 1, 7, 8]
def baseStart_2272115 : Nat := 118140960795 + 2272115 * 2 ^ 59
def prefixEnd_2272115 : Nat := 4983230072969 + 3 ^ 40 * 2272115 * 2
def baseEnd_2272115 : Nat := 43210633232980854567157

theorem tailTrace_2272115 : CollatzResearch.WordTrace tailWord_2272115 prefixEnd_2272115 43210633232980854567157 := by
  unfold tailWord_2272115
  simp only [CollatzResearch.WordTrace]
  refine ⟨82870842163522876193161799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55247228109015250795441199 82870842163522876193161799)
  ·
    refine ⟨124306263245284314289742699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82870842163522876193161799 124306263245284314289742699)
    ·
      refine ⟨186459394867926471434614049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124306263245284314289742699 186459394867926471434614049)
      ·
        refine ⟨139844546150944853575960537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186459394867926471434614049 139844546150944853575960537)
        ·
          refine ⟨104883409613208640181970403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139844546150944853575960537 104883409613208640181970403)
          ·
            refine ⟨157325114419812960272955605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104883409613208640181970403 157325114419812960272955605)
            ·
              refine ⟨3687307369214366256397397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 157325114419812960272955605 3687307369214366256397397)
              ·
                refine ⟨43210633232980854567157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3687307369214366256397397 43210633232980854567157)
                ·
                  rfl

theorem cell23_2272115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 8].length) (baseStart_2272115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272115 prefixEnd_2272115 := by exact prefixLift 2272115
  have htrace : WordTrace (prefixWord ++ tailWord_2272115) baseStart_2272115 baseEnd_2272115 := by
    simpa [prefixWord, tailWord_2272115, baseEnd_2272115] using wordTrace_append hprefix tailTrace_2272115
  have hstable : (prefixWord ++ tailWord_2272115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272115).length < 2 ^ (prefixWord ++ tailWord_2272115).sum := by decide
  have hdescent : baseEnd_2272115 < baseStart_2272115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272173 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2272173 : Nat := 118140960795 + 2272173 * 2 ^ 59
def prefixEnd_2272173 : Nat := 4983230072969 + 3 ^ 40 * 2272173 * 2
def baseEnd_2272173 : Nat := 1166716879168443846387973

theorem tailTrace_2272173 : CollatzResearch.WordTrace tailWord_2272173 prefixEnd_2272173 1166716879168443846387973 := by
  unfold tailWord_2272173
  simp only [CollatzResearch.WordTrace]
  refine ⟨82872957597312752098773173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55248638398208501399182115 82872957597312752098773173)
  ·
    refine ⟨7769339774748070509259985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82872957597312752098773173 7769339774748070509259985)
    ·
      refine ⟨5827004831061052881944989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7769339774748070509259985 5827004831061052881944989)
      ·
        refine ⟨2185126811647894830729371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5827004831061052881944989 2185126811647894830729371)
        ·
          refine ⟨3277690217471842246094057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2185126811647894830729371 3277690217471842246094057)
          ·
            refine ⟨2458267663103881684570543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3277690217471842246094057 2458267663103881684570543)
            ·
              refine ⟨3687401494655822526855815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458267663103881684570543 3687401494655822526855815)
              ·
                refine ⟨5531102241983733790283723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3687401494655822526855815 5531102241983733790283723)
                ·
                  refine ⟨8296653362975600685425585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5531102241983733790283723 8296653362975600685425585)
                  ·
                    refine ⟨6222490022231700514069189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8296653362975600685425585 6222490022231700514069189)
                    ·
                      refine ⟨1166716879168443846387973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6222490022231700514069189 1166716879168443846387973)
                      ·
                        rfl

theorem cell23_2272173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2272173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272173 prefixEnd_2272173 := by exact prefixLift 2272173
  have htrace : WordTrace (prefixWord ++ tailWord_2272173) baseStart_2272173 baseEnd_2272173 := by
    simpa [prefixWord, tailWord_2272173, baseEnd_2272173] using wordTrace_append hprefix tailTrace_2272173
  have hstable : (prefixWord ++ tailWord_2272173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272173).length < 2 ^ (prefixWord ++ tailWord_2272173).sum := by decide
  have hdescent : baseEnd_2272173 < baseStart_2272173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272175 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 1, 8]
def baseStart_2272175 : Nat := 118140960795 + 2272175 * 2 ^ 59
def prefixEnd_2272175 : Nat := 4983230072969 + 3 ^ 40 * 2272175 * 2
def baseEnd_2272175 : Nat := 388905968709917612854321

theorem tailTrace_2272175 : CollatzResearch.WordTrace tailWord_2272175 prefixEnd_2272175 388905968709917612854321 := by
  unfold tailWord_2272175
  simp only [CollatzResearch.WordTrace]
  refine ⟨82873030543305506440345979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55248687028870337626897319 82873030543305506440345979)
  ·
    refine ⟨124309545814958259660518969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82873030543305506440345979 124309545814958259660518969)
    ·
      refine ⟨93232159361218694745389227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124309545814958259660518969 93232159361218694745389227)
      ·
        refine ⟨139848239041828042118083841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93232159361218694745389227 139848239041828042118083841)
        ·
          refine ⟨104886179281371031588562881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139848239041828042118083841 104886179281371031588562881)
          ·
            refine ⟨78664634461028273691422161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104886179281371031588562881 78664634461028273691422161)
            ·
              refine ⟨58998475845771205268566621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78664634461028273691422161 58998475845771205268566621)
              ·
                refine ⟨22124428442164201975712483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58998475845771205268566621 22124428442164201975712483)
                ·
                  refine ⟨33186642663246302963568725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22124428442164201975712483 33186642663246302963568725)
                  ·
                    refine ⟨388905968709917612854321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33186642663246302963568725 388905968709917612854321)
                    ·
                      rfl

theorem cell23_2272175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_2272175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272175 prefixEnd_2272175 := by exact prefixLift 2272175
  have htrace : WordTrace (prefixWord ++ tailWord_2272175) baseStart_2272175 baseEnd_2272175 := by
    simpa [prefixWord, tailWord_2272175, baseEnd_2272175] using wordTrace_append hprefix tailTrace_2272175
  have hstable : (prefixWord ++ tailWord_2272175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272175).length < 2 ^ (prefixWord ++ tailWord_2272175).sum := by decide
  have hdescent : baseEnd_2272175 < baseStart_2272175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272186 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2]
def baseStart_2272186 : Nat := 118140960795 + 2272186 * 2 ^ 59
def prefixEnd_2272186 : Nat := 4983230072969 + 3 ^ 40 * 2272186 * 2
def baseEnd_2272186 : Nat := 1166723554416952295525413

theorem tailTrace_2272186 : CollatzResearch.WordTrace tailWord_2272186 prefixEnd_2272186 1166723554416952295525413 := by
  unfold tailWord_2272186
  simp only [CollatzResearch.WordTrace]
  refine ⟨20718357936566413829749103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55248954497510436879330941 20718357936566413829749103)
  ·
    refine ⟨31077536904849620744623655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20718357936566413829749103 31077536904849620744623655)
    ·
      refine ⟨46616305357274431116935483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31077536904849620744623655 46616305357274431116935483)
      ·
        refine ⟨69924458035911646675403225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46616305357274431116935483 69924458035911646675403225)
        ·
          refine ⟨52443343526933735006552419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69924458035911646675403225 52443343526933735006552419)
          ·
            refine ⟨78665015290400602509828629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52443343526933735006552419 78665015290400602509828629)
            ·
              refine ⟨3687422591737528242648217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78665015290400602509828629 3687422591737528242648217)
              ·
                refine ⟨2765566943803146181986163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3687422591737528242648217 2765566943803146181986163)
                ·
                  refine ⟨4148350415704719272979245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765566943803146181986163 4148350415704719272979245)
                  ·
                    refine ⟨1555631405889269727367217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4148350415704719272979245 1555631405889269727367217)
                    ·
                      refine ⟨1166723554416952295525413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555631405889269727367217 1166723554416952295525413)
                      ·
                        rfl

theorem cell23_2272186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2].length) (baseStart_2272186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272186 prefixEnd_2272186 := by exact prefixLift 2272186
  have htrace : WordTrace (prefixWord ++ tailWord_2272186) baseStart_2272186 baseEnd_2272186 := by
    simpa [prefixWord, tailWord_2272186, baseEnd_2272186] using wordTrace_append hprefix tailTrace_2272186
  have hstable : (prefixWord ++ tailWord_2272186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272186).length < 2 ^ (prefixWord ++ tailWord_2272186).sum := by decide
  have hdescent : baseEnd_2272186 < baseStart_2272186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272199 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 1, 4, 2]
def baseStart_2272199 : Nat := 118140960795 + 2272199 * 2 ^ 59
def prefixEnd_2272199 : Nat := 4983230072969 + 3 ^ 40 * 2272199 * 2
def baseEnd_2272199 : Nat := 1166730229665460744662853

theorem tailTrace_2272199 : CollatzResearch.WordTrace tailWord_2272199 prefixEnd_2272199 1166730229665460744662853 := by
  unfold tailWord_2272199
  simp only [CollatzResearch.WordTrace]
  refine ⟨82873905895218558539219651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55249270596812372359479767 82873905895218558539219651)
  ·
    refine ⟨124310858842827837808829477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82873905895218558539219651 124310858842827837808829477)
    ·
      refine ⟨23308286033030219589155527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124310858842827837808829477 23308286033030219589155527)
      ·
        refine ⟨34962429049545329383733291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23308286033030219589155527 34962429049545329383733291)
        ·
          refine ⟨52443643574317994075599937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34962429049545329383733291 52443643574317994075599937)
          ·
            refine ⟨39332732680738495556699953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52443643574317994075599937 39332732680738495556699953)
            ·
              refine ⟨29499549510553871667524965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39332732680738495556699953 29499549510553871667524965)
              ·
                refine ⟨5531165533228850937660931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29499549510553871667524965 5531165533228850937660931)
                ·
                  refine ⟨8296748299843276406491397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5531165533228850937660931 8296748299843276406491397)
                  ·
                    refine ⟨1555640306220614326217137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8296748299843276406491397 1555640306220614326217137)
                    ·
                      refine ⟨1166730229665460744662853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555640306220614326217137 1166730229665460744662853)
                      ·
                        rfl

theorem cell23_2272199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_2272199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272199 prefixEnd_2272199 := by exact prefixLift 2272199
  have htrace : WordTrace (prefixWord ++ tailWord_2272199) baseStart_2272199 baseEnd_2272199 := by
    simpa [prefixWord, tailWord_2272199, baseEnd_2272199] using wordTrace_append hprefix tailTrace_2272199
  have hstable : (prefixWord ++ tailWord_2272199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272199).length < 2 ^ (prefixWord ++ tailWord_2272199).sum := by decide
  have hdescent : baseEnd_2272199 < baseStart_2272199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272202 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_2272202 : Nat := 118140960795 + 2272202 * 2 ^ 59
def prefixEnd_2272202 : Nat := 4983230072969 + 3 ^ 40 * 2272202 * 2
def baseEnd_2272202 : Nat := 1166731770107424232925339

theorem tailTrace_2272202 : CollatzResearch.WordTrace tailWord_2272202 prefixEnd_2272202 1166731770107424232925339 := by
  unfold tailWord_2272202
  simp only [CollatzResearch.WordTrace]
  refine ⟨20718503828551922512894715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55249343542805126701052573 20718503828551922512894715)
  ·
    refine ⟨31077755742827883769342073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20718503828551922512894715 31077755742827883769342073)
    ·
      refine ⟨23308316807120912827006555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31077755742827883769342073 23308316807120912827006555)
      ·
        refine ⟨34962475210681369240509833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23308316807120912827006555 34962475210681369240509833)
        ·
          refine ⟨26221856408011026930382375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34962475210681369240509833 26221856408011026930382375)
          ·
            refine ⟨39332784612016540395573563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26221856408011026930382375 39332784612016540395573563)
            ·
              refine ⟨58999176918024810593360345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39332784612016540395573563 58999176918024810593360345)
              ·
                refine ⟨44249382688518607945020259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58999176918024810593360345 44249382688518607945020259)
                ·
                  refine ⟨66374074032777911917530389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44249382688518607945020259 66374074032777911917530389)
                  ·
                    refine ⟨3111284720286464621134237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66374074032777911917530389 3111284720286464621134237)
                    ·
                      refine ⟨1166731770107424232925339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3111284720286464621134237 1166731770107424232925339)
                      ·
                        rfl

theorem cell23_2272202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_2272202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272202 prefixEnd_2272202 := by exact prefixLift 2272202
  have htrace : WordTrace (prefixWord ++ tailWord_2272202) baseStart_2272202 baseEnd_2272202 := by
    simpa [prefixWord, tailWord_2272202, baseEnd_2272202] using wordTrace_append hprefix tailTrace_2272202
  have hstable : (prefixWord ++ tailWord_2272202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272202).length < 2 ^ (prefixWord ++ tailWord_2272202).sum := by decide
  have hdescent : baseEnd_2272202 < baseStart_2272202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272216 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 4, 2, 2]
def baseStart_2272216 : Nat := 118140960795 + 2272216 * 2 ^ 59
def prefixEnd_2272216 : Nat := 4983230072969 + 3 ^ 40 * 2272216 * 2
def baseEnd_2272216 : Nat := 1166738958836587178150275

theorem tailTrace_2272216 : CollatzResearch.WordTrace tailWord_2272216 prefixEnd_2272216 1166738958836587178150275 := by
  unfold tailWord_2272216
  simp only [CollatzResearch.WordTrace]
  refine ⟨41437262968078485221294251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55249683957437980295059001 41437262968078485221294251)
  ·
    refine ⟨62155894452117727831941377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41437262968078485221294251 62155894452117727831941377)
    ·
      refine ⟨46616920839088295873956033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62155894452117727831941377 46616920839088295873956033)
      ·
        refine ⟨34962690629316221905467025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46616920839088295873956033 34962690629316221905467025)
        ·
          refine ⟨26222017971987166429100269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34962690629316221905467025 26222017971987166429100269)
          ·
            refine ⟨9833256739495187410912601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26222017971987166429100269 9833256739495187410912601)
            ·
              refine ⟨7374942554621390558184451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9833256739495187410912601 7374942554621390558184451)
              ·
                refine ⟨11062413831932085837276677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7374942554621390558184451 11062413831932085837276677)
                ·
                  refine ⟨2074202593487266094489377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11062413831932085837276677 2074202593487266094489377)
                  ·
                    refine ⟨1555651945115449570867033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2074202593487266094489377 1555651945115449570867033)
                    ·
                      refine ⟨1166738958836587178150275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555651945115449570867033 1166738958836587178150275)
                      ·
                        rfl

theorem cell23_2272216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_2272216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272216 prefixEnd_2272216 := by exact prefixLift 2272216
  have htrace : WordTrace (prefixWord ++ tailWord_2272216) baseStart_2272216 baseEnd_2272216 := by
    simpa [prefixWord, tailWord_2272216, baseEnd_2272216] using wordTrace_append hprefix tailTrace_2272216
  have hstable : (prefixWord ++ tailWord_2272216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272216).length < 2 ^ (prefixWord ++ tailWord_2272216).sum := by decide
  have hdescent : baseEnd_2272216 < baseStart_2272216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272279 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2272279 : Nat := 118140960795 + 2272279 * 2 ^ 59
def prefixEnd_2272279 : Nat := 4983230072969 + 3 ^ 40 * 2272279 * 2
def baseEnd_2272279 : Nat := 1166771308117820431662485

theorem tailTrace_2272279 : CollatzResearch.WordTrace tailWord_2272279 prefixEnd_2272279 1166771308117820431662485 := by
  unfold tailWord_2272279
  simp only [CollatzResearch.WordTrace]
  refine ⟨82876823734928732202131891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55251215823285821468087927 82876823734928732202131891)
  ·
    refine ⟨124315235602393098303197837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82876823734928732202131891 124315235602393098303197837)
    ·
      refine ⟨46618213350897411863699189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124315235602393098303197837 46618213350897411863699189)
      ·
        refine ⟨4370457501646632362221799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46618213350897411863699189 4370457501646632362221799)
        ·
          refine ⟨6555686252469948543332699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370457501646632362221799 6555686252469948543332699)
          ·
            refine ⟨9833529378704922814999049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6555686252469948543332699 9833529378704922814999049)
            ·
              refine ⟨7375147034028692111249287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9833529378704922814999049 7375147034028692111249287)
              ·
                refine ⟨11062720551043038166873931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7375147034028692111249287 11062720551043038166873931)
                ·
                  refine ⟨16594080826564557250310897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11062720551043038166873931 16594080826564557250310897)
                  ·
                    refine ⟨12445560619923417937733173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16594080826564557250310897 12445560619923417937733173)
                    ·
                      refine ⟨1166771308117820431662485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12445560619923417937733173 1166771308117820431662485)
                      ·
                        rfl

theorem cell23_2272279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2272279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272279 prefixEnd_2272279 := by exact prefixLift 2272279
  have htrace : WordTrace (prefixWord ++ tailWord_2272279) baseStart_2272279 baseEnd_2272279 := by
    simpa [prefixWord, tailWord_2272279, baseEnd_2272279] using wordTrace_append hprefix tailTrace_2272279
  have hstable : (prefixWord ++ tailWord_2272279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272279).length < 2 ^ (prefixWord ++ tailWord_2272279).sum := by decide
  have hdescent : baseEnd_2272279 < baseStart_2272279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272299 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 3, 4]
def baseStart_2272299 : Nat := 118140960795 + 2272299 * 2 ^ 59
def prefixEnd_2272299 : Nat := 4983230072969 + 3 ^ 40 * 2272299 * 2
def baseEnd_2272299 : Nat := 388927192576970117804131

theorem tailTrace_2272299 : CollatzResearch.WordTrace tailWord_2272299 prefixEnd_2272299 388927192576970117804131 := by
  unfold tailWord_2272299
  simp only [CollatzResearch.WordTrace]
  refine ⟨82877553194856275617859951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55251702129904183745239967 82877553194856275617859951)
  ·
    refine ⟨124316329792284413426789927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82877553194856275617859951 124316329792284413426789927)
    ·
      refine ⟨186474494688426620140184891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124316329792284413426789927 186474494688426620140184891)
      ·
        refine ⟨279711742032639930210277337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186474494688426620140184891 279711742032639930210277337)
        ·
          refine ⟨209783806524479947657708003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279711742032639930210277337 209783806524479947657708003)
          ·
            refine ⟨314675709786719921486562005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209783806524479947657708003 314675709786719921486562005)
            ·
              refine ⟨7375211948126248159841297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 314675709786719921486562005 7375211948126248159841297)
              ·
                refine ⟨5531408961094686119880973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7375211948126248159841297 5531408961094686119880973)
                ·
                  refine ⟨2074278360410507294955365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5531408961094686119880973 2074278360410507294955365)
                  ·
                    refine ⟨388927192576970117804131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2074278360410507294955365 388927192576970117804131)
                    ·
                      rfl

theorem cell23_2272299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 4].length) (baseStart_2272299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272299 prefixEnd_2272299 := by exact prefixLift 2272299
  have htrace : WordTrace (prefixWord ++ tailWord_2272299) baseStart_2272299 baseEnd_2272299 := by
    simpa [prefixWord, tailWord_2272299, baseEnd_2272299] using wordTrace_append hprefix tailTrace_2272299
  have hstable : (prefixWord ++ tailWord_2272299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272299).length < 2 ^ (prefixWord ++ tailWord_2272299).sum := by decide
  have hdescent : baseEnd_2272299 < baseStart_2272299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272333 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_2272333 : Nat := 118140960795 + 2272333 * 2 ^ 59
def prefixEnd_2272333 : Nat := 4983230072969 + 3 ^ 40 * 2272333 * 2
def baseEnd_2272333 : Nat := 388933012024387740129079

theorem tailTrace_2272333 : CollatzResearch.WordTrace tailWord_2272333 prefixEnd_2272333 388933012024387740129079 := by
  unfold tailWord_2272333
  simp only [CollatzResearch.WordTrace]
  refine ⟨82878793276733099424597653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55252528851155399616398435 82878793276733099424597653)
  ·
    refine ⟨3884943434846864035528015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82878793276733099424597653 3884943434846864035528015)
    ·
      refine ⟨5827415152270296053292023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3884943434846864035528015 5827415152270296053292023)
      ·
        refine ⟨8741122728405444079938035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5827415152270296053292023 8741122728405444079938035)
        ·
          refine ⟨13111684092608166119907053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8741122728405444079938035 13111684092608166119907053)
          ·
            refine ⟨4916881534728062294965145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13111684092608166119907053 4916881534728062294965145)
            ·
              refine ⟨3687661151046046721223859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4916881534728062294965145 3687661151046046721223859)
              ·
                refine ⟨5531491726569070081835789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3687661151046046721223859 5531491726569070081835789)
                ·
                  refine ⟨2074309397463401280688421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5531491726569070081835789 2074309397463401280688421)
                  ·
                    refine ⟨388933012024387740129079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2074309397463401280688421 388933012024387740129079)
                    ·
                      rfl

theorem cell23_2272333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_2272333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272333 prefixEnd_2272333 := by exact prefixLift 2272333
  have htrace : WordTrace (prefixWord ++ tailWord_2272333) baseStart_2272333 baseEnd_2272333 := by
    simpa [prefixWord, tailWord_2272333, baseEnd_2272333] using wordTrace_append hprefix tailTrace_2272333
  have hstable : (prefixWord ++ tailWord_2272333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272333).length < 2 ^ (prefixWord ++ tailWord_2272333).sum := by decide
  have hdescent : baseEnd_2272333 < baseStart_2272333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272350 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2272350 : Nat := 118140960795 + 2272350 * 2 ^ 59
def prefixEnd_2272350 : Nat := 4983230072969 + 3 ^ 40 * 2272350 * 2
def baseEnd_2272350 : Nat := 388935921748096551291553

theorem tailTrace_2272350 : CollatzResearch.WordTrace tailWord_2272350 prefixEnd_2272350 388935921748096551291553 := by
  unfold tailWord_2272350
  simp only [CollatzResearch.WordTrace]
  refine ⟨10359926664708938915995813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55252942211781007551977669 10359926664708938915995813)
  ·
    refine ⟨1942486249632926046749215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10359926664708938915995813 1942486249632926046749215)
    ·
      refine ⟨2913729374449389070123823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942486249632926046749215 2913729374449389070123823)
      ·
        refine ⟨4370594061674083605185735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2913729374449389070123823 4370594061674083605185735)
        ·
          refine ⟨6555891092511125407778603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370594061674083605185735 6555891092511125407778603)
          ·
            refine ⟨9833836638766688111667905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6555891092511125407778603 9833836638766688111667905)
            ·
              refine ⟨7375377479075016083750929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9833836638766688111667905 7375377479075016083750929)
              ·
                refine ⟨5531533109306262062813197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7375377479075016083750929 5531533109306262062813197)
                ·
                  refine ⟨2074324915989848273554949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5531533109306262062813197 2074324915989848273554949)
                  ·
                    refine ⟨388935921748096551291553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2074324915989848273554949 388935921748096551291553)
                    ·
                      rfl

theorem cell23_2272350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2272350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272350 prefixEnd_2272350 := by exact prefixLift 2272350
  have htrace : WordTrace (prefixWord ++ tailWord_2272350) baseStart_2272350 baseEnd_2272350 := by
    simpa [prefixWord, tailWord_2272350, baseEnd_2272350] using wordTrace_append hprefix tailTrace_2272350
  have hstable : (prefixWord ++ tailWord_2272350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272350).length < 2 ^ (prefixWord ++ tailWord_2272350).sum := by decide
  have hdescent : baseEnd_2272350 < baseStart_2272350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272413 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_2272413 : Nat := 118140960795 + 2272413 * 2 ^ 59
def prefixEnd_2272413 : Nat := 4983230072969 + 3 ^ 40 * 2272413 * 2
def baseEnd_2272413 : Nat := 1166840114525522907386869

theorem tailTrace_2272413 : CollatzResearch.WordTrace tailWord_2272413 prefixEnd_2272413 1166840114525522907386869 := by
  unfold tailWord_2272413
  simp only [CollatzResearch.WordTrace]
  refine ⟨82881711116443273087509893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55254474077628848725006595 82881711116443273087509893)
  ·
    refine ⟨15540320834333113703908105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82881711116443273087509893 15540320834333113703908105)
    ·
      refine ⟨11655240625749835277931079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15540320834333113703908105 11655240625749835277931079)
      ·
        refine ⟨17482860938624752916896619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11655240625749835277931079 17482860938624752916896619)
        ·
          refine ⟨26224291407937129375344929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17482860938624752916896619 26224291407937129375344929)
          ·
            refine ⟨19668218555952847031508697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26224291407937129375344929 19668218555952847031508697)
            ·
              refine ⟨14751163916964635273631523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19668218555952847031508697 14751163916964635273631523)
              ·
                refine ⟨22126745875446952910447285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14751163916964635273631523 22126745875446952910447285)
                ·
                  refine ⟨2074382425823151835354433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22126745875446952910447285 2074382425823151835354433)
                  ·
                    refine ⟨1555786819367363876515825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2074382425823151835354433 1555786819367363876515825)
                    ·
                      refine ⟨1166840114525522907386869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555786819367363876515825 1166840114525522907386869)
                      ·
                        rfl

theorem cell23_2272413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_2272413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272413 prefixEnd_2272413 := by exact prefixLift 2272413
  have htrace : WordTrace (prefixWord ++ tailWord_2272413) baseStart_2272413 baseEnd_2272413 := by
    simpa [prefixWord, tailWord_2272413, baseEnd_2272413] using wordTrace_append hprefix tailTrace_2272413
  have hstable : (prefixWord ++ tailWord_2272413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272413).length < 2 ^ (prefixWord ++ tailWord_2272413).sum := by decide
  have hdescent : baseEnd_2272413 < baseStart_2272413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272416 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 3]
def baseStart_2272416 : Nat := 118140960795 + 2272416 * 2 ^ 59
def prefixEnd_2272416 : Nat := 4983230072969 + 3 ^ 40 * 2272416 * 2
def baseEnd_2272416 : Nat := 1166841654967486395649355

theorem tailTrace_2272416 : CollatzResearch.WordTrace tailWord_2272416 prefixEnd_2272416 1166841654967486395649355 := by
  unfold tailWord_2272416
  simp only [CollatzResearch.WordTrace]
  refine ⟨41440910267716202299934551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55254547023621603066579401 41440910267716202299934551)
  ·
    refine ⟨62161365401574303449901827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41440910267716202299934551 62161365401574303449901827)
    ·
      refine ⟨93242048102361455174852741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62161365401574303449901827 93242048102361455174852741)
      ·
        refine ⟨17482884019192772845284889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93242048102361455174852741 17482884019192772845284889)
        ·
          refine ⟨13112163014394579633963667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17482884019192772845284889 13112163014394579633963667)
          ·
            refine ⟨19668244521591869450945501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13112163014394579633963667 19668244521591869450945501)
            ·
              refine ⟨7375591695596951044104563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19668244521591869450945501 7375591695596951044104563)
              ·
                refine ⟨11063387543395426566156845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7375591695596951044104563 11063387543395426566156845)
                ·
                  refine ⟨4148770328773284962308817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11063387543395426566156845 4148770328773284962308817)
                  ·
                    refine ⟨3111577746579963721731613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4148770328773284962308817 3111577746579963721731613)
                    ·
                      refine ⟨1166841654967486395649355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3111577746579963721731613 1166841654967486395649355)
                      ·
                        rfl

theorem cell23_2272416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_2272416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272416 prefixEnd_2272416 := by exact prefixLift 2272416
  have htrace : WordTrace (prefixWord ++ tailWord_2272416) baseStart_2272416 baseEnd_2272416 := by
    simpa [prefixWord, tailWord_2272416, baseEnd_2272416] using wordTrace_append hprefix tailTrace_2272416
  have hstable : (prefixWord ++ tailWord_2272416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272416).length < 2 ^ (prefixWord ++ tailWord_2272416).sum := by decide
  have hdescent : baseEnd_2272416 < baseStart_2272416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272433 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2272433 : Nat := 118140960795 + 2272433 * 2 ^ 59
def prefixEnd_2272433 : Nat := 4983230072969 + 3 ^ 40 * 2272433 * 2
def baseEnd_2272433 : Nat := 1166850384138612829136777

theorem tailTrace_2272433 : CollatzResearch.WordTrace tailWord_2272433 prefixEnd_2272433 1166850384138612829136777 := by
  unfold tailWord_2272433
  simp only [CollatzResearch.WordTrace]
  refine ⟨82882440576370816503237953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55254960384247211002158635 82882440576370816503237953)
  ·
    refine ⟨62161830432278112377428465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82882440576370816503237953 62161830432278112377428465)
    ·
      refine ⟨46621372824208584283071349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62161830432278112377428465 46621372824208584283071349)
      ·
        refine ⟨4370753702269554776537939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46621372824208584283071349 4370753702269554776537939)
        ·
          refine ⟨6556130553404332164806909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370753702269554776537939 6556130553404332164806909)
          ·
            refine ⟨2458548957526624561802591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6556130553404332164806909 2458548957526624561802591)
            ·
              refine ⟨3687823436289936842703887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458548957526624561802591 3687823436289936842703887)
              ·
                refine ⟨5531735154434905264055831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3687823436289936842703887 5531735154434905264055831)
                ·
                  refine ⟨8297602731652357896083747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5531735154434905264055831 8297602731652357896083747)
                  ·
                    refine ⟨12446404097478536844125621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8297602731652357896083747 12446404097478536844125621)
                    ·
                      refine ⟨1166850384138612829136777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12446404097478536844125621 1166850384138612829136777)
                      ·
                        rfl

theorem cell23_2272433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2272433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272433 prefixEnd_2272433 := by exact prefixLift 2272433
  have htrace : WordTrace (prefixWord ++ tailWord_2272433) baseStart_2272433 baseEnd_2272433 := by
    simpa [prefixWord, tailWord_2272433, baseEnd_2272433] using wordTrace_append hprefix tailTrace_2272433
  have hstable : (prefixWord ++ tailWord_2272433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272433).length < 2 ^ (prefixWord ++ tailWord_2272433).sum := by decide
  have hdescent : baseEnd_2272433 < baseStart_2272433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272436 : List Nat := [2, 5, 3, 13]
def baseStart_2272436 : Nat := 118140960795 + 2272436 * 2 ^ 59
def prefixEnd_2272436 : Nat := 4983230072969 + 3 ^ 40 * 2272436 * 2
def baseEnd_2272436 : Nat := 533539974659614228349

theorem tailTrace_2272436 : CollatzResearch.WordTrace tailWord_2272436 prefixEnd_2272436 533539974659614228349 := by
  unfold tailWord_2272436
  simp only [CollatzResearch.WordTrace]
  refine ⟨41441274997679974007798581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55255033330239965343731441 41441274997679974007798581)
  ·
    refine ⟨3885119531032497563231117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41441274997679974007798581 3885119531032497563231117)
    ·
      refine ⟨1456919824137186586211669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3885119531032497563231117 1456919824137186586211669)
      ·
        refine ⟨533539974659614228349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1456919824137186586211669 533539974659614228349)
        ·
          rfl

theorem cell23_2272436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 13].length) (baseStart_2272436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272436 prefixEnd_2272436 := by exact prefixLift 2272436
  have htrace : WordTrace (prefixWord ++ tailWord_2272436) baseStart_2272436 baseEnd_2272436 := by
    simpa [prefixWord, tailWord_2272436, baseEnd_2272436] using wordTrace_append hprefix tailTrace_2272436
  have hstable : (prefixWord ++ tailWord_2272436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272436).length < 2 ^ (prefixWord ++ tailWord_2272436).sum := by decide
  have hdescent : baseEnd_2272436 < baseStart_2272436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272447 : List Nat := [1, 1, 2, 2, 2, 2, 6, 2, 1, 2, 2]
def baseStart_2272447 : Nat := 118140960795 + 2272447 * 2 ^ 59
def prefixEnd_2272447 : Nat := 4983230072969 + 3 ^ 40 * 2272447 * 2
def baseEnd_2272447 : Nat := 1166857572867775774361713

theorem tailTrace_2272447 : CollatzResearch.WordTrace tailWord_2272447 prefixEnd_2272447 1166857572867775774361713 := by
  unfold tailWord_2272447
  simp only [CollatzResearch.WordTrace]
  refine ⟨82882951198320096894247595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55255300798880064596165063 82882951198320096894247595)
  ·
    refine ⟨124324426797480145341371393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82882951198320096894247595 124324426797480145341371393)
    ·
      refine ⟨93243320098110109006028545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124324426797480145341371393 93243320098110109006028545)
      ·
        refine ⟨69932490073582581754521409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93243320098110109006028545 69932490073582581754521409)
        ·
          refine ⟨52449367555186936315891057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69932490073582581754521409 52449367555186936315891057)
          ·
            refine ⟨39337025666390202236918293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52449367555186936315891057 39337025666390202236918293)
            ·
              refine ⟨1843923078112040729855545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39337025666390202236918293 1843923078112040729855545)
              ·
                refine ⟨1382942308584030547391659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1843923078112040729855545 1382942308584030547391659)
                ·
                  refine ⟨2074413462876045821087489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382942308584030547391659 2074413462876045821087489)
                  ·
                    refine ⟨1555810097157034365815617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2074413462876045821087489 1555810097157034365815617)
                    ·
                      refine ⟨1166857572867775774361713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555810097157034365815617 1166857572867775774361713)
                      ·
                        rfl

theorem cell23_2272447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 1, 2, 2].length) (baseStart_2272447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272447 prefixEnd_2272447 := by exact prefixLift 2272447
  have htrace : WordTrace (prefixWord ++ tailWord_2272447) baseStart_2272447 baseEnd_2272447 := by
    simpa [prefixWord, tailWord_2272447, baseEnd_2272447] using wordTrace_append hprefix tailTrace_2272447
  have hstable : (prefixWord ++ tailWord_2272447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272447).length < 2 ^ (prefixWord ++ tailWord_2272447).sum := by decide
  have hdescent : baseEnd_2272447 < baseStart_2272447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272470 : List Nat := [5, 2, 1, 2, 2, 1, 3, 7]
def baseStart_2272470 : Nat := 118140960795 + 2272470 * 2 ^ 59
def prefixEnd_2272470 : Nat := 4983230072969 + 3 ^ 40 * 2272470 * 2
def baseEnd_2272470 : Nat := 43217384552697377199041

theorem tailTrace_2272470 : CollatzResearch.WordTrace tailWord_2272470 prefixEnd_2272470 43217384552697377199041 := by
  unfold tailWord_2272470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5180236879827298238895929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55255860051491181214889909 5180236879827298238895929)
  ·
    refine ⟨3885177659870473679171947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5180236879827298238895929 3885177659870473679171947)
    ·
      refine ⟨5827766489805710518757921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3885177659870473679171947 5827766489805710518757921)
      ·
        refine ⟨4370824867354282889068441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5827766489805710518757921 4370824867354282889068441)
        ·
          refine ⟨3278118650515712166801331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4370824867354282889068441 3278118650515712166801331)
          ·
            refine ⟨4917177975773568250201997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278118650515712166801331 4917177975773568250201997)
            ·
              refine ⟨1843941740915088093825749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4917177975773568250201997 1843941740915088093825749)
              ·
                refine ⟨43217384552697377199041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1843941740915088093825749 43217384552697377199041)
                ·
                  rfl

theorem cell23_2272470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_2272470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272470 prefixEnd_2272470 := by exact prefixLift 2272470
  have htrace : WordTrace (prefixWord ++ tailWord_2272470) baseStart_2272470 baseEnd_2272470 := by
    simpa [prefixWord, tailWord_2272470, baseEnd_2272470] using wordTrace_append hprefix tailTrace_2272470
  have hstable : (prefixWord ++ tailWord_2272470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272470).length < 2 ^ (prefixWord ++ tailWord_2272470).sum := by decide
  have hdescent : baseEnd_2272470 < baseStart_2272470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272473 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 1, 3, 2]
def baseStart_2272473 : Nat := 118140960795 + 2272473 * 2 ^ 59
def prefixEnd_2272473 : Nat := 4983230072969 + 3 ^ 40 * 2272473 * 2
def baseEnd_2272473 : Nat := 1166870923364792672636593

theorem tailTrace_2272473 : CollatzResearch.WordTrace tailWord_2272473 prefixEnd_2272473 1166870923364792672636593 := by
  unfold tailWord_2272473
  simp only [CollatzResearch.WordTrace]
  refine ⟨82883899496225903334694073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55255932997483935556462715 82883899496225903334694073)
  ·
    refine ⟨62162924622169427501020555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82883899496225903334694073 62162924622169427501020555)
    ·
      refine ⟨93244386933254141251530833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62162924622169427501020555 93244386933254141251530833)
      ·
        refine ⟨69933290199940605938648125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93244386933254141251530833 69933290199940605938648125)
        ·
          refine ⟨26224983824977727226993047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69933290199940605938648125 26224983824977727226993047)
          ·
            refine ⟨39337475737466590840489571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26224983824977727226993047 39337475737466590840489571)
            ·
              refine ⟨59006213606199886260734357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39337475737466590840489571 59006213606199886260734357)
              ·
                refine ⟨2765916262790619668471923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59006213606199886260734357 2765916262790619668471923)
                ·
                  refine ⟨4148874394185929502707885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765916262790619668471923 4148874394185929502707885)
                  ·
                    refine ⟨1555827897819723563515457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4148874394185929502707885 1555827897819723563515457)
                    ·
                      refine ⟨1166870923364792672636593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555827897819723563515457 1166870923364792672636593)
                      ·
                        rfl

theorem cell23_2272473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 3, 2].length) (baseStart_2272473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272473 prefixEnd_2272473 := by exact prefixLift 2272473
  have htrace : WordTrace (prefixWord ++ tailWord_2272473) baseStart_2272473 baseEnd_2272473 := by
    simpa [prefixWord, tailWord_2272473, baseEnd_2272473] using wordTrace_append hprefix tailTrace_2272473
  have hstable : (prefixWord ++ tailWord_2272473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272473).length < 2 ^ (prefixWord ++ tailWord_2272473).sum := by decide
  have hdescent : baseEnd_2272473 < baseStart_2272473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272490 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_2272490 : Nat := 118140960795 + 2272490 * 2 ^ 59
def prefixEnd_2272490 : Nat := 4983230072969 + 3 ^ 40 * 2272490 * 2
def baseEnd_2272490 : Nat := 1166879652535919106124015

theorem tailTrace_2272490 : CollatzResearch.WordTrace tailWord_2272490 prefixEnd_2272490 1166879652535919106124015 := by
  unfold tailWord_2272490
  simp only [CollatzResearch.WordTrace]
  refine ⟨20721129884291078809515731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55256346358109543492041949 20721129884291078809515731)
  ·
    refine ⟨31081694826436618214273597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20721129884291078809515731 31081694826436618214273597)
    ·
      refine ⟨11655635559913731830352599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31081694826436618214273597 11655635559913731830352599)
      ·
        refine ⟨17483453339870597745528899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11655635559913731830352599 17483453339870597745528899)
        ·
          refine ⟨26225180009805896618293349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17483453339870597745528899 26225180009805896618293349)
          ·
            refine ⟨4917221251838605615930003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26225180009805896618293349 4917221251838605615930003)
            ·
              refine ⟨7375831877757908423895005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4917221251838605615930003 7375831877757908423895005)
              ·
                refine ⟨2765936954159215658960627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7375831877757908423895005 2765936954159215658960627)
                ·
                  refine ⟨4148905431238823488440941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765936954159215658960627 4148905431238823488440941)
                  ·
                    refine ⟨1555839536714558808165353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4148905431238823488440941 1555839536714558808165353)
                    ·
                      refine ⟨1166879652535919106124015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555839536714558808165353 1166879652535919106124015)
                      ·
                        rfl

theorem cell23_2272490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_2272490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272490 prefixEnd_2272490 := by exact prefixLift 2272490
  have htrace : WordTrace (prefixWord ++ tailWord_2272490) baseStart_2272490 baseEnd_2272490 := by
    simpa [prefixWord, tailWord_2272490, baseEnd_2272490] using wordTrace_append hprefix tailTrace_2272490
  have hstable : (prefixWord ++ tailWord_2272490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272490).length < 2 ^ (prefixWord ++ tailWord_2272490).sum := by decide
  have hdescent : baseEnd_2272490 < baseStart_2272490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272503 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 4, 2, 2]
def baseStart_2272503 : Nat := 118140960795 + 2272503 * 2 ^ 59
def prefixEnd_2272503 : Nat := 4983230072969 + 3 ^ 40 * 2272503 * 2
def baseEnd_2272503 : Nat := 1166886327784427555261455

theorem tailTrace_2272503 : CollatzResearch.WordTrace tailWord_2272503 prefixEnd_2272503 1166886327784427555261455 := by
  unfold tailWord_2272503
  simp only [CollatzResearch.WordTrace]
  refine ⟨82884993686117218458286163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55256662457411478972190775 82884993686117218458286163)
  ·
    refine ⟨124327490529175827687429245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82884993686117218458286163 124327490529175827687429245)
    ·
      refine ⟨46622808948440935382785967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124327490529175827687429245 46622808948440935382785967)
      ·
        refine ⟨69934213422661403074178951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46622808948440935382785967 69934213422661403074178951)
        ·
          refine ⟨104901320133992104611268427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69934213422661403074178951 104901320133992104611268427)
          ·
            refine ⟨157351980200988156916902641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104901320133992104611268427 157351980200988156916902641)
            ·
              refine ⟨118013985150741117687676981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157351980200988156916902641 118013985150741117687676981)
              ·
                refine ⟨11063811107881979783219717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118013985150741117687676981 11063811107881979783219717)
                ·
                  refine ⟨2074464582727871209353697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11063811107881979783219717 2074464582727871209353697)
                  ·
                    refine ⟨1555848437045903407015273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2074464582727871209353697 1555848437045903407015273)
                    ·
                      refine ⟨1166886327784427555261455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555848437045903407015273 1166886327784427555261455)
                      ·
                        rfl

theorem cell23_2272503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 2, 2].length) (baseStart_2272503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272503 prefixEnd_2272503 := by exact prefixLift 2272503
  have htrace : WordTrace (prefixWord ++ tailWord_2272503) baseStart_2272503 baseEnd_2272503 := by
    simpa [prefixWord, tailWord_2272503, baseEnd_2272503] using wordTrace_append hprefix tailTrace_2272503
  have hstable : (prefixWord ++ tailWord_2272503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272503).length < 2 ^ (prefixWord ++ tailWord_2272503).sum := by decide
  have hdescent : baseEnd_2272503 < baseStart_2272503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272514 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_2272514 : Nat := 118140960795 + 2272514 * 2 ^ 59
def prefixEnd_2272514 : Nat := 4983230072969 + 3 ^ 40 * 2272514 * 2
def baseEnd_2272514 : Nat := 1166891976071627012223905

theorem tailTrace_2272514 : CollatzResearch.WordTrace tailWord_2272514 prefixEnd_2272514 1166891976071627012223905 := by
  unfold tailWord_2272514
  simp only [CollatzResearch.WordTrace]
  refine ⟨20721348722269341834234149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55256929926051578224624397 20721348722269341834234149)
  ·
    refine ⟨3885252885425501593918903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20721348722269341834234149 3885252885425501593918903)
    ·
      refine ⟨5827879328138252390878355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3885252885425501593918903 5827879328138252390878355)
      ·
        refine ⟨8741818992207378586317533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5827879328138252390878355 8741818992207378586317533)
        ·
          refine ⟨3278182122077766969869075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8741818992207378586317533 3278182122077766969869075)
          ·
            refine ⟨4917273183116650454803613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278182122077766969869075 4917273183116650454803613)
            ·
              refine ⟨1843977443668743920551355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4917273183116650454803613 1843977443668743920551355)
              ·
                refine ⟨2765966165503115880827033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843977443668743920551355 2765966165503115880827033)
                ·
                  refine ⟨2074474624127336910620275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2765966165503115880827033 2074474624127336910620275)
                  ·
                    refine ⟨3111711936191005365930413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2074474624127336910620275 3111711936191005365930413)
                    ·
                      refine ⟨1166891976071627012223905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3111711936191005365930413 1166891976071627012223905)
                      ·
                        rfl

theorem cell23_2272514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_2272514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272514 prefixEnd_2272514 := by exact prefixLift 2272514
  have htrace : WordTrace (prefixWord ++ tailWord_2272514) baseStart_2272514 baseEnd_2272514 := by
    simpa [prefixWord, tailWord_2272514, baseEnd_2272514] using wordTrace_append hprefix tailTrace_2272514
  have hstable : (prefixWord ++ tailWord_2272514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272514).length < 2 ^ (prefixWord ++ tailWord_2272514).sum := by decide
  have hdescent : baseEnd_2272514 < baseStart_2272514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272526 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_2272526 : Nat := 118140960795 + 2272526 * 2 ^ 59
def prefixEnd_2272526 : Nat := 4983230072969 + 3 ^ 40 * 2272526 * 2
def baseEnd_2272526 : Nat := 129655348648831218363761

theorem tailTrace_2272526 : CollatzResearch.WordTrace tailWord_2272526 prefixEnd_2272526 129655348648831218363761 := by
  unfold tailWord_2272526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10360729070629236673296679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55257221710022595590915621 10360729070629236673296679)
  ·
    refine ⟨15541093605943855009945019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10360729070629236673296679 15541093605943855009945019)
    ·
      refine ⟨23311640408915782514917529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15541093605943855009945019 23311640408915782514917529)
      ·
        refine ⟨17483730306686836886188147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23311640408915782514917529 17483730306686836886188147)
        ·
          refine ⟨26225595460030255329282221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17483730306686836886188147 26225595460030255329282221)
          ·
            refine ⟨9834598297511345748480833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26225595460030255329282221 9834598297511345748480833)
            ·
              refine ⟨7375948723133509311360625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9834598297511345748480833 7375948723133509311360625)
              ·
                refine ⟨5531961542350131983520469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7375948723133509311360625 5531961542350131983520469)
                ·
                  refine ⟨129655348648831218363761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5531961542350131983520469 129655348648831218363761)
                  ·
                    rfl

theorem cell23_2272526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_2272526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272526 prefixEnd_2272526 := by exact prefixLift 2272526
  have htrace : WordTrace (prefixWord ++ tailWord_2272526) baseStart_2272526 baseEnd_2272526 := by
    simpa [prefixWord, tailWord_2272526, baseEnd_2272526] using wordTrace_append hprefix tailTrace_2272526
  have hstable : (prefixWord ++ tailWord_2272526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272526).length < 2 ^ (prefixWord ++ tailWord_2272526).sum := by decide
  have hdescent : baseEnd_2272526 < baseStart_2272526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272576 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 4]
def baseStart_2272576 : Nat := 118140960795 + 2272576 * 2 ^ 59
def prefixEnd_2272576 : Nat := 4983230072969 + 3 ^ 40 * 2272576 * 2
def baseEnd_2272576 : Nat := 1166923811872205769648619

theorem tailTrace_2272576 : CollatzResearch.WordTrace tailWord_2272576 prefixEnd_2272576 1166923811872205769648619 := by
  unfold tailWord_2272576
  simp only [CollatzResearch.WordTrace]
  refine ⟨41443828107426375962846791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55258437476568501283795721 41443828107426375962846791)
  ·
    refine ⟨62165742161139563944270187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41443828107426375962846791 62165742161139563944270187)
    ·
      refine ⟨93248613241709345916405281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62165742161139563944270187 93248613241709345916405281)
      ·
        refine ⟨69936459931282009437303961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93248613241709345916405281 69936459931282009437303961)
        ·
          refine ⟨52452344948461507077977971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69936459931282009437303961 52452344948461507077977971)
          ·
            refine ⟨78678517422692260616966957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52452344948461507077977971 78678517422692260616966957)
            ·
              refine ⟨29504444033509597731362609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78678517422692260616966957 29504444033509597731362609)
              ·
                refine ⟨22128333025132198298521957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29504444033509597731362609 22128333025132198298521957)
                ·
                  refine ⟨4149062442212287180972867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22128333025132198298521957 4149062442212287180972867)
                  ·
                    refine ⟨6223593663318430771459301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4149062442212287180972867 6223593663318430771459301)
                    ·
                      refine ⟨1166923811872205769648619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6223593663318430771459301 1166923811872205769648619)
                      ·
                        rfl

theorem cell23_2272576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_2272576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272576 prefixEnd_2272576 := by exact prefixLift 2272576
  have htrace : WordTrace (prefixWord ++ tailWord_2272576) baseStart_2272576 baseEnd_2272576 := by
    simpa [prefixWord, tailWord_2272576, baseEnd_2272576] using wordTrace_append hprefix tailTrace_2272576
  have hstable : (prefixWord ++ tailWord_2272576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272576).length < 2 ^ (prefixWord ++ tailWord_2272576).sum := by decide
  have hdescent : baseEnd_2272576 < baseStart_2272576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272593 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 4]
def baseStart_2272593 : Nat := 118140960795 + 2272593 * 2 ^ 59
def prefixEnd_2272593 : Nat := 4983230072969 + 3 ^ 40 * 2272593 * 2
def baseEnd_2272593 : Nat := 1166932541043332203136041

theorem tailTrace_2272593 : CollatzResearch.WordTrace tailWord_2272593 prefixEnd_2272593 1166932541043332203136041 := by
  unfold tailWord_2272593
  simp only [CollatzResearch.WordTrace]
  refine ⟨82888276255791163829062433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55258850837194109219374955 82888276255791163829062433)
  ·
    refine ⟨62166207191843372871796825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82888276255791163829062433 62166207191843372871796825)
    ·
      refine ⟨46624655393882529653847619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62166207191843372871796825 46624655393882529653847619)
      ·
        refine ⟨69936983090823794480771429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46624655393882529653847619 69936983090823794480771429)
        ·
          refine ⟨13113184329529461465144643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69936983090823794480771429 13113184329529461465144643)
          ·
            refine ⟨19669776494294192197716965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13113184329529461465144643 19669776494294192197716965)
            ·
              refine ⟨3688083092680161037071931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19669776494294192197716965 3688083092680161037071931)
              ·
                refine ⟨5532124639020241555607897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3688083092680161037071931 5532124639020241555607897)
                ·
                  refine ⟨4149093479265181166705923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5532124639020241555607897 4149093479265181166705923)
                  ·
                    refine ⟨6223640218897771750058885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4149093479265181166705923 6223640218897771750058885)
                    ·
                      refine ⟨1166932541043332203136041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6223640218897771750058885 1166932541043332203136041)
                      ·
                        rfl

theorem cell23_2272593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_2272593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272593 prefixEnd_2272593 := by exact prefixLift 2272593
  have htrace : WordTrace (prefixWord ++ tailWord_2272593) baseStart_2272593 baseEnd_2272593 := by
    simpa [prefixWord, tailWord_2272593, baseEnd_2272593] using wordTrace_append hprefix tailTrace_2272593
  have hstable : (prefixWord ++ tailWord_2272593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272593).length < 2 ^ (prefixWord ++ tailWord_2272593).sum := by decide
  have hdescent : baseEnd_2272593 < baseStart_2272593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272610 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_2272610 : Nat := 118140960795 + 2272610 * 2 ^ 59
def prefixEnd_2272610 : Nat := 4983230072969 + 3 ^ 40 * 2272610 * 2
def baseEnd_2272610 : Nat := 1166941270214458636623463

theorem tailTrace_2272610 : CollatzResearch.WordTrace tailWord_2272610 prefixEnd_2272610 1166941270214458636623463 := by
  unfold tailWord_2272610
  simp only [CollatzResearch.WordTrace]
  refine ⟨20722224074182393933107821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55259264197819717154954189 20722224074182393933107821)
  ·
    refine ⟨7770834027818397724915433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20722224074182393933107821 7770834027818397724915433)
    ·
      refine ⟨5828125520863798293686575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7770834027818397724915433 5828125520863798293686575)
      ·
        refine ⟨8742188281295697440529863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5828125520863798293686575 8742188281295697440529863)
        ·
          refine ⟨13113282421943546160794795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8742188281295697440529863 13113282421943546160794795)
          ·
            refine ⟨19669923632915319241192193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13113282421943546160794795 19669923632915319241192193)
            ·
              refine ⟨14752442724686489430894145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19669923632915319241192193 14752442724686489430894145)
              ·
                refine ⟨11064332043514867073170609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14752442724686489430894145 11064332043514867073170609)
                ·
                  refine ⟨8298249032636150304877957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11064332043514867073170609 8298249032636150304877957)
                  ·
                    refine ⟨1555921693619278182164617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8298249032636150304877957 1555921693619278182164617)
                    ·
                      refine ⟨1166941270214458636623463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1555921693619278182164617 1166941270214458636623463)
                      ·
                        rfl

theorem cell23_2272610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_2272610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272610 prefixEnd_2272610 := by exact prefixLift 2272610
  have htrace : WordTrace (prefixWord ++ tailWord_2272610) baseStart_2272610 baseEnd_2272610 := by
    simpa [prefixWord, tailWord_2272610, baseEnd_2272610] using wordTrace_append hprefix tailTrace_2272610
  have hstable : (prefixWord ++ tailWord_2272610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272610).length < 2 ^ (prefixWord ++ tailWord_2272610).sum := by decide
  have hdescent : baseEnd_2272610 < baseStart_2272610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272613 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 2, 2, 3]
def baseStart_2272613 : Nat := 118140960795 + 2272613 * 2 ^ 59
def prefixEnd_2272613 : Nat := 4983230072969 + 3 ^ 40 * 2272613 * 2
def baseEnd_2272613 : Nat := 1166942810656422124885949

theorem tailTrace_2272613 : CollatzResearch.WordTrace tailWord_2272613 prefixEnd_2272613 1166942810656422124885949 := by
  unfold tailWord_2272613
  simp only [CollatzResearch.WordTrace]
  refine ⟨82889005715718707244790493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55259337143812471496526995 82889005715718707244790493)
  ·
    refine ⟨31083377143394515216796435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82889005715718707244790493 31083377143394515216796435)
    ·
      refine ⟨46625065715091772825194653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31083377143394515216796435 46625065715091772825194653)
      ·
        refine ⟨17484399643159414809447995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46625065715091772825194653 17484399643159414809447995)
        ·
          refine ⟨26226599464739122214171993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17484399643159414809447995 26226599464739122214171993)
          ·
            refine ⟨19669949598554341660628995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26226599464739122214171993 19669949598554341660628995)
            ·
              refine ⟨29504924397831512490943493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19669949598554341660628995 29504924397831512490943493)
              ·
                refine ⟨5532173324593408592051905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29504924397831512490943493 5532173324593408592051905)
                ·
                  refine ⟨4149129993445056444038929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5532173324593408592051905 4149129993445056444038929)
                  ·
                    refine ⟨3111847495083792333029197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4149129993445056444038929 3111847495083792333029197)
                    ·
                      refine ⟨1166942810656422124885949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3111847495083792333029197 1166942810656422124885949)
                      ·
                        rfl

theorem cell23_2272613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_2272613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272613 prefixEnd_2272613 := by exact prefixLift 2272613
  have htrace : WordTrace (prefixWord ++ tailWord_2272613) baseStart_2272613 baseEnd_2272613 := by
    simpa [prefixWord, tailWord_2272613, baseEnd_2272613] using wordTrace_append hprefix tailTrace_2272613
  have hstable : (prefixWord ++ tailWord_2272613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272613).length < 2 ^ (prefixWord ++ tailWord_2272613).sum := by decide
  have hdescent : baseEnd_2272613 < baseStart_2272613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272654 : List Nat := [4, 1, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_2272654 : Nat := 118140960795 + 2272654 * 2 ^ 59
def prefixEnd_2272654 : Nat := 4983230072969 + 3 ^ 40 * 2272654 * 2
def baseEnd_2272654 : Nat := 388987954454418821491087

theorem tailTrace_2272654 : CollatzResearch.WordTrace tailWord_2272654 prefixEnd_2272654 388987954454418821491087 := by
  unfold tailWord_2272654
  simp only [CollatzResearch.WordTrace]
  refine ⟨10361312638571271405879127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55260334072380114164688677 10361312638571271405879127)
  ·
    refine ⟨15541968957856907108818691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10361312638571271405879127 15541968957856907108818691)
    ·
      refine ⟨23312953436785360663228037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15541968957856907108818691 23312953436785360663228037)
      ·
        refine ⟨4371178769397255124355257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23312953436785360663228037 4371178769397255124355257)
        ·
          refine ⟨3278384077047941343266443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4371178769397255124355257 3278384077047941343266443)
          ·
            refine ⟨4917576115571912014899665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278384077047941343266443 4917576115571912014899665)
            ·
              refine ⟨3688182086678934011174749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4917576115571912014899665 3688182086678934011174749)
              ·
                refine ⟨1383068282504600254190531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3688182086678934011174749 1383068282504600254190531)
                ·
                  refine ⟨2074602423756900381285797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383068282504600254190531 2074602423756900381285797)
                  ·
                    refine ⟨388987954454418821491087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2074602423756900381285797 388987954454418821491087)
                    ·
                      rfl

theorem cell23_2272654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_2272654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272654 prefixEnd_2272654 := by exact prefixLift 2272654
  have htrace : WordTrace (prefixWord ++ tailWord_2272654) baseStart_2272654 baseEnd_2272654 := by
    simpa [prefixWord, tailWord_2272654, baseEnd_2272654] using wordTrace_append hprefix tailTrace_2272654
  have hstable : (prefixWord ++ tailWord_2272654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272654).length < 2 ^ (prefixWord ++ tailWord_2272654).sum := by decide
  have hdescent : baseEnd_2272654 < baseStart_2272654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272703 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 3]
def baseStart_2272703 : Nat := 118140960795 + 2272703 * 2 ^ 59
def prefixEnd_2272703 : Nat := 4983230072969 + 3 ^ 40 * 2272703 * 2
def baseEnd_2272703 : Nat := 1166989023915326772760535

theorem tailTrace_2272703 : CollatzResearch.WordTrace tailWord_2272703 prefixEnd_2272703 1166989023915326772760535 := by
  unfold tailWord_2272703
  simp only [CollatzResearch.WordTrace]
  refine ⟨82892288285392652615566763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55261525523595101743711175 82892288285392652615566763)
  ·
    refine ⟨124338432428088978923350145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82892288285392652615566763 124338432428088978923350145)
    ·
      refine ⟨93253824321066734192512609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124338432428088978923350145 93253824321066734192512609)
      ·
        refine ⟨69940368240800050644384457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93253824321066734192512609 69940368240800050644384457)
        ·
          refine ⟨52455276180600037983288343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69940368240800050644384457 52455276180600037983288343)
          ·
            refine ⟨78682914270900056974932515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52455276180600037983288343 78682914270900056974932515)
            ·
              refine ⟨118024371406350085462398773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78682914270900056974932515 118024371406350085462398773)
              ·
                refine ⟨11064784819345320512099885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118024371406350085462398773 11064784819345320512099885)
                ·
                  refine ⟨4149294307254495192037457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11064784819345320512099885 4149294307254495192037457)
                  ·
                    refine ⟨3111970730440871394028093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4149294307254495192037457 3111970730440871394028093)
                    ·
                      refine ⟨1166989023915326772760535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3111970730440871394028093 1166989023915326772760535)
                      ·
                        rfl

theorem cell23_2272703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_2272703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272703 prefixEnd_2272703 := by exact prefixLift 2272703
  have htrace : WordTrace (prefixWord ++ tailWord_2272703) baseStart_2272703 baseEnd_2272703 := by
    simpa [prefixWord, tailWord_2272703, baseEnd_2272703] using wordTrace_append hprefix tailTrace_2272703
  have hstable : (prefixWord ++ tailWord_2272703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272703).length < 2 ^ (prefixWord ++ tailWord_2272703).sum := by decide
  have hdescent : baseEnd_2272703 < baseStart_2272703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272750 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_2272750 : Nat := 118140960795 + 2272750 * 2 ^ 59
def prefixEnd_2272750 : Nat := 4983230072969 + 3 ^ 40 * 2272750 * 2
def baseEnd_2272750 : Nat := 1167013157506088088872819

theorem tailTrace_2272750 : CollatzResearch.WordTrace tailWord_2272750 prefixEnd_2272750 1167013157506088088872819 := by
  unfold tailWord_2272750
  simp only [CollatzResearch.WordTrace]
  refine ⟨10361750314527797455315963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55262668344148253095018469 10361750314527797455315963)
  ·
    refine ⟨15542625471791696182973945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10361750314527797455315963 15542625471791696182973945)
    ·
      refine ⟨11656969103843772137230459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15542625471791696182973945 11656969103843772137230459)
      ·
        refine ⟨17485453655765658205845689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11656969103843772137230459 17485453655765658205845689)
        ·
          refine ⟨13114090241824243654384267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17485453655765658205845689 13114090241824243654384267)
          ·
            refine ⟨19671135362736365481576401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13114090241824243654384267 19671135362736365481576401)
            ·
              refine ⟨14753351522052274111182301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19671135362736365481576401 14753351522052274111182301)
              ·
                refine ⟨5532506820769602791693363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14753351522052274111182301 5532506820769602791693363)
                ·
                  refine ⟨8298760231154404187540045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5532506820769602791693363 8298760231154404187540045)
                  ·
                    refine ⟨3112035086682901570327517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8298760231154404187540045 3112035086682901570327517)
                    ·
                      refine ⟨1167013157506088088872819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3112035086682901570327517 1167013157506088088872819)
                      ·
                        rfl

theorem cell23_2272750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_2272750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272750 prefixEnd_2272750 := by exact prefixLift 2272750
  have htrace : WordTrace (prefixWord ++ tailWord_2272750) baseStart_2272750 baseEnd_2272750 := by
    simpa [prefixWord, tailWord_2272750, baseEnd_2272750] using wordTrace_append hprefix tailTrace_2272750
  have hstable : (prefixWord ++ tailWord_2272750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272750).length < 2 ^ (prefixWord ++ tailWord_2272750).sum := by decide
  have hdescent : baseEnd_2272750 < baseStart_2272750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272754 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2272754 : Nat := 118140960795 + 2272754 * 2 ^ 59
def prefixEnd_2272754 : Nat := 4983230072969 + 3 ^ 40 * 2272754 * 2
def baseEnd_2272754 : Nat := 1167015211428706073222801

theorem tailTrace_2272754 : CollatzResearch.WordTrace tailWord_2272754 prefixEnd_2272754 1167015211428706073222801 := by
  unfold tailWord_2272754
  simp only [CollatzResearch.WordTrace]
  refine ⟨20723537102051972081418329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55262765605471925550448877 20723537102051972081418329)
  ·
    refine ⟨15542652826538979061063747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20723537102051972081418329 15542652826538979061063747)
    ·
      refine ⟨23313979239808468591595621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15542652826538979061063747 23313979239808468591595621)
      ·
        refine ⟨4371371107464087860924179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23313979239808468591595621 4371371107464087860924179)
        ·
          refine ⟨6557056661196131791386269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4371371107464087860924179 6557056661196131791386269)
          ·
            refine ⟨2458896247948549421769851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6557056661196131791386269 2458896247948549421769851)
            ·
              refine ⟨3688344371922824132654777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458896247948549421769851 3688344371922824132654777)
              ·
                refine ⟨2766258278942118099491083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3688344371922824132654777 2766258278942118099491083)
                ·
                  refine ⟨4149387418413177149236625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766258278942118099491083 4149387418413177149236625)
                  ·
                    refine ⟨3112040563809882861927469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4149387418413177149236625 3112040563809882861927469)
                    ·
                      refine ⟨1167015211428706073222801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3112040563809882861927469 1167015211428706073222801)
                      ·
                        rfl

theorem cell23_2272754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2272754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272754 prefixEnd_2272754 := by exact prefixLift 2272754
  have htrace : WordTrace (prefixWord ++ tailWord_2272754) baseStart_2272754 baseEnd_2272754 := by
    simpa [prefixWord, tailWord_2272754, baseEnd_2272754] using wordTrace_append hprefix tailTrace_2272754
  have hstable : (prefixWord ++ tailWord_2272754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272754).length < 2 ^ (prefixWord ++ tailWord_2272754).sum := by decide
  have hdescent : baseEnd_2272754 < baseStart_2272754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272774 : List Nat := [6, 2, 1, 1, 3, 10]
def baseStart_2272774 : Nat := 118140960795 + 2272774 * 2 ^ 59
def prefixEnd_2272774 : Nat := 4983230072969 + 3 ^ 40 * 2272774 * 2
def baseEnd_2272774 : Nat := 4802573996056773641863

theorem tailTrace_2272774 : CollatzResearch.WordTrace tailWord_2272774 prefixEnd_2272774 4802573996056773641863 := by
  unfold tailWord_2272774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590464933379232241918793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55263251912090287827600917 2590464933379232241918793)
  ·
    refine ⟨1942848700034424181439095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2590464933379232241918793 1942848700034424181439095)
    ·
      refine ⟨2914273050051636272158643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942848700034424181439095 2914273050051636272158643)
      ·
        refine ⟨4371409575077454408237965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914273050051636272158643 4371409575077454408237965)
        ·
          refine ⟨1639278590654045403089237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4371409575077454408237965 1639278590654045403089237)
          ·
            refine ⟨4802573996056773641863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1639278590654045403089237 4802573996056773641863)
            ·
              rfl

theorem cell23_2272774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 10].length) (baseStart_2272774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272774 prefixEnd_2272774 := by exact prefixLift 2272774
  have htrace : WordTrace (prefixWord ++ tailWord_2272774) baseStart_2272774 baseEnd_2272774 := by
    simpa [prefixWord, tailWord_2272774, baseEnd_2272774] using wordTrace_append hprefix tailTrace_2272774
  have hstable : (prefixWord ++ tailWord_2272774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272774).length < 2 ^ (prefixWord ++ tailWord_2272774).sum := by decide
  have hdescent : baseEnd_2272774 < baseStart_2272774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272800 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 2, 6]
def baseStart_2272800 : Nat := 118140960795 + 2272800 * 2 ^ 59
def prefixEnd_2272800 : Nat := 4983230072969 + 3 ^ 40 * 2272800 * 2
def baseEnd_2272800 : Nat := 389012943846270964415863

theorem tailTrace_2272800 : CollatzResearch.WordTrace tailWord_2272800 prefixEnd_2272800 389012943846270964415863 := by
  unfold tailWord_2272800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41447913083020619090923927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55263884110694158787898569 41447913083020619090923927)
  ·
    refine ⟨62171869624530928636385891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41447913083020619090923927 62171869624530928636385891)
    ·
      refine ⟨93257804436796392954578837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62171869624530928636385891 93257804436796392954578837)
      ·
        refine ⟨4371459582974830919745883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93257804436796392954578837 4371459582974830919745883)
        ·
          refine ⟨6557189374462246379618825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4371459582974830919745883 6557189374462246379618825)
          ·
            refine ⟨4917892030846684784714119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6557189374462246379618825 4917892030846684784714119)
            ·
              refine ⟨7376838046270027177071179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4917892030846684784714119 7376838046270027177071179)
              ·
                refine ⟨11065257069405040765606769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7376838046270027177071179 11065257069405040765606769)
                ·
                  refine ⟨8298942802053780574205077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11065257069405040765606769 8298942802053780574205077)
                  ·
                    refine ⟨389012943846270964415863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8298942802053780574205077 389012943846270964415863)
                    ·
                      rfl

theorem cell23_2272800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_2272800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272800 prefixEnd_2272800 := by exact prefixLift 2272800
  have htrace : WordTrace (prefixWord ++ tailWord_2272800) baseStart_2272800 baseEnd_2272800 := by
    simpa [prefixWord, tailWord_2272800, baseEnd_2272800] using wordTrace_append hprefix tailTrace_2272800
  have hstable : (prefixWord ++ tailWord_2272800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272800).length < 2 ^ (prefixWord ++ tailWord_2272800).sum := by decide
  have hdescent : baseEnd_2272800 < baseStart_2272800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272810 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2272810 : Nat := 118140960795 + 2272810 * 2 ^ 59
def prefixEnd_2272810 : Nat := 4983230072969 + 3 ^ 40 * 2272810 * 2
def baseEnd_2272810 : Nat := 1167043966345357854122543

theorem tailTrace_2272810 : CollatzResearch.WordTrace tailWord_2272810 prefixEnd_2272810 1167043966345357854122543 := by
  unfold tailWord_2272810
  simp only [CollatzResearch.WordTrace]
  refine ⟨20724047724001252472427971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55264127264003339926474589 20724047724001252472427971)
  ·
    refine ⟨31086071586001878708641957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20724047724001252472427971 31086071586001878708641957)
    ·
      refine ⟨5828638422375352257870367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31086071586001878708641957 5828638422375352257870367)
      ·
        refine ⟨8742957633563028386805551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5828638422375352257870367 8742957633563028386805551)
        ·
          refine ⟨13114436450344542580208327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8742957633563028386805551 13114436450344542580208327)
          ·
            refine ⟨19671654675516813870312491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13114436450344542580208327 19671654675516813870312491)
            ·
              refine ⟨29507482013275220805468737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19671654675516813870312491 29507482013275220805468737)
              ·
                refine ⟨22130611509956415604101553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29507482013275220805468737 22130611509956415604101553)
                ·
                  refine ⟨16597958632467311703076165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22130611509956415604101553 16597958632467311703076165)
                  ·
                    refine ⟨3112117243587620944326781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16597958632467311703076165 3112117243587620944326781)
                    ·
                      refine ⟨1167043966345357854122543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3112117243587620944326781 1167043966345357854122543)
                      ·
                        rfl

theorem cell23_2272810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2272810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272810 prefixEnd_2272810 := by exact prefixLift 2272810
  have htrace : WordTrace (prefixWord ++ tailWord_2272810) baseStart_2272810 baseEnd_2272810 := by
    simpa [prefixWord, tailWord_2272810, baseEnd_2272810] using wordTrace_append hprefix tailTrace_2272810
  have hstable : (prefixWord ++ tailWord_2272810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272810).length < 2 ^ (prefixWord ++ tailWord_2272810).sum := by decide
  have hdescent : baseEnd_2272810 < baseStart_2272810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272828 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 1, 3, 2]
def baseStart_2272828 : Nat := 118140960795 + 2272828 * 2 ^ 59
def prefixEnd_2272828 : Nat := 4983230072969 + 3 ^ 40 * 2272828 * 2
def baseEnd_2272828 : Nat := 1167053208997138783697461

theorem tailTrace_2272828 : CollatzResearch.WordTrace tailWord_2272828 prefixEnd_2272828 1167053208997138783697461 := by
  unfold tailWord_2272828
  simp only [CollatzResearch.WordTrace]
  refine ⟨41448423704969899481933569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55264564939959865975911425 41448423704969899481933569)
  ·
    refine ⟨31086317778727424611450177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41448423704969899481933569 31086317778727424611450177)
    ·
      refine ⟨23314738334045568458587633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31086317778727424611450177 23314738334045568458587633)
      ·
        refine ⟨17486053750534176343940725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23314738334045568458587633 17486053750534176343940725)
        ·
          refine ⟨1639317539112579032244443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17486053750534176343940725 1639317539112579032244443)
          ·
            refine ⟨2458976308668868548366665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639317539112579032244443 2458976308668868548366665)
            ·
              refine ⟨1844232231501651411274999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2458976308668868548366665 1844232231501651411274999)
              ·
                refine ⟨2766348347252477116912499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844232231501651411274999 2766348347252477116912499)
                ·
                  refine ⟨4149522520878715675368749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766348347252477116912499 4149522520878715675368749)
                  ·
                    refine ⟨1556070945329518378263281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4149522520878715675368749 1556070945329518378263281)
                    ·
                      refine ⟨1167053208997138783697461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1556070945329518378263281 1167053208997138783697461)
                      ·
                        rfl

theorem cell23_2272828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_2272828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272828 prefixEnd_2272828 := by exact prefixLift 2272828
  have htrace : WordTrace (prefixWord ++ tailWord_2272828) baseStart_2272828 baseEnd_2272828 := by
    simpa [prefixWord, tailWord_2272828, baseEnd_2272828] using wordTrace_append hprefix tailTrace_2272828
  have hstable : (prefixWord ++ tailWord_2272828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272828).length < 2 ^ (prefixWord ++ tailWord_2272828).sum := by decide
  have hdescent : baseEnd_2272828 < baseStart_2272828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272843 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 4, 5]
def baseStart_2272843 : Nat := 118140960795 + 2272843 * 2 ^ 59
def prefixEnd_2272843 : Nat := 4983230072969 + 3 ^ 40 * 2272843 * 2
def baseEnd_2272843 : Nat := 389020303735652075003297

theorem tailTrace_2272843 : CollatzResearch.WordTrace tailWord_2272843 prefixEnd_2272843 389020303735652075003297 := by
  unfold tailWord_2272843
  simp only [CollatzResearch.WordTrace]
  refine ⟨82897394504885456525663183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55264929669923637683775455 82897394504885456525663183)
  ·
    refine ⟨124346091757328184788494775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82897394504885456525663183 124346091757328184788494775)
    ·
      refine ⟨186519137635992277182742163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124346091757328184788494775 186519137635992277182742163)
      ·
        refine ⟨279778706453988415774113245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186519137635992277182742163 279778706453988415774113245)
        ·
          refine ⟨104917014920245655915292467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 279778706453988415774113245 104917014920245655915292467)
          ·
            refine ⟨157375522380368483872938701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104917014920245655915292467 157375522380368483872938701)
            ·
              refine ⟨59015820892638181452352013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157375522380368483872938701 59015820892638181452352013)
              ·
                refine ⟨22130932834739318044632005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59015820892638181452352013 22130932834739318044632005)
                ·
                  refine ⟨4149549906513622133368501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22130932834739318044632005 4149549906513622133368501)
                  ·
                    refine ⟨389020303735652075003297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4149549906513622133368501 389020303735652075003297)
                    ·
                      rfl

theorem cell23_2272843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 5].length) (baseStart_2272843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272843 prefixEnd_2272843 := by exact prefixLift 2272843
  have htrace : WordTrace (prefixWord ++ tailWord_2272843) baseStart_2272843 baseEnd_2272843 := by
    simpa [prefixWord, tailWord_2272843, baseEnd_2272843] using wordTrace_append hprefix tailTrace_2272843
  have hstable : (prefixWord ++ tailWord_2272843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272843).length < 2 ^ (prefixWord ++ tailWord_2272843).sum := by decide
  have hdescent : baseEnd_2272843 < baseStart_2272843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272853 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2272853 : Nat := 118140960795 + 2272853 * 2 ^ 59
def prefixEnd_2272853 : Nat := 4983230072969 + 3 ^ 40 * 2272853 * 2
def baseEnd_2272853 : Nat := 1167066046013501185884845

theorem tailTrace_2272853 : CollatzResearch.WordTrace tailWord_2272853 prefixEnd_2272853 1167066046013501185884845 := by
  unfold tailWord_2272853
  simp only [CollatzResearch.WordTrace]
  refine ⟨82897759234849228233527213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55265172823232818822351475 82897759234849228233527213)
  ·
    refine ⟨31086659713068460587572705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82897759234849228233527213 31086659713068460587572705)
    ·
      refine ⟨23314994784801345440679529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31086659713068460587572705 23314994784801345440679529)
      ·
        refine ⟨17486246088601009080509647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23314994784801345440679529 17486246088601009080509647)
        ·
          refine ⟨26229369132901513620764471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17486246088601009080509647 26229369132901513620764471)
          ·
            refine ⟨39344053699352270431146707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26229369132901513620764471 39344053699352270431146707)
            ·
              refine ⟨59016080549028405646720061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39344053699352270431146707 59016080549028405646720061)
              ·
                refine ⟨22131030205885652117520023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59016080549028405646720061 22131030205885652117520023)
                ·
                  refine ⟨33196545308828478176280035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22131030205885652117520023 33196545308828478176280035)
                  ·
                    refine ⟨49794817963242717264420053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33196545308828478176280035 49794817963242717264420053)
                    ·
                      refine ⟨1167066046013501185884845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49794817963242717264420053 1167066046013501185884845)
                      ·
                        rfl

theorem cell23_2272853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2272853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272853 prefixEnd_2272853 := by exact prefixLift 2272853
  have htrace : WordTrace (prefixWord ++ tailWord_2272853) baseStart_2272853 baseEnd_2272853 := by
    simpa [prefixWord, tailWord_2272853, baseEnd_2272853] using wordTrace_append hprefix tailTrace_2272853
  have hstable : (prefixWord ++ tailWord_2272853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272853).length < 2 ^ (prefixWord ++ tailWord_2272853).sum := by decide
  have hdescent : baseEnd_2272853 < baseStart_2272853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272860 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2272860 : Nat := 118140960795 + 2272860 * 2 ^ 59
def prefixEnd_2272860 : Nat := 4983230072969 + 3 ^ 40 * 2272860 * 2
def baseEnd_2272860 : Nat := 389023213459360886165771

theorem tailTrace_2272860 : CollatzResearch.WordTrace tailWord_2272860 prefixEnd_2272860 389023213459360886165771 := by
  unfold tailWord_2272860
  simp only [CollatzResearch.WordTrace]
  refine ⟨41449007272911934214516017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55265343030549245619354689 41449007272911934214516017)
  ·
    refine ⟨31086755454683950660887013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41449007272911934214516017 31086755454683950660887013)
    ·
      refine ⟨5828766647753240748916315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31086755454683950660887013 5828766647753240748916315)
      ·
        refine ⟨8743149971629861123374473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5828766647753240748916315 8743149971629861123374473)
        ·
          refine ⟨6557362478722395842530855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8743149971629861123374473 6557362478722395842530855)
          ·
            refine ⟨9836043718083593763796283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6557362478722395842530855 9836043718083593763796283)
            ·
              refine ⟨14754065577125390645694425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9836043718083593763796283 14754065577125390645694425)
              ·
                refine ⟨11065549182844042984270819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14754065577125390645694425 11065549182844042984270819)
                ·
                  refine ⟨16598323774266064476406229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11065549182844042984270819 16598323774266064476406229)
                  ·
                    refine ⟨389023213459360886165771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16598323774266064476406229 389023213459360886165771)
                    ·
                      rfl

theorem cell23_2272860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2272860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272860 prefixEnd_2272860 := by exact prefixLift 2272860
  have htrace : WordTrace (prefixWord ++ tailWord_2272860) baseStart_2272860 baseEnd_2272860 := by
    simpa [prefixWord, tailWord_2272860, baseEnd_2272860] using wordTrace_append hprefix tailTrace_2272860
  have hstable : (prefixWord ++ tailWord_2272860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272860).length < 2 ^ (prefixWord ++ tailWord_2272860).sum := by decide
  have hdescent : baseEnd_2272860 < baseStart_2272860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272880 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 4]
def baseStart_2272880 : Nat := 118140960795 + 2272880 * 2 ^ 59
def prefixEnd_2272880 : Nat := 4983230072969 + 3 ^ 40 * 2272880 * 2
def baseEnd_2272880 : Nat := 1167079909991172580247221

theorem tailTrace_2272880 : CollatzResearch.WordTrace tailWord_2272880 prefixEnd_2272880 1167079909991172580247221 := by
  unfold tailWord_2272880
  simp only [CollatzResearch.WordTrace]
  refine ⟨41449372002875705922380047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55265829337167607896506729 41449372002875705922380047)
  ·
    refine ⟨62174058004313558883570071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41449372002875705922380047 62174058004313558883570071)
    ·
      refine ⟨93261087006470338325355107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62174058004313558883570071 93261087006470338325355107)
      ·
        refine ⟨139891630509705507488032661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93261087006470338325355107 139891630509705507488032661)
        ·
          refine ⟨6557420180142445663501531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139891630509705507488032661 6557420180142445663501531)
          ·
            refine ⟨9836130270213668495252297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6557420180142445663501531 9836130270213668495252297)
            ·
              refine ⟨7377097702660251371439223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9836130270213668495252297 7377097702660251371439223)
              ·
                refine ⟨11065646553990377057158835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7377097702660251371439223 11065646553990377057158835)
                ·
                  refine ⟨16598469830985565585738253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11065646553990377057158835 16598469830985565585738253)
                  ·
                    refine ⟨6224426186619587094651845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16598469830985565585738253 6224426186619587094651845)
                    ·
                      refine ⟨1167079909991172580247221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6224426186619587094651845 1167079909991172580247221)
                      ·
                        rfl

theorem cell23_2272880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_2272880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272880 prefixEnd_2272880 := by exact prefixLift 2272880
  have htrace : WordTrace (prefixWord ++ tailWord_2272880) baseStart_2272880 baseEnd_2272880 := by
    simpa [prefixWord, tailWord_2272880, baseEnd_2272880] using wordTrace_append hprefix tailTrace_2272880
  have hstable : (prefixWord ++ tailWord_2272880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272880).length < 2 ^ (prefixWord ++ tailWord_2272880).sum := by decide
  have hdescent : baseEnd_2272880 < baseStart_2272880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272897 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_2272897 : Nat := 118140960795 + 2272897 * 2 ^ 59
def prefixEnd_2272897 : Nat := 4983230072969 + 3 ^ 40 * 2272897 * 2
def baseEnd_2272897 : Nat := 1167088639162299013734643

theorem tailTrace_2272897 : CollatzResearch.WordTrace tailWord_2272897 prefixEnd_2272897 1167088639162299013734643 := by
  unfold tailWord_2272897
  simp only [CollatzResearch.WordTrace]
  refine ⟨82899364046689823748128945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55266242697793215832085963 82899364046689823748128945)
  ·
    refine ⟨62174523035017367811096709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82899364046689823748128945 62174523035017367811096709)
    ·
      refine ⟨11657723069065756464580633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62174523035017367811096709 11657723069065756464580633)
      ·
        refine ⟨8743292301799317348435475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11657723069065756464580633 8743292301799317348435475)
        ·
          refine ⟨13114938452698976022653213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8743292301799317348435475 13114938452698976022653213)
          ·
            refine ⟨4918101919762116008494955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13114938452698976022653213 4918101919762116008494955)
            ·
              refine ⟨7377152879643174012742433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918101919762116008494955 7377152879643174012742433)
              ·
                refine ⟨5532864659732380509556825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7377152879643174012742433 5532864659732380509556825)
                ·
                  refine ⟨4149648494799285382167619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5532864659732380509556825 4149648494799285382167619)
                  ·
                    refine ⟨6224472742198928073251429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4149648494799285382167619 6224472742198928073251429)
                    ·
                      refine ⟨1167088639162299013734643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6224472742198928073251429 1167088639162299013734643)
                      ·
                        rfl

theorem cell23_2272897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_2272897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272897 prefixEnd_2272897 := by exact prefixLift 2272897
  have htrace : WordTrace (prefixWord ++ tailWord_2272897) baseStart_2272897 baseEnd_2272897 := by
    simpa [prefixWord, tailWord_2272897, baseEnd_2272897] using wordTrace_append hprefix tailTrace_2272897
  have hstable : (prefixWord ++ tailWord_2272897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272897).length < 2 ^ (prefixWord ++ tailWord_2272897).sum := by decide
  have hdescent : baseEnd_2272897 < baseStart_2272897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272958 : List Nat := [4, 2, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_2272958 : Nat := 118140960795 + 2272958 * 2 ^ 59
def prefixEnd_2272958 : Nat := 4983230072969 + 3 ^ 40 * 2272958 * 2
def baseEnd_2272958 : Nat := 389039987160741091690621

theorem tailTrace_2272958 : CollatzResearch.WordTrace tailWord_2272958 prefixEnd_2272958 389039987160741091690621 := by
  unfold tailWord_2272958
  simp only [CollatzResearch.WordTrace]
  refine ⟨10362698612433603895762441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55267725932979220777399685 10362698612433603895762441)
  ·
    refine ⟨7772023959325202921821831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10362698612433603895762441 7772023959325202921821831)
    ·
      refine ⟨11658035938987804382732747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7772023959325202921821831 11658035938987804382732747)
      ·
        refine ⟨17487053908481706574099121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11658035938987804382732747 17487053908481706574099121)
        ·
          refine ⟨13115290431361279930574341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17487053908481706574099121 13115290431361279930574341)
          ·
            refine ⟨2459116955880239986982689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13115290431361279930574341 2459116955880239986982689)
            ·
              refine ⟨1844337716910179990237017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2459116955880239986982689 1844337716910179990237017)
              ·
                refine ⟨1383253287682634992677763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1844337716910179990237017 1383253287682634992677763)
                ·
                  refine ⟨2074879931523952489016645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383253287682634992677763 2074879931523952489016645)
                  ·
                    refine ⟨389039987160741091690621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2074879931523952489016645 389039987160741091690621)
                    ·
                      rfl

theorem cell23_2272958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_2272958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272958 prefixEnd_2272958 := by exact prefixLift 2272958
  have htrace : WordTrace (prefixWord ++ tailWord_2272958) baseStart_2272958 baseEnd_2272958 := by
    simpa [prefixWord, tailWord_2272958, baseEnd_2272958] using wordTrace_append hprefix tailTrace_2272958
  have hstable : (prefixWord ++ tailWord_2272958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272958).length < 2 ^ (prefixWord ++ tailWord_2272958).sum := by decide
  have hdescent : baseEnd_2272958 < baseStart_2272958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272964 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_2272964 : Nat := 118140960795 + 2272964 * 2 ^ 59
def prefixEnd_2272964 : Nat := 4983230072969 + 3 ^ 40 * 2272964 * 2
def baseEnd_2272964 : Nat := 1167123042366150251596835

theorem tailTrace_2272964 : CollatzResearch.WordTrace tailWord_2272964 prefixEnd_2272964 1167123042366150251596835 := by
  unfold tailWord_2272964
  simp only [CollatzResearch.WordTrace]
  refine ⟨41450903868723547095408973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55267871824964729460545297 41450903868723547095408973)
  ·
    refine ⟨15544088950771330160778365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41450903868723547095408973 15544088950771330160778365)
    ·
      refine ⟨5829033356539248810291887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15544088950771330160778365 5829033356539248810291887)
      ·
        refine ⟨8743550034808873215437831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5829033356539248810291887 8743550034808873215437831)
        ·
          refine ⟨13115325052213309823156747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8743550034808873215437831 13115325052213309823156747)
          ·
            refine ⟨19672987578319964734735121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13115325052213309823156747 19672987578319964734735121)
            ·
              refine ⟨14754740683739973551051341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19672987578319964734735121 14754740683739973551051341)
              ·
                refine ⟨5533027756402490081644253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14754740683739973551051341 5533027756402490081644253)
                ·
                  refine ⟨2074885408650933780616595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5533027756402490081644253 2074885408650933780616595)
                  ·
                    refine ⟨3112328112976400670924893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2074885408650933780616595 3112328112976400670924893)
                    ·
                      refine ⟨1167123042366150251596835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3112328112976400670924893 1167123042366150251596835)
                      ·
                        rfl

theorem cell23_2272964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_2272964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272964 prefixEnd_2272964 := by exact prefixLift 2272964
  have htrace : WordTrace (prefixWord ++ tailWord_2272964) baseStart_2272964 baseEnd_2272964 := by
    simpa [prefixWord, tailWord_2272964, baseEnd_2272964] using wordTrace_append hprefix tailTrace_2272964
  have hstable : (prefixWord ++ tailWord_2272964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272964).length < 2 ^ (prefixWord ++ tailWord_2272964).sum := by decide
  have hdescent : baseEnd_2272964 < baseStart_2272964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272997 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 4, 4]
def baseStart_2272997 : Nat := 118140960795 + 2272997 * 2 ^ 59
def prefixEnd_2272997 : Nat := 4983230072969 + 3 ^ 40 * 2272997 * 2
def baseEnd_2272997 : Nat := 389046662409249540828061

theorem tailTrace_2272997 : CollatzResearch.WordTrace tailWord_2272997 prefixEnd_2272997 389046662409249540828061 := by
  unfold tailWord_2272997
  simp only [CollatzResearch.WordTrace]
  refine ⟨82903011346327540826769245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55268674230885027217846163 82903011346327540826769245)
  ·
    refine ⟨31088629254872827810038467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82903011346327540826769245 31088629254872827810038467)
    ·
      refine ⟨46632943882309241715057701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31088629254872827810038467 46632943882309241715057701)
      ·
        refine ⟨8743676977932982821573319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46632943882309241715057701 8743676977932982821573319)
        ·
          refine ⟨13115515466899474232359979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8743676977932982821573319 13115515466899474232359979)
          ·
            refine ⟨19673273200349211348539969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13115515466899474232359979 19673273200349211348539969)
            ·
              refine ⟨14754954900261908511404977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19673273200349211348539969 14754954900261908511404977)
              ·
                refine ⟨11066216175196431383553733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14754954900261908511404977 11066216175196431383553733)
                ·
                  refine ⟨2074915532849330884416325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11066216175196431383553733 2074915532849330884416325)
                  ·
                    refine ⟨389046662409249540828061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2074915532849330884416325 389046662409249540828061)
                    ·
                      rfl

theorem cell23_2272997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_2272997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2272997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2272997 prefixEnd_2272997 := by exact prefixLift 2272997
  have htrace : WordTrace (prefixWord ++ tailWord_2272997) baseStart_2272997 baseEnd_2272997 := by
    simpa [prefixWord, tailWord_2272997, baseEnd_2272997] using wordTrace_append hprefix tailTrace_2272997
  have hstable : (prefixWord ++ tailWord_2272997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272997).length < 2 ^ (prefixWord ++ tailWord_2272997).sum := by decide
  have hdescent : baseEnd_2272997 < baseStart_2272997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273004 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 4]
def baseStart_2273004 : Nat := 118140960795 + 2273004 * 2 ^ 59
def prefixEnd_2273004 : Nat := 4983230072969 + 3 ^ 40 * 2273004 * 2
def baseEnd_2273004 : Nat := 1167143581592330095096651

theorem tailTrace_2273004 : CollatzResearch.WordTrace tailWord_2273004 prefixEnd_2273004 1167143581592330095096651 := by
  unfold tailWord_2273004
  simp only [CollatzResearch.WordTrace]
  refine ⟨41451633328651090511137033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55268844438201454014849377 41451633328651090511137033)
  ·
    refine ⟨31088724996488317883352775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41451633328651090511137033 31088724996488317883352775)
    ·
      refine ⟨46633087494732476825029163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31088724996488317883352775 46633087494732476825029163)
      ·
        refine ⟨69949631242098715237543745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46633087494732476825029163 69949631242098715237543745)
        ·
          refine ⟨52462223431574036428157809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69949631242098715237543745 52462223431574036428157809)
          ·
            refine ⟨39346667573680527321118357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52462223431574036428157809 39346667573680527321118357)
            ·
              refine ⟨1844375042516274718177423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39346667573680527321118357 1844375042516274718177423)
              ·
                refine ⟨2766562563774412077266135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844375042516274718177423 2766562563774412077266135)
                ·
                  refine ⟨4149843845661618115899203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766562563774412077266135 4149843845661618115899203)
                  ·
                    refine ⟨6224765768492427173848805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4149843845661618115899203 6224765768492427173848805)
                    ·
                      refine ⟨1167143581592330095096651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6224765768492427173848805 1167143581592330095096651)
                      ·
                        rfl

theorem cell23_2273004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 4].length) (baseStart_2273004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273004 prefixEnd_2273004 := by exact prefixLift 2273004
  have htrace : WordTrace (prefixWord ++ tailWord_2273004) baseStart_2273004 baseEnd_2273004 := by
    simpa [prefixWord, tailWord_2273004, baseEnd_2273004] using wordTrace_append hprefix tailTrace_2273004
  have hstable : (prefixWord ++ tailWord_2273004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273004).length < 2 ^ (prefixWord ++ tailWord_2273004).sum := by decide
  have hdescent : baseEnd_2273004 < baseStart_2273004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273010 : List Nat := [3, 2, 1, 3, 1, 1, 12]
def baseStart_2273010 : Nat := 118140960795 + 2273010 * 2 ^ 59
def prefixEnd_2273010 : Nat := 4983230072969 + 3 ^ 40 * 2273010 * 2
def baseEnd_2273010 : Nat := 14409218055262432982983

theorem tailTrace_2273010 : CollatzResearch.WordTrace tailWord_2273010 prefixEnd_2273010 14409218055262432982983 := by
  unfold tailWord_2273010
  simp only [CollatzResearch.WordTrace]
  refine ⟨20725871373820111011748121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55268990330186962697994989 20725871373820111011748121)
  ·
    refine ⟨15544403530365083258811091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20725871373820111011748121 15544403530365083258811091)
    ·
      refine ⟨23316605295547624888216637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15544403530365083258811091 23316605295547624888216637)
      ·
        refine ⟨8743726985830359333081239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23316605295547624888216637 8743726985830359333081239)
        ·
          refine ⟨13115590478745538999621859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8743726985830359333081239 13115590478745538999621859)
          ·
            refine ⟨19673385718118308499432789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13115590478745538999621859 19673385718118308499432789)
            ·
              refine ⟨14409218055262432982983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 19673385718118308499432789 14409218055262432982983)
              ·
                rfl

theorem cell23_2273010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 12].length) (baseStart_2273010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273010 prefixEnd_2273010 := by exact prefixLift 2273010
  have htrace : WordTrace (prefixWord ++ tailWord_2273010) baseStart_2273010 baseEnd_2273010 := by
    simpa [prefixWord, tailWord_2273010, baseEnd_2273010] using wordTrace_append hprefix tailTrace_2273010
  have hstable : (prefixWord ++ tailWord_2273010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273010).length < 2 ^ (prefixWord ++ tailWord_2273010).sum := by decide
  have hdescent : baseEnd_2273010 < baseStart_2273010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273014 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_2273014 : Nat := 118140960795 + 2273014 * 2 ^ 59
def prefixEnd_2273014 : Nat := 4983230072969 + 3 ^ 40 * 2273014 * 2
def baseEnd_2273014 : Nat := 389049572132958351990535

theorem tailTrace_2273014 : CollatzResearch.WordTrace tailWord_2273014 prefixEnd_2273014 389049572132958351990535 := by
  unfold tailWord_2273014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5181476961704122045633631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55269087591510635153425397 5181476961704122045633631)
  ·
    refine ⟨7772215442556183068450447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5181476961704122045633631 7772215442556183068450447)
    ·
      refine ⟨11658323163834274602675671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7772215442556183068450447 11658323163834274602675671)
      ·
        refine ⟨17487484745751411904013507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11658323163834274602675671 17487484745751411904013507)
        ·
          refine ⟨26231227118627117856020261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17487484745751411904013507 26231227118627117856020261)
          ·
            refine ⟨4918355084742584598003799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26231227118627117856020261 4918355084742584598003799)
            ·
              refine ⟨7377532627113876897005699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918355084742584598003799 7377532627113876897005699)
              ·
                refine ⟨11066298940670815345508549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7377532627113876897005699 11066298940670815345508549)
                ·
                  refine ⟨2074931051375777877282853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11066298940670815345508549 2074931051375777877282853)
                  ·
                    refine ⟨389049572132958351990535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2074931051375777877282853 389049572132958351990535)
                    ·
                      rfl

theorem cell23_2273014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_2273014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273014 prefixEnd_2273014 := by exact prefixLift 2273014
  have htrace : WordTrace (prefixWord ++ tailWord_2273014) baseStart_2273014 baseEnd_2273014 := by
    simpa [prefixWord, tailWord_2273014, baseEnd_2273014] using wordTrace_append hprefix tailTrace_2273014
  have hstable : (prefixWord ++ tailWord_2273014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273014).length < 2 ^ (prefixWord ++ tailWord_2273014).sum := by decide
  have hdescent : baseEnd_2273014 < baseStart_2273014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273031 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 1, 6]
def baseStart_2273031 : Nat := 118140960795 + 2273031 * 2 ^ 59
def prefixEnd_2273031 : Nat := 4983230072969 + 3 ^ 40 * 2273031 * 2
def baseEnd_2273031 : Nat := 389052481856667163153009

theorem tailTrace_2273031 : CollatzResearch.WordTrace tailWord_2273031 prefixEnd_2273031 389052481856667163153009 := by
  unfold tailWord_2273031
  simp only [CollatzResearch.WordTrace]
  refine ⟨82904251428204364633506947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55269500952136243089004631 82904251428204364633506947)
  ·
    refine ⟨124356377142306546950260421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82904251428204364633506947 124356377142306546950260421)
    ·
      refine ⟨23316820714182477553173829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124356377142306546950260421 23316820714182477553173829)
      ·
        refine ⟨4371903883909214541220093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23316820714182477553173829 4371903883909214541220093)
        ·
          refine ⟨1639463956465955452957535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4371903883909214541220093 1639463956465955452957535)
          ·
            refine ⟨2459195934698933179436303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639463956465955452957535 2459195934698933179436303)
            ·
              refine ⟨3688793902048399769154455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2459195934698933179436303 3688793902048399769154455)
              ·
                refine ⟨5533190853072599653731683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3688793902048399769154455 5533190853072599653731683)
                ·
                  refine ⟨8299786279608899480597525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5533190853072599653731683 8299786279608899480597525)
                  ·
                    refine ⟨389052481856667163153009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8299786279608899480597525 389052481856667163153009)
                    ·
                      rfl

theorem cell23_2273031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_2273031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273031 prefixEnd_2273031 := by exact prefixLift 2273031
  have htrace : WordTrace (prefixWord ++ tailWord_2273031) baseStart_2273031 baseEnd_2273031 := by
    simpa [prefixWord, tailWord_2273031, baseEnd_2273031] using wordTrace_append hprefix tailTrace_2273031
  have hstable : (prefixWord ++ tailWord_2273031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273031).length < 2 ^ (prefixWord ++ tailWord_2273031).sum := by decide
  have hdescent : baseEnd_2273031 < baseStart_2273031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273034 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_2273034 : Nat := 118140960795 + 2273034 * 2 ^ 59
def prefixEnd_2273034 : Nat := 4983230072969 + 3 ^ 40 * 2273034 * 2
def baseEnd_2273034 : Nat := 1167158986011964977721513

theorem tailTrace_2273034 : CollatzResearch.WordTrace tailWord_2273034 prefixEnd_2273034 1167158986011964977721513 := by
  unfold tailWord_2273034
  simp only [CollatzResearch.WordTrace]
  refine ⟨20726090211798374036466539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55269573898128997430577437 20726090211798374036466539)
  ·
    refine ⟨31089135317697561054699809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20726090211798374036466539 31089135317697561054699809)
    ·
      refine ⟨23316851488273170791024857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31089135317697561054699809 23316851488273170791024857)
      ·
        refine ⟨17487638616204878093268643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23316851488273170791024857 17487638616204878093268643)
        ·
          refine ⟨26231457924307317139902965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17487638616204878093268643 26231457924307317139902965)
          ·
            refine ⟨2459199180403810981865903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26231457924307317139902965 2459199180403810981865903)
            ·
              refine ⟨3688798770605716472798855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2459199180403810981865903 3688798770605716472798855)
              ·
                refine ⟨5533198155908574709198283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3688798770605716472798855 5533198155908574709198283)
                ·
                  refine ⟨8299797233862862063797425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5533198155908574709198283 8299797233862862063797425)
                  ·
                    refine ⟨6224847925397146547848069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8299797233862862063797425 6224847925397146547848069)
                    ·
                      refine ⟨1167158986011964977721513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6224847925397146547848069 1167158986011964977721513)
                      ·
                        rfl

theorem cell23_2273034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_2273034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273034 prefixEnd_2273034 := by exact prefixLift 2273034
  have htrace : WordTrace (prefixWord ++ tailWord_2273034) baseStart_2273034 baseEnd_2273034 := by
    simpa [prefixWord, tailWord_2273034, baseEnd_2273034] using wordTrace_append hprefix tailTrace_2273034
  have hstable : (prefixWord ++ tailWord_2273034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273034).length < 2 ^ (prefixWord ++ tailWord_2273034).sum := by decide
  have hdescent : baseEnd_2273034 < baseStart_2273034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273111 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 1, 4, 2]
def baseStart_2273111 : Nat := 118140960795 + 2273111 * 2 ^ 59
def prefixEnd_2273111 : Nat := 4983230072969 + 3 ^ 40 * 2273111 * 2
def baseEnd_2273111 : Nat := 1167198524022361176458659

theorem tailTrace_2273111 : CollatzResearch.WordTrace tailWord_2273111 prefixEnd_2273111 1167198524022361176458659 := by
  unfold tailWord_2273111
  simp only [CollatzResearch.WordTrace]
  refine ⟨82907169267914538296419187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55271446178609692197612791 82907169267914538296419187)
  ·
    refine ⟨124360753901871807444628781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82907169267914538296419187 124360753901871807444628781)
    ·
      refine ⟨46635282713201927791735793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124360753901871807444628781 46635282713201927791735793)
      ·
        refine ⟨34976462034901445843801845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46635282713201927791735793 34976462034901445843801845)
        ·
          refine ⟨3279043315772010547856423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34976462034901445843801845 3279043315772010547856423)
          ·
            refine ⟨4918564973658015821784635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279043315772010547856423 4918564973658015821784635)
            ·
              refine ⟨7377847460487023732676953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918564973658015821784635 7377847460487023732676953)
              ·
                refine ⟨5533385595365267799507715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7377847460487023732676953 5533385595365267799507715)
                ·
                  refine ⟨8300078393047901699261573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5533385595365267799507715 8300078393047901699261573)
                  ·
                    refine ⟨1556264698696481568611545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8300078393047901699261573 1556264698696481568611545)
                    ·
                      refine ⟨1167198524022361176458659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1556264698696481568611545 1167198524022361176458659)
                      ·
                        rfl

theorem cell23_2273111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_2273111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273111 prefixEnd_2273111 := by exact prefixLift 2273111
  have htrace : WordTrace (prefixWord ++ tailWord_2273111) baseStart_2273111 baseEnd_2273111 := by
    simpa [prefixWord, tailWord_2273111, baseEnd_2273111] using wordTrace_append hprefix tailTrace_2273111
  have hstable : (prefixWord ++ tailWord_2273111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273111).length < 2 ^ (prefixWord ++ tailWord_2273111).sum := by decide
  have hdescent : baseEnd_2273111 < baseStart_2273111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273128 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_2273128 : Nat := 118140960795 + 2273128 * 2 ^ 59
def prefixEnd_2273128 : Nat := 4983230072969 + 3 ^ 40 * 2273128 * 2
def baseEnd_2273128 : Nat := 1167207253193487609946081

theorem tailTrace_2273128 : CollatzResearch.WordTrace tailWord_2273128 prefixEnd_2273128 1167207253193487609946081 := by
  unfold tailWord_2273128
  simp only [CollatzResearch.WordTrace]
  refine ⟨41453894654426475099894019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55271859539235300133192025 41453894654426475099894019)
  ·
    refine ⟨62180841981639712649841029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41453894654426475099894019 62180841981639712649841029)
    ·
      refine ⟨11658907871557446121845193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62180841981639712649841029 11658907871557446121845193)
      ·
        refine ⟨8744180903668084591383895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11658907871557446121845193 8744180903668084591383895)
        ·
          refine ⟨13116271355502126887075843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8744180903668084591383895 13116271355502126887075843)
          ·
            refine ⟨19674407033253190330613765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13116271355502126887075843 19674407033253190330613765)
            ·
              refine ⟨3688951318734973186990081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19674407033253190330613765 3688951318734973186990081)
              ·
                refine ⟨2766713489051229890242561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3688951318734973186990081 2766713489051229890242561)
                ·
                  refine ⟨2075035116788422417681921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2766713489051229890242561 2075035116788422417681921)
                  ·
                    refine ⟨1556276337591316813261441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2075035116788422417681921 1556276337591316813261441)
                    ·
                      refine ⟨1167207253193487609946081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1556276337591316813261441 1167207253193487609946081)
                      ·
                        rfl

theorem cell23_2273128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_2273128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273128 prefixEnd_2273128 := by exact prefixLift 2273128
  have htrace : WordTrace (prefixWord ++ tailWord_2273128) baseStart_2273128 baseEnd_2273128 := by
    simpa [prefixWord, tailWord_2273128, baseEnd_2273128] using wordTrace_append hprefix tailTrace_2273128
  have hstable : (prefixWord ++ tailWord_2273128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273128).length < 2 ^ (prefixWord ++ tailWord_2273128).sum := by decide
  have hdescent : baseEnd_2273128 < baseStart_2273128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273201 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 2, 4, 2]
def baseStart_2273201 : Nat := 118140960795 + 2273201 * 2 ^ 59
def prefixEnd_2273201 : Nat := 4983230072969 + 3 ^ 40 * 2273201 * 2
def baseEnd_2273201 : Nat := 1167244737281265824333245

theorem tailTrace_2273201 : CollatzResearch.WordTrace tailWord_2273201 prefixEnd_2273201 1167244737281265824333245 := by
  unfold tailWord_2273201
  simp only [CollatzResearch.WordTrace]
  refine ⟨82910451837588483667195457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55273634558392322444796971 82910451837588483667195457)
  ·
    refine ⟨62182838878191362750396593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82910451837588483667195457 62182838878191362750396593)
    ·
      refine ⟨46637129158643522062797445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62182838878191362750396593 46637129158643522062797445)
      ·
        refine ⟨8744461717245660386774521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46637129158643522062797445 8744461717245660386774521)
        ·
          refine ⟨6558346287934245290080891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8744461717245660386774521 6558346287934245290080891)
          ·
            refine ⟨9837519431901367935121337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558346287934245290080891 9837519431901367935121337)
            ·
              refine ⟨7378139573926025951341003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9837519431901367935121337 7378139573926025951341003)
              ·
                refine ⟨11067209360889038927011505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7378139573926025951341003 11067209360889038927011505)
                ·
                  refine ⟨8300407020666779195258629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11067209360889038927011505 8300407020666779195258629)
                  ·
                    refine ⟨1556326316375021099110993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8300407020666779195258629 1556326316375021099110993)
                    ·
                      refine ⟨1167244737281265824333245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1556326316375021099110993 1167244737281265824333245)
                      ·
                        rfl

theorem cell23_2273201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_2273201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273201 prefixEnd_2273201 := by exact prefixLift 2273201
  have htrace : WordTrace (prefixWord ++ tailWord_2273201) baseStart_2273201 baseEnd_2273201 := by
    simpa [prefixWord, tailWord_2273201, baseEnd_2273201] using wordTrace_append hprefix tailTrace_2273201
  have hstable : (prefixWord ++ tailWord_2273201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273201).length < 2 ^ (prefixWord ++ tailWord_2273201).sum := by decide
  have hdescent : baseEnd_2273201 < baseStart_2273201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273228 : List Nat := [2, 2, 1, 4, 1, 2, 3, 3, 1, 4]
def baseStart_2273228 : Nat := 118140960795 + 2273228 * 2 ^ 59
def prefixEnd_2273228 : Nat := 4983230072969 + 3 ^ 40 * 2273228 * 2
def baseEnd_2273228 : Nat := 389086200419645739565207

theorem tailTrace_2273228 : CollatzResearch.WordTrace tailWord_2273228 prefixEnd_2273228 389086200419645739565207 := by
  unfold tailWord_2273228
  simp only [CollatzResearch.WordTrace]
  refine ⟨41455718304245333639214169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55274291072327111518952225 41455718304245333639214169)
  ·
    refine ⟨31091788728184000229410627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41455718304245333639214169 31091788728184000229410627)
    ·
      refine ⟨46637683092276000344115941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31091788728184000229410627 46637683092276000344115941)
      ·
        refine ⟨8744565579801750064521739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46637683092276000344115941 8744565579801750064521739)
        ·
          refine ⟨13116848369702625096782609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8744565579801750064521739 13116848369702625096782609)
          ·
            refine ⟨9837636277276968822586957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13116848369702625096782609 9837636277276968822586957)
            ·
              refine ⟨3689113603978863308470109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9837636277276968822586957 3689113603978863308470109)
              ·
                refine ⟨1383417601492073740676291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3689113603978863308470109 1383417601492073740676291)
                ·
                  refine ⟨2075126402238110611014437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383417601492073740676291 2075126402238110611014437)
                  ·
                    refine ⟨389086200419645739565207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2075126402238110611014437 389086200419645739565207)
                    ·
                      rfl

theorem cell23_2273228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_2273228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273228 prefixEnd_2273228 := by exact prefixLift 2273228
  have htrace : WordTrace (prefixWord ++ tailWord_2273228) baseStart_2273228 baseEnd_2273228 := by
    simpa [prefixWord, tailWord_2273228, baseEnd_2273228] using wordTrace_append hprefix tailTrace_2273228
  have hstable : (prefixWord ++ tailWord_2273228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273228).length < 2 ^ (prefixWord ++ tailWord_2273228).sum := by decide
  have hdescent : baseEnd_2273228 < baseStart_2273228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273245 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2273245 : Nat := 118140960795 + 2273245 * 2 ^ 59
def prefixEnd_2273245 : Nat := 4983230072969 + 3 ^ 40 * 2273245 * 2
def baseEnd_2273245 : Nat := 389089110143354550727681

theorem tailTrace_2273245 : CollatzResearch.WordTrace tailWord_2273245 prefixEnd_2273245 389089110143354550727681 := by
  unfold tailWord_2273245
  simp only [CollatzResearch.WordTrace]
  refine ⟨82912056649429079181797189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55274704432952719454531459 82912056649429079181797189)
  ·
    refine ⟨15546010621767952346586973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82912056649429079181797189 15546010621767952346586973)
    ·
      refine ⟨5829753983162982129970115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15546010621767952346586973 5829753983162982129970115)
      ·
        refine ⟨8744630974744473194955173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5829753983162982129970115 8744630974744473194955173)
        ·
          refine ⟨1639618307764588724054095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8744630974744473194955173 1639618307764588724054095)
          ·
            refine ⟨2459427461646883086081143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639618307764588724054095 2459427461646883086081143)
            ·
              refine ⟨3689141192470324629121715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2459427461646883086081143 3689141192470324629121715)
              ·
                refine ⟨5533711788705486943682573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3689141192470324629121715 5533711788705486943682573)
                ·
                  refine ⟨2075141920764557603880965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5533711788705486943682573 2075141920764557603880965)
                  ·
                    refine ⟨389089110143354550727681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2075141920764557603880965 389089110143354550727681)
                    ·
                      rfl

theorem cell23_2273245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2273245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273245 prefixEnd_2273245 := by exact prefixLift 2273245
  have htrace : WordTrace (prefixWord ++ tailWord_2273245) baseStart_2273245 baseEnd_2273245 := by
    simpa [prefixWord, tailWord_2273245, baseEnd_2273245] using wordTrace_append hprefix tailTrace_2273245
  have hstable : (prefixWord ++ tailWord_2273245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273245).length < 2 ^ (prefixWord ++ tailWord_2273245).sum := by decide
  have hdescent : baseEnd_2273245 < baseStart_2273245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273267 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 5, 6]
def baseStart_2273267 : Nat := 118140960795 + 2273267 * 2 ^ 59
def prefixEnd_2273267 : Nat := 4983230072969 + 3 ^ 40 * 2273267 * 2
def baseEnd_2273267 : Nat := 389092875668154188702647

theorem tailTrace_2273267 : CollatzResearch.WordTrace tailWord_2273267 prefixEnd_2273267 389092875668154188702647 := by
  unfold tailWord_2273267
  simp only [CollatzResearch.WordTrace]
  refine ⟨82912859055349376939098055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55275239370232917959398703 82912859055349376939098055)
  ·
    refine ⟨124369288583024065408647083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82912859055349376939098055 124369288583024065408647083)
    ·
      refine ⟨186553932874536098112970625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124369288583024065408647083 186553932874536098112970625)
      ·
        refine ⟨139915449655902073584727969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186553932874536098112970625 139915449655902073584727969)
        ·
          refine ⟨104936587241926555188545977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139915449655902073584727969 104936587241926555188545977)
          ·
            refine ⟨78702440431444916391409483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104936587241926555188545977 78702440431444916391409483)
            ·
              refine ⟨118053660647167374587114225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78702440431444916391409483 118053660647167374587114225)
              ·
                refine ⟨88540245485375530940335669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118053660647167374587114225 88540245485375530940335669)
                ·
                  refine ⟨8300648014253956025656469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88540245485375530940335669 8300648014253956025656469)
                  ·
                    refine ⟨389092875668154188702647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8300648014253956025656469 389092875668154188702647)
                    ·
                      rfl

theorem cell23_2273267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 6].length) (baseStart_2273267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273267 prefixEnd_2273267 := by exact prefixLift 2273267
  have htrace : WordTrace (prefixWord ++ tailWord_2273267) baseStart_2273267 baseEnd_2273267 := by
    simpa [prefixWord, tailWord_2273267, baseEnd_2273267] using wordTrace_append hprefix tailTrace_2273267
  have hstable : (prefixWord ++ tailWord_2273267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273267).length < 2 ^ (prefixWord ++ tailWord_2273267).sum := by decide
  have hdescent : baseEnd_2273267 < baseStart_2273267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273304 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2273304 : Nat := 118140960795 + 2273304 * 2 ^ 59
def prefixEnd_2273304 : Nat := 4983230072969 + 3 ^ 40 * 2273304 * 2
def baseEnd_2273304 : Nat := 1167297625788678921345271

theorem tailTrace_2273304 : CollatzResearch.WordTrace tailWord_2273304 prefixEnd_2273304 1167297625788678921345271 := by
  unfold tailWord_2273304
  simp only [CollatzResearch.WordTrace]
  refine ⟨41457104278107666129097483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55276139037476888172129977 41457104278107666129097483)
  ·
    refine ⟨62185656417161499193646225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41457104278107666129097483 62185656417161499193646225)
    ·
      refine ⟨46639242312871124395234669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62185656417161499193646225 46639242312871124395234669)
      ·
        refine ⟨17489715867326671648213001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46639242312871124395234669 17489715867326671648213001)
        ·
          refine ⟨13117286900495003736159751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17489715867326671648213001 13117286900495003736159751)
          ·
            refine ⟨19675930350742505604239627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13117286900495003736159751 19675930350742505604239627)
            ·
              refine ⟨29513895526113758406359441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19675930350742505604239627 29513895526113758406359441)
              ·
                refine ⟨22135421644585318804769581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29513895526113758406359441 22135421644585318804769581)
                ·
                  refine ⟨8300783116719494551788593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22135421644585318804769581 8300783116719494551788593)
                  ·
                    refine ⟨6225587337539620913841445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8300783116719494551788593 6225587337539620913841445)
                    ·
                      refine ⟨1167297625788678921345271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6225587337539620913841445 1167297625788678921345271)
                      ·
                        rfl

theorem cell23_2273304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2273304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273304 prefixEnd_2273304 := by exact prefixLift 2273304
  have htrace : WordTrace (prefixWord ++ tailWord_2273304) baseStart_2273304 baseEnd_2273304 := by
    simpa [prefixWord, tailWord_2273304, baseEnd_2273304] using wordTrace_append hprefix tailTrace_2273304
  have hstable : (prefixWord ++ tailWord_2273304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273304).length < 2 ^ (prefixWord ++ tailWord_2273304).sum := by decide
  have hdescent : baseEnd_2273304 < baseStart_2273304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273307 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 7]
def baseStart_2273307 : Nat := 118140960795 + 2273307 * 2 ^ 59
def prefixEnd_2273307 : Nat := 4983230072969 + 3 ^ 40 * 2273307 * 2
def baseEnd_2273307 : Nat := 1167299166230642409607757

theorem tailTrace_2273307 : CollatzResearch.WordTrace tailWord_2273307 prefixEnd_2273307 1167299166230642409607757 := by
  unfold tailWord_2273307
  simp only [CollatzResearch.WordTrace]
  refine ⟨82914317975204463770554175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55276211983469642513702783 82914317975204463770554175)
  ·
    refine ⟨124371476962806695655831263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82914317975204463770554175 124371476962806695655831263)
    ·
      refine ⟨186557215444210043483746895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124371476962806695655831263 186557215444210043483746895)
      ·
        refine ⟨279835823166315065225620343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186557215444210043483746895 279835823166315065225620343)
        ·
          refine ⟨419753734749472597838430515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279835823166315065225620343 419753734749472597838430515)
          ·
            refine ⟨629630602124208896757645773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419753734749472597838430515 629630602124208896757645773)
            ·
              refine ⟨236111475796578336284117165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 629630602124208896757645773 236111475796578336284117165)
              ·
                refine ⟨88541803423716876106543937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236111475796578336284117165 88541803423716876106543937)
                ·
                  refine ⟨66406352567787657079907953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88541803423716876106543937 66406352567787657079907953)
                  ·
                    refine ⟨49804764425840742809930965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66406352567787657079907953 49804764425840742809930965)
                    ·
                      refine ⟨1167299166230642409607757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49804764425840742809930965 1167299166230642409607757)
                      ·
                        rfl

theorem cell23_2273307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_2273307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273307 prefixEnd_2273307 := by exact prefixLift 2273307
  have htrace : WordTrace (prefixWord ++ tailWord_2273307) baseStart_2273307 baseEnd_2273307 := by
    simpa [prefixWord, tailWord_2273307, baseEnd_2273307] using wordTrace_append hprefix tailTrace_2273307
  have hstable : (prefixWord ++ tailWord_2273307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273307).length < 2 ^ (prefixWord ++ tailWord_2273307).sum := by decide
  have hdescent : baseEnd_2273307 < baseStart_2273307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273341 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_2273341 : Nat := 118140960795 + 2273341 * 2 ^ 59
def prefixEnd_2273341 : Nat := 4983230072969 + 3 ^ 40 * 2273341 * 2
def baseEnd_2273341 : Nat := 1167316624572895276582601

theorem tailTrace_2273341 : CollatzResearch.WordTrace tailWord_2273341 prefixEnd_2273341 1167316624572895276582601 := by
  unfold tailWord_2273341
  simp only [CollatzResearch.WordTrace]
  refine ⟨82915558057081287577291877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55277038704720858384861251 82915558057081287577291877)
  ·
    refine ⟨15546667135702741420742227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82915558057081287577291877 15546667135702741420742227)
    ·
      refine ⟨23320000703554112131113341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15546667135702741420742227 23320000703554112131113341)
      ·
        refine ⟨8745000263832792049167503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23320000703554112131113341 8745000263832792049167503)
        ·
          refine ⟨13117500395749188073751255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8745000263832792049167503 13117500395749188073751255)
          ·
            refine ⟨19676250593623782110626883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13117500395749188073751255 19676250593623782110626883)
            ·
              refine ⟨29514375890435673165940325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19676250593623782110626883 29514375890435673165940325)
              ·
                refine ⟨5533945479456688718613811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29514375890435673165940325 5533945479456688718613811)
                ·
                  refine ⟨8300918219185033077920717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5533945479456688718613811 8300918219185033077920717)
                  ·
                    refine ⟨3112844332194387404220269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8300918219185033077920717 3112844332194387404220269)
                    ·
                      refine ⟨1167316624572895276582601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3112844332194387404220269 1167316624572895276582601)
                      ·
                        rfl

theorem cell23_2273341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_2273341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273341 prefixEnd_2273341 := by exact prefixLift 2273341
  have htrace : WordTrace (prefixWord ++ tailWord_2273341) baseStart_2273341 baseEnd_2273341 := by
    simpa [prefixWord, tailWord_2273341, baseEnd_2273341] using wordTrace_append hprefix tailTrace_2273341
  have hstable : (prefixWord ++ tailWord_2273341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273341).length < 2 ^ (prefixWord ++ tailWord_2273341).sum := by decide
  have hdescent : baseEnd_2273341 < baseStart_2273341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273342 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_2273342 : Nat := 118140960795 + 2273342 * 2 ^ 59
def prefixEnd_2273342 : Nat := 4983230072969 + 3 ^ 40 * 2273342 * 2
def baseEnd_2273342 : Nat := 1167317138053549772670097

theorem tailTrace_2273342 : CollatzResearch.WordTrace tailWord_2273342 prefixEnd_2273342 1167317138053549772670097 := by
  unfold tailWord_2273342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10364449316259708093509785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55277063020051776498718853 10364449316259708093509785)
  ·
    refine ⟨7773336987194781070132339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10364449316259708093509785 7773336987194781070132339)
    ·
      refine ⟨11660005480792171605198509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7773336987194781070132339 11660005480792171605198509)
      ·
        refine ⟨4372502055297064351949441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11660005480792171605198509 4372502055297064351949441)
        ·
          refine ⟨3279376541472798263962081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4372502055297064351949441 3279376541472798263962081)
          ·
            refine ⟨2459532406104598697971561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3279376541472798263962081 2459532406104598697971561)
            ·
              refine ⟨1844649304578449023478671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2459532406104598697971561 1844649304578449023478671)
              ·
                refine ⟨2766973956867673535218007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844649304578449023478671 2766973956867673535218007)
                ·
                  refine ⟨4150460935301510302827011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766973956867673535218007 4150460935301510302827011)
                  ·
                    refine ⟨6225691402952265454240517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4150460935301510302827011 6225691402952265454240517)
                    ·
                      refine ⟨1167317138053549772670097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6225691402952265454240517 1167317138053549772670097)
                      ·
                        rfl

theorem cell23_2273342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_2273342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273342 prefixEnd_2273342 := by exact prefixLift 2273342
  have htrace : WordTrace (prefixWord ++ tailWord_2273342) baseStart_2273342 baseEnd_2273342 := by
    simpa [prefixWord, tailWord_2273342, baseEnd_2273342] using wordTrace_append hprefix tailTrace_2273342
  have hstable : (prefixWord ++ tailWord_2273342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273342).length < 2 ^ (prefixWord ++ tailWord_2273342).sum := by decide
  have hdescent : baseEnd_2273342 < baseStart_2273342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273345 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_2273345 : Nat := 118140960795 + 2273345 * 2 ^ 59
def prefixEnd_2273345 : Nat := 4983230072969 + 3 ^ 40 * 2273345 * 2
def baseEnd_2273345 : Nat := 1167318678495513260932583

theorem tailTrace_2273345 : CollatzResearch.WordTrace tailWord_2273345 prefixEnd_2273345 1167318678495513260932583 := by
  unfold tailWord_2273345
  simp only [CollatzResearch.WordTrace]
  refine ⟨82915703949066796260437489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55277135966044530840291659 82915703949066796260437489)
  ·
    refine ⟨62186777961800097195328117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82915703949066796260437489 62186777961800097195328117)
    ·
      refine ⟨5830010433918759112062011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62186777961800097195328117 5830010433918759112062011)
      ·
        refine ⟨8745015650878138668093017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5830010433918759112062011 8745015650878138668093017)
        ·
          refine ⟨6558761738158604001069763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8745015650878138668093017 6558761738158604001069763)
          ·
            refine ⟨9838142607237906001604645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558761738158604001069763 9838142607237906001604645)
            ·
              refine ⟨1844651738857107375300871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9838142607237906001604645 1844651738857107375300871)
              ·
                refine ⟨2766977608285661062951307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844651738857107375300871 2766977608285661062951307)
                ·
                  refine ⟨4150466412428491594426961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766977608285661062951307 4150466412428491594426961)
                  ·
                    refine ⟨3112849809321368695820221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4150466412428491594426961 3112849809321368695820221)
                    ·
                      refine ⟨1167318678495513260932583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3112849809321368695820221 1167318678495513260932583)
                      ·
                        rfl

theorem cell23_2273345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_2273345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273345 prefixEnd_2273345 := by exact prefixLift 2273345
  have htrace : WordTrace (prefixWord ++ tailWord_2273345) baseStart_2273345 baseEnd_2273345 := by
    simpa [prefixWord, tailWord_2273345, baseEnd_2273345] using wordTrace_append hprefix tailTrace_2273345
  have hstable : (prefixWord ++ tailWord_2273345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273345).length < 2 ^ (prefixWord ++ tailWord_2273345).sum := by decide
  have hdescent : baseEnd_2273345 < baseStart_2273345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273358 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_2273358 : Nat := 118140960795 + 2273358 * 2 ^ 59
def prefixEnd_2273358 : Nat := 4983230072969 + 3 ^ 40 * 2273358 * 2
def baseEnd_2273358 : Nat := 1167325353744021710070023

theorem tailTrace_2273358 : CollatzResearch.WordTrace tailWord_2273358 prefixEnd_2273358 1167325353744021710070023 := by
  unfold tailWord_2273358
  simp only [CollatzResearch.WordTrace]
  refine ⟨10364522262252462435082591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55277452065346466320440485 10364522262252462435082591)
  ·
    refine ⟨15546783393378693652623887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10364522262252462435082591 15546783393378693652623887)
    ·
      refine ⟨23320175090068040478935831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15546783393378693652623887 23320175090068040478935831)
      ·
        refine ⟨34980262635102060718403747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23320175090068040478935831 34980262635102060718403747)
        ·
          refine ⟨52470393952653091077605621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34980262635102060718403747 52470393952653091077605621)
          ·
            refine ⟨4919099433061227288525527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52470393952653091077605621 4919099433061227288525527)
            ·
              refine ⟨7378649149591840932788291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4919099433061227288525527 7378649149591840932788291)
              ·
                refine ⟨11067973724387761399182437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7378649149591840932788291 11067973724387761399182437)
                ·
                  refine ⟨2075245073322705262346707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11067973724387761399182437 2075245073322705262346707)
                  ·
                    refine ⟨3112867609984057893520061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2075245073322705262346707 3112867609984057893520061)
                    ·
                      refine ⟨1167325353744021710070023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3112867609984057893520061 1167325353744021710070023)
                      ·
                        rfl

theorem cell23_2273358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_2273358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273358 prefixEnd_2273358 := by exact prefixLift 2273358
  have htrace : WordTrace (prefixWord ++ tailWord_2273358) baseStart_2273358 baseEnd_2273358 := by
    simpa [prefixWord, tailWord_2273358, baseEnd_2273358] using wordTrace_append hprefix tailTrace_2273358
  have hstable : (prefixWord ++ tailWord_2273358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273358).length < 2 ^ (prefixWord ++ tailWord_2273358).sum := by decide
  have hdescent : baseEnd_2273358 < baseStart_2273358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273401 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 5]
def baseStart_2273401 : Nat := 118140960795 + 2273401 * 2 ^ 59
def prefixEnd_2273401 : Nat := 4983230072969 + 3 ^ 40 * 2273401 * 2
def baseEnd_2273401 : Nat := 1167347433412165041832325

theorem tailTrace_2273401 : CollatzResearch.WordTrace tailWord_2273401 prefixEnd_2273401 1167347433412165041832325 := by
  unfold tailWord_2273401
  simp only [CollatzResearch.WordTrace]
  refine ⟨82917746436863917824476057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55278497624575945216317371 82917746436863917824476057)
  ·
    refine ⟨62188309827647938368357043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82917746436863917824476057 62188309827647938368357043)
    ·
      refine ⟨93282464741471907552535565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62188309827647938368357043 93282464741471907552535565)
      ·
        refine ⟨34980924278051965332200837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93282464741471907552535565 34980924278051965332200837)
        ·
          refine ⟨6558923302134743499787657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34980924278051965332200837 6558923302134743499787657)
          ·
            refine ⟨4919192476601057624840743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6558923302134743499787657 4919192476601057624840743)
            ·
              refine ⟨7378788714901586437261115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4919192476601057624840743 7378788714901586437261115)
              ·
                refine ⟨11068183072352379655891673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7378788714901586437261115 11068183072352379655891673)
                ·
                  refine ⟨8301137304264284741918755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11068183072352379655891673 8301137304264284741918755)
                  ·
                    refine ⟨12451705956396427112878133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8301137304264284741918755 12451705956396427112878133)
                    ·
                      refine ⟨1167347433412165041832325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12451705956396427112878133 1167347433412165041832325)
                      ·
                        rfl

theorem cell23_2273401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_2273401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273401 prefixEnd_2273401 := by exact prefixLift 2273401
  have htrace : WordTrace (prefixWord ++ tailWord_2273401) baseStart_2273401 baseEnd_2273401 := by
    simpa [prefixWord, tailWord_2273401, baseEnd_2273401] using wordTrace_append hprefix tailTrace_2273401
  have hstable : (prefixWord ++ tailWord_2273401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273401).length < 2 ^ (prefixWord ++ tailWord_2273401).sum := by decide
  have hdescent : baseEnd_2273401 < baseStart_2273401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273432 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 2, 2, 2]
def baseStart_2273432 : Nat := 118140960795 + 2273432 * 2 ^ 59
def prefixEnd_2273432 : Nat := 4983230072969 + 3 ^ 40 * 2273432 * 2
def baseEnd_2273432 : Nat := 1167363351312454420544683

theorem tailTrace_2273432 : CollatzResearch.WordTrace tailWord_2273432 prefixEnd_2273432 1167363351312454420544683 := by
  unfold tailWord_2273432
  simp only [CollatzResearch.WordTrace]
  refine ⟨41459438549875805059427275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55279251399834406745903033 41459438549875805059427275)
  ·
    refine ⟨62189157824813707589140913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41459438549875805059427275 62189157824813707589140913)
    ·
      refine ⟨46641868368610280691855685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62189157824813707589140913 46641868368610280691855685)
      ·
        refine ⟨8745350319114427629722941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46641868368610280691855685 8745350319114427629722941)
        ·
          refine ⟨3279506369667910361146103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8745350319114427629722941 3279506369667910361146103)
          ·
            refine ⟨4919259554501865541719155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279506369667910361146103 4919259554501865541719155)
            ·
              refine ⟨7378889331752798312578733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4919259554501865541719155 7378889331752798312578733)
              ·
                refine ⟨2767083499407299367217025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7378889331752798312578733 2767083499407299367217025)
                ·
                  refine ⟨2075312624555474525412769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2767083499407299367217025 2075312624555474525412769)
                  ·
                    refine ⟨1556484468416605894059577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2075312624555474525412769 1556484468416605894059577)
                    ·
                      refine ⟨1167363351312454420544683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1556484468416605894059577 1167363351312454420544683)
                      ·
                        rfl

theorem cell23_2273432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_2273432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273432 prefixEnd_2273432 := by exact prefixLift 2273432
  have htrace : WordTrace (prefixWord ++ tailWord_2273432) baseStart_2273432 baseEnd_2273432 := by
    simpa [prefixWord, tailWord_2273432, baseEnd_2273432] using wordTrace_append hprefix tailTrace_2273432
  have hstable : (prefixWord ++ tailWord_2273432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273432).length < 2 ^ (prefixWord ++ tailWord_2273432).sum := by decide
  have hdescent : baseEnd_2273432 < baseStart_2273432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273515 : List Nat := [1, 1, 1, 1, 2, 5, 4, 3, 1, 4]
def baseStart_2273515 : Nat := 118140960795 + 2273515 * 2 ^ 59
def prefixEnd_2273515 : Nat := 4983230072969 + 3 ^ 40 * 2273515 * 2
def baseEnd_2273515 : Nat := 389135323402259198602267

theorem tailTrace_2273515 : CollatzResearch.WordTrace tailWord_2273515 prefixEnd_2273515 389135323402259198602267 := by
  unfold tailWord_2273515
  simp only [CollatzResearch.WordTrace]
  refine ⟨82921904358450915294125999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55281269572300610196083999 82921904358450915294125999)
  ·
    refine ⟨124382856537676372941188999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82921904358450915294125999 124382856537676372941188999)
    ·
      refine ⟨186574284806514559411783499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124382856537676372941188999 186574284806514559411783499)
      ·
        refine ⟨279861427209771839117675249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186574284806514559411783499 279861427209771839117675249)
        ·
          refine ⟨209896070407328879338256437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279861427209771839117675249 209896070407328879338256437)
          ·
            refine ⟨19677756600687082437961541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 209896070407328879338256437 19677756600687082437961541)
            ·
              refine ⟨3689579362628827957117789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19677756600687082437961541 3689579362628827957117789)
              ·
                refine ⟨1383592260985810483919171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3689579362628827957117789 1383592260985810483919171)
                ·
                  refine ⟨2075388391478715725878757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383592260985810483919171 2075388391478715725878757)
                  ·
                    refine ⟨389135323402259198602267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2075388391478715725878757 389135323402259198602267)
                    ·
                      rfl

theorem cell23_2273515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 1, 4].length) (baseStart_2273515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273515 prefixEnd_2273515 := by exact prefixLift 2273515
  have htrace : WordTrace (prefixWord ++ tailWord_2273515) baseStart_2273515 baseEnd_2273515 := by
    simpa [prefixWord, tailWord_2273515, baseEnd_2273515] using wordTrace_append hprefix tailTrace_2273515
  have hstable : (prefixWord ++ tailWord_2273515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273515).length < 2 ^ (prefixWord ++ tailWord_2273515).sum := by decide
  have hdescent : baseEnd_2273515 < baseStart_2273515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273541 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_2273541 : Nat := 118140960795 + 2273541 * 2 ^ 59
def prefixEnd_2273541 : Nat := 4983230072969 + 3 ^ 40 * 2273541 * 2
def baseEnd_2273541 : Nat := 389139773567931498027227

theorem tailTrace_2273541 : CollatzResearch.WordTrace tailWord_2273541 prefixEnd_2273541 389139773567931498027227 := by
  unfold tailWord_2273541
  simp only [CollatzResearch.WordTrace]
  refine ⟨82922852656356721734572477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55281901770904481156381651 82922852656356721734572477)
  ·
    refine ⟨31096069746133770650464679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82922852656356721734572477 31096069746133770650464679)
    ·
      refine ⟨46644104619200655975697019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31096069746133770650464679 46644104619200655975697019)
      ·
        refine ⟨69966156928800983963545529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46644104619200655975697019 69966156928800983963545529)
        ·
          refine ⟨52474617696600737972659147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69966156928800983963545529 52474617696600737972659147)
          ·
            refine ⟨78711926544901106958988721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52474617696600737972659147 78711926544901106958988721)
            ·
              refine ⟨59033944908675830219241541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78711926544901106958988721 59033944908675830219241541)
              ·
                refine ⟨11068864670376718166107789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59033944908675830219241541 11068864670376718166107789)
                ·
                  refine ⟨4150824251391269312290421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11068864670376718166107789 4150824251391269312290421)
                  ·
                    refine ⟨389139773567931498027227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4150824251391269312290421 389139773567931498027227)
                    ·
                      rfl

theorem cell23_2273541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_2273541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273541 prefixEnd_2273541 := by exact prefixLift 2273541
  have htrace : WordTrace (prefixWord ++ tailWord_2273541) baseStart_2273541 baseEnd_2273541 := by
    simpa [prefixWord, tailWord_2273541, baseEnd_2273541] using wordTrace_append hprefix tailTrace_2273541
  have hstable : (prefixWord ++ tailWord_2273541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273541).length < 2 ^ (prefixWord ++ tailWord_2273541).sum := by decide
  have hdescent : baseEnd_2273541 < baseStart_2273541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273548 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 3, 5, 2]
def baseStart_2273548 : Nat := 118140960795 + 2273548 * 2 ^ 59
def prefixEnd_2273548 : Nat := 4983230072969 + 3 ^ 40 * 2273548 * 2
def baseEnd_2273548 : Nat := 1167422915068375966694149

theorem tailTrace_2273548 : CollatzResearch.WordTrace tailWord_2273548 prefixEnd_2273548 1167422915068375966694149 := by
  unfold tailWord_2273548
  simp only [CollatzResearch.WordTrace]
  refine ⟨41461553983665680965038649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55282071978220907953384865 41461553983665680965038649)
  ·
    refine ⟨31096165487749260723778987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41461553983665680965038649 31096165487749260723778987)
    ·
      refine ⟨46644248231623891085668481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31096165487749260723778987 46644248231623891085668481)
      ·
        refine ⟨34983186173717918314251361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46644248231623891085668481 34983186173717918314251361)
        ·
          refine ⟨26237389630288438735688521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34983186173717918314251361 26237389630288438735688521)
          ·
            refine ⟨19678042222716329051766391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26237389630288438735688521 19678042222716329051766391)
            ·
              refine ⟨29517063334074493577649587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19678042222716329051766391 29517063334074493577649587)
              ·
                refine ⟨44275595001111740366474381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29517063334074493577649587 44275595001111740366474381)
                ·
                  refine ⟨16603348125416902637427893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44275595001111740366474381 16603348125416902637427893)
                  ·
                    refine ⟨1556563886757834622258865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16603348125416902637427893 1556563886757834622258865)
                    ·
                      refine ⟨1167422915068375966694149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1556563886757834622258865 1167422915068375966694149)
                      ·
                        rfl

theorem cell23_2273548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_2273548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273548 prefixEnd_2273548 := by exact prefixLift 2273548
  have htrace : WordTrace (prefixWord ++ tailWord_2273548) baseStart_2273548 baseEnd_2273548 := by
    simpa [prefixWord, tailWord_2273548, baseEnd_2273548] using wordTrace_append hprefix tailTrace_2273548
  have hstable : (prefixWord ++ tailWord_2273548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273548).length < 2 ^ (prefixWord ++ tailWord_2273548).sum := by decide
  have hdescent : baseEnd_2273548 < baseStart_2273548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273566 : List Nat := [4, 3, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2273566 : Nat := 118140960795 + 2273566 * 2 ^ 59
def prefixEnd_2273566 : Nat := 4983230072969 + 3 ^ 40 * 2273566 * 2
def baseEnd_2273566 : Nat := 389144052573385632089689

theorem tailTrace_2273566 : CollatzResearch.WordTrace tailWord_2273566 prefixEnd_2273566 389144052573385632089689 := by
  unfold tailWord_2273566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10365470560158268875529069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55282509654177434002821701 10365470560158268875529069)
  ·
    refine ⟨3887051460059350828323401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10365470560158268875529069 3887051460059350828323401)
    ·
      refine ⟨2915288595044513121242551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3887051460059350828323401 2915288595044513121242551)
      ·
        refine ⟨4372932892566769681863827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2915288595044513121242551 4372932892566769681863827)
        ·
          refine ⟨6559399338850154522795741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4372932892566769681863827 6559399338850154522795741)
          ·
            refine ⟨2459774752068807946048403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6559399338850154522795741 2459774752068807946048403)
            ·
              refine ⟨3689662128103211919072605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2459774752068807946048403 3689662128103211919072605)
              ·
                refine ⟨1383623298038704469652227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3689662128103211919072605 1383623298038704469652227)
                ·
                  refine ⟨2075434947058056704478341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383623298038704469652227 2075434947058056704478341)
                  ·
                    refine ⟨389144052573385632089689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2075434947058056704478341 389144052573385632089689)
                    ·
                      rfl

theorem cell23_2273566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2273566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273566 prefixEnd_2273566 := by exact prefixLift 2273566
  have htrace : WordTrace (prefixWord ++ tailWord_2273566) baseStart_2273566 baseEnd_2273566 := by
    simpa [prefixWord, tailWord_2273566, baseEnd_2273566] using wordTrace_append hprefix tailTrace_2273566
  have hstable : (prefixWord ++ tailWord_2273566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273566).length < 2 ^ (prefixWord ++ tailWord_2273566).sum := by decide
  have hdescent : baseEnd_2273566 < baseStart_2273566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273571 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 3, 6]
def baseStart_2273571 : Nat := 118140960795 + 2273571 * 2 ^ 59
def prefixEnd_2273571 : Nat := 4983230072969 + 3 ^ 40 * 2273571 * 2
def baseEnd_2273571 : Nat := 389144908374476458902181

theorem tailTrace_2273571 : CollatzResearch.WordTrace tailWord_2273571 prefixEnd_2273571 389144908374476458902181 := by
  unfold tailWord_2273571
  simp only [CollatzResearch.WordTrace]
  refine ⟨82923946846248036858164567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55282631230832024572109711 82923946846248036858164567)
  ·
    refine ⟨124385920269372055287246851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82923946846248036858164567 124385920269372055287246851)
    ·
      refine ⟨186578880404058082930870277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124385920269372055287246851 186578880404058082930870277)
      ·
        refine ⟨34983540075760890549538177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186578880404058082930870277 34983540075760890549538177)
        ·
          refine ⟨26237655056820667912153633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34983540075760890549538177 26237655056820667912153633)
          ·
            refine ⟨19678241292615500934115225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26237655056820667912153633 19678241292615500934115225)
            ·
              refine ⟨14758680969461625700586419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19678241292615500934115225 14758680969461625700586419)
              ·
                refine ⟨22138021454192438550879629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14758680969461625700586419 22138021454192438550879629)
                ·
                  refine ⟨8301758045322164456579861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22138021454192438550879629 8301758045322164456579861)
                  ·
                    refine ⟨389144908374476458902181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8301758045322164456579861 389144908374476458902181)
                    ·
                      rfl

theorem cell23_2273571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 6].length) (baseStart_2273571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273571 prefixEnd_2273571 := by exact prefixLift 2273571
  have htrace : WordTrace (prefixWord ++ tailWord_2273571) baseStart_2273571 baseEnd_2273571 := by
    simpa [prefixWord, tailWord_2273571, baseEnd_2273571] using wordTrace_append hprefix tailTrace_2273571
  have hstable : (prefixWord ++ tailWord_2273571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273571).length < 2 ^ (prefixWord ++ tailWord_2273571).sum := by decide
  have hdescent : baseEnd_2273571 < baseStart_2273571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273589 : List Nat := [1, 3, 3, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_2273589 : Nat := 118140960795 + 2273589 * 2 ^ 59
def prefixEnd_2273589 : Nat := 4983230072969 + 3 ^ 40 * 2273589 * 2
def baseEnd_2273589 : Nat := 1167443967775210306281461

theorem tailTrace_2273589 : CollatzResearch.WordTrace tailWord_2273589 prefixEnd_2273589 1167443967775210306281461 := by
  unfold tailWord_2273589
  simp only [CollatzResearch.WordTrace]
  refine ⟨82924603360182825932319821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55283068906788550621546547 82924603360182825932319821)
  ·
    refine ⟨31096726260068559724619933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82924603360182825932319821 31096726260068559724619933)
    ·
      refine ⟨11661272347525709896732475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31096726260068559724619933 11661272347525709896732475)
      ·
        refine ⟨17491908521288564845098713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11661272347525709896732475 17491908521288564845098713)
        ·
          refine ⟨13118931390966423633824035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17491908521288564845098713 13118931390966423633824035)
          ·
            refine ⟨19678397086449635450736053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13118931390966423633824035 19678397086449635450736053)
            ·
              refine ⟨1844849726854653323506505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19678397086449635450736053 1844849726854653323506505)
              ·
                refine ⟨1383637295140989992629879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1844849726854653323506505 1383637295140989992629879)
                ·
                  refine ⟨2075455942711484988944819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383637295140989992629879 2075455942711484988944819)
                  ·
                    refine ⟨3113183914067227483417229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2075455942711484988944819 3113183914067227483417229)
                    ·
                      refine ⟨1167443967775210306281461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3113183914067227483417229 1167443967775210306281461)
                      ·
                        rfl

theorem cell23_2273589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_2273589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273589 prefixEnd_2273589 := by exact prefixLift 2273589
  have htrace : WordTrace (prefixWord ++ tailWord_2273589) baseStart_2273589 baseEnd_2273589 := by
    simpa [prefixWord, tailWord_2273589, baseEnd_2273589] using wordTrace_append hprefix tailTrace_2273589
  have hstable : (prefixWord ++ tailWord_2273589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273589).length < 2 ^ (prefixWord ++ tailWord_2273589).sum := by decide
  have hdescent : baseEnd_2273589 < baseStart_2273589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273632 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 1, 1, 5]
def baseStart_2273632 : Nat := 118140960795 + 2273632 * 2 ^ 59
def prefixEnd_2273632 : Nat := 4983230072969 + 3 ^ 40 * 2273632 * 2
def baseEnd_2273632 : Nat := 1167466047443353638043763

theorem tailTrace_2273632 : CollatzResearch.WordTrace tailWord_2273632 prefixEnd_2273632 1167466047443353638043763 := by
  unfold tailWord_2273632
  simp only [CollatzResearch.WordTrace]
  refine ⟨41463085849513522138067575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55284114466018029517423433 41463085849513522138067575)
  ·
    refine ⟨62194628774270283207101363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41463085849513522138067575 62194628774270283207101363)
    ·
      refine ⟨93291943161405424810652045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62194628774270283207101363 93291943161405424810652045)
      ·
        refine ⟨34984478685527034303994517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93291943161405424810652045 34984478685527034303994517)
        ·
          refine ⟨1639897438384079732999743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34984478685527034303994517 1639897438384079732999743)
          ·
            refine ⟨2459846157576119599499615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639897438384079732999743 2459846157576119599499615)
            ·
              refine ⟨3689769236364179399249423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2459846157576119599499615 3689769236364179399249423)
              ·
                refine ⟨5534653854546269098874135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3689769236364179399249423 5534653854546269098874135)
                ·
                  refine ⟨8301980781819403648311203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5534653854546269098874135 8301980781819403648311203)
                  ·
                    refine ⟨12452971172729105472466805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8301980781819403648311203 12452971172729105472466805)
                    ·
                      refine ⟨1167466047443353638043763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12452971172729105472466805 1167466047443353638043763)
                      ·
                        rfl

theorem cell23_2273632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_2273632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273632 prefixEnd_2273632 := by exact prefixLift 2273632
  have htrace : WordTrace (prefixWord ++ tailWord_2273632) baseStart_2273632 baseEnd_2273632 := by
    simpa [prefixWord, tailWord_2273632, baseEnd_2273632] using wordTrace_append hprefix tailTrace_2273632
  have hstable : (prefixWord ++ tailWord_2273632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273632).length < 2 ^ (prefixWord ++ tailWord_2273632).sum := by decide
  have hdescent : baseEnd_2273632 < baseStart_2273632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273668 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_2273668 : Nat := 118140960795 + 2273668 * 2 ^ 59
def prefixEnd_2273668 : Nat := 4983230072969 + 3 ^ 40 * 2273668 * 2
def baseEnd_2273668 : Nat := 1167484532746915497193597

theorem tailTrace_2273668 : CollatzResearch.WordTrace tailWord_2273668 prefixEnd_2273668 1167484532746915497193597 := by
  unfold tailWord_2273668
  simp only [CollatzResearch.WordTrace]
  refine ⟨41463742363448311212222829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55284989817931081616297105 41463742363448311212222829)
  ·
    refine ⟨15548903386293116704583561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41463742363448311212222829 15548903386293116704583561)
    ·
      refine ⟨11661677539719837528437671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15548903386293116704583561 11661677539719837528437671)
      ·
        refine ⟨17492516309579756292656507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11661677539719837528437671 17492516309579756292656507)
        ·
          refine ⟨26238774464369634438984761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17492516309579756292656507 26238774464369634438984761)
          ·
            refine ⟨19679080848277225829238571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26238774464369634438984761 19679080848277225829238571)
            ·
              refine ⟨29518621272415838743857857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19679080848277225829238571 29518621272415838743857857)
              ·
                refine ⟨22138965954311879057893393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29518621272415838743857857 22138965954311879057893393)
                ·
                  refine ⟨16604224465733909293420045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22138965954311879057893393 16604224465733909293420045)
                  ·
                    refine ⟨6226584174650215985032517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16604224465733909293420045 6226584174650215985032517)
                    ·
                      refine ⟨1167484532746915497193597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6226584174650215985032517 1167484532746915497193597)
                      ·
                        rfl

theorem cell23_2273668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_2273668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273668 prefixEnd_2273668 := by exact prefixLift 2273668
  have htrace : WordTrace (prefixWord ++ tailWord_2273668) baseStart_2273668 baseEnd_2273668 := by
    simpa [prefixWord, tailWord_2273668, baseEnd_2273668] using wordTrace_append hprefix tailTrace_2273668
  have hstable : (prefixWord ++ tailWord_2273668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273668).length < 2 ^ (prefixWord ++ tailWord_2273668).sum := by decide
  have hdescent : baseEnd_2273668 < baseStart_2273668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273672 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 1, 3, 2]
def baseStart_2273672 : Nat := 118140960795 + 2273672 * 2 ^ 59
def prefixEnd_2273672 : Nat := 4983230072969 + 3 ^ 40 * 2273672 * 2
def baseEnd_2273672 : Nat := 1167486586669533481543579

theorem tailTrace_2273672 : CollatzResearch.WordTrace tailWord_2273672 prefixEnd_2273672 1167486586669533481543579 := by
  unfold tailWord_2273672
  simp only [CollatzResearch.WordTrace]
  refine ⟨41463815309441065553795635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55285087079254754071727513 41463815309441065553795635)
  ·
    refine ⟨62195722964161598330693453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41463815309441065553795635 62195722964161598330693453)
    ·
      refine ⟨23323396111560599374010045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62195722964161598330693453 23323396111560599374010045)
      ·
        refine ⟨8746273541835224765253767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23323396111560599374010045 8746273541835224765253767)
        ·
          refine ⟨13119410312752837147880651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8746273541835224765253767 13119410312752837147880651)
          ·
            refine ⟨19679115469129255721820977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13119410312752837147880651 19679115469129255721820977)
            ·
              refine ⟨14759336601846941791365733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19679115469129255721820977 14759336601846941791365733)
              ·
                refine ⟨2767375612846301585881075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14759336601846941791365733 2767375612846301585881075)
                ·
                  refine ⟨4151063419269452378821613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767375612846301585881075 4151063419269452378821613)
                  ·
                    refine ⟨1556648782226044642058105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4151063419269452378821613 1556648782226044642058105)
                    ·
                      refine ⟨1167486586669533481543579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1556648782226044642058105 1167486586669533481543579)
                      ·
                        rfl

theorem cell23_2273672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_2273672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273672 prefixEnd_2273672 := by exact prefixLift 2273672
  have htrace : WordTrace (prefixWord ++ tailWord_2273672) baseStart_2273672 baseEnd_2273672 := by
    simpa [prefixWord, tailWord_2273672, baseEnd_2273672] using wordTrace_append hprefix tailTrace_2273672
  have hstable : (prefixWord ++ tailWord_2273672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273672).length < 2 ^ (prefixWord ++ tailWord_2273672).sum := by decide
  have hdescent : baseEnd_2273672 < baseStart_2273672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273738 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_2273738 : Nat := 118140960795 + 2273738 * 2 ^ 59
def prefixEnd_2273738 : Nat := 4983230072969 + 3 ^ 40 * 2273738 * 2
def baseEnd_2273738 : Nat := 389173492130910074439425

theorem tailTrace_2273738 : CollatzResearch.WordTrace tailWord_2273738 prefixEnd_2273738 389173492130910074439425 := by
  unfold tailWord_2273738
  simp only [CollatzResearch.WordTrace]
  refine ⟨20732509459160756094873467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55286691891095349586329245 20732509459160756094873467)
  ·
    refine ⟨31098764188741134142310201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20732509459160756094873467 31098764188741134142310201)
    ·
      refine ⟨23324073141555850606732651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31098764188741134142310201 23324073141555850606732651)
      ·
        refine ⟨34986109712333775910098977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23324073141555850606732651 34986109712333775910098977)
        ·
          refine ⟨26239582284250331932574233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34986109712333775910098977 26239582284250331932574233)
          ·
            refine ⟨19679686713187748949430675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26239582284250331932574233 19679686713187748949430675)
            ·
              refine ⟨29519530069781623424146013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19679686713187748949430675 29519530069781623424146013)
              ·
                refine ⟨11069823776168108784054755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29519530069781623424146013 11069823776168108784054755)
                ·
                  refine ⟨16604735664252163176082133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11069823776168108784054755 16604735664252163176082133)
                  ·
                    refine ⟨389173492130910074439425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16604735664252163176082133 389173492130910074439425)
                    ·
                      rfl

theorem cell23_2273738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_2273738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273738 prefixEnd_2273738 := by exact prefixLift 2273738
  have htrace : WordTrace (prefixWord ++ tailWord_2273738) baseStart_2273738 baseEnd_2273738 := by
    simpa [prefixWord, tailWord_2273738, baseEnd_2273738] using wordTrace_append hprefix tailTrace_2273738
  have hstable : (prefixWord ++ tailWord_2273738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273738).length < 2 ^ (prefixWord ++ tailWord_2273738).sum := by decide
  have hdescent : baseEnd_2273738 < baseStart_2273738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273775 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 1, 6, 2]
def baseStart_2273775 : Nat := 118140960795 + 2273775 * 2 ^ 59
def prefixEnd_2273775 : Nat := 4983230072969 + 3 ^ 40 * 2273775 * 2
def baseEnd_2273775 : Nat := 1167539475176946578555605

theorem tailTrace_2273775 : CollatzResearch.WordTrace tailWord_2273775 prefixEnd_2273775 1167539475176946578555605 := by
  unfold tailWord_2273775
  simp only [CollatzResearch.WordTrace]
  refine ⟨82931387337508979698590779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55287591558339319799060519 82931387337508979698590779)
  ·
    refine ⟨124397081006263469547886169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82931387337508979698590779 124397081006263469547886169)
    ·
      refine ⟨93297810754697602160914627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124397081006263469547886169 93297810754697602160914627)
      ·
        refine ⟨139946716132046403241371941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93297810754697602160914627 139946716132046403241371941)
        ·
          refine ⟨26240009274758700607757239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139946716132046403241371941 26240009274758700607757239)
          ·
            refine ⟨39360013912138050911635859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26240009274758700607757239 39360013912138050911635859)
            ·
              refine ⟨59040020868207076367453789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39360013912138050911635859 59040020868207076367453789)
              ·
                refine ⟨22140007825577653637795171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59040020868207076367453789 22140007825577653637795171)
                ·
                  refine ⟨33210011738366480456692757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22140007825577653637795171 33210011738366480456692757)
                  ·
                    refine ⟨1556719300235928771407473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33210011738366480456692757 1556719300235928771407473)
                    ·
                      refine ⟨1167539475176946578555605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1556719300235928771407473 1167539475176946578555605)
                      ·
                        rfl

theorem cell23_2273775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 6, 2].length) (baseStart_2273775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273775 prefixEnd_2273775 := by exact prefixLift 2273775
  have htrace : WordTrace (prefixWord ++ tailWord_2273775) baseStart_2273775 baseEnd_2273775 := by
    simpa [prefixWord, tailWord_2273775, baseEnd_2273775] using wordTrace_append hprefix tailTrace_2273775
  have hstable : (prefixWord ++ tailWord_2273775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273775).length < 2 ^ (prefixWord ++ tailWord_2273775).sum := by decide
  have hdescent : baseEnd_2273775 < baseStart_2273775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273785 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 3, 4]
def baseStart_2273785 : Nat := 118140960795 + 2273785 * 2 ^ 59
def prefixEnd_2273785 : Nat := 4983230072969 + 3 ^ 40 * 2273785 * 2
def baseEnd_2273785 : Nat := 389181536661163846476853

theorem tailTrace_2273785 : CollatzResearch.WordTrace tailWord_2273785 prefixEnd_2273785 389181536661163846476853 := by
  unfold tailWord_2273785
  simp only [CollatzResearch.WordTrace]
  refine ⟨82931752067472751406454809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55287834711648500937636539 82931752067472751406454809)
  ·
    refine ⟨62198814050604563554841107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82931752067472751406454809 62198814050604563554841107)
    ·
      refine ⟨93298221075906845332261661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62198814050604563554841107 93298221075906845332261661)
      ·
        refine ⟨34986832903465066999598123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93298221075906845332261661 34986832903465066999598123)
        ·
          refine ⟨52480249355197600499397185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34986832903465066999598123 52480249355197600499397185)
          ·
            refine ⟨39360187016398200374547889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52480249355197600499397185 39360187016398200374547889)
            ·
              refine ⟨29520140262298650280910917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39360187016398200374547889 29520140262298650280910917)
              ·
                refine ⟨5535026299180996927670797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29520140262298650280910917 5535026299180996927670797)
                ·
                  refine ⟨2075634862192873847876549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5535026299180996927670797 2075634862192873847876549)
                  ·
                    refine ⟨389181536661163846476853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2075634862192873847876549 389181536661163846476853)
                    ·
                      rfl

theorem cell23_2273785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 4].length) (baseStart_2273785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273785 prefixEnd_2273785 := by exact prefixLift 2273785
  have htrace : WordTrace (prefixWord ++ tailWord_2273785) baseStart_2273785 baseEnd_2273785 := by
    simpa [prefixWord, tailWord_2273785, baseEnd_2273785] using wordTrace_append hprefix tailTrace_2273785
  have hstable : (prefixWord ++ tailWord_2273785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273785).length < 2 ^ (prefixWord ++ tailWord_2273785).sum := by decide
  have hdescent : baseEnd_2273785 < baseStart_2273785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273788 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_2273788 : Nat := 118140960795 + 2273788 * 2 ^ 59
def prefixEnd_2273788 : Nat := 4983230072969 + 3 ^ 40 * 2273788 * 2
def baseEnd_2273788 : Nat := 1167546150425455027693045

theorem tailTrace_2273788 : CollatzResearch.WordTrace tailWord_2273788 prefixEnd_2273788 1167546150425455027693045 := by
  unfold tailWord_2273788
  simp only [CollatzResearch.WordTrace]
  refine ⟨41465930743230941459407009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55287907657641255279209345 41465930743230941459407009)
  ·
    refine ⟨31099448057423206094555257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41465930743230941459407009 31099448057423206094555257)
    ·
      refine ⟨23324586043067404570916443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31099448057423206094555257 23324586043067404570916443)
      ·
        refine ⟨34986879064601106856374665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23324586043067404570916443 34986879064601106856374665)
        ·
          refine ⟨26240159298450830142280999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34986879064601106856374665 26240159298450830142280999)
          ·
            refine ⟨39360238947676245213421499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26240159298450830142280999 39360238947676245213421499)
            ·
              refine ⟨59040358421514367820132249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39360238947676245213421499 59040358421514367820132249)
              ·
                refine ⟨44280268816135775865099187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59040358421514367820132249 44280268816135775865099187)
                ·
                  refine ⟨66420403224203663797648781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44280268816135775865099187 66420403224203663797648781)
                  ·
                    refine ⟨24907651209076373924118293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66420403224203663797648781 24907651209076373924118293)
                    ·
                      refine ⟨1167546150425455027693045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24907651209076373924118293 1167546150425455027693045)
                      ·
                        rfl

theorem cell23_2273788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_2273788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273788 prefixEnd_2273788 := by exact prefixLift 2273788
  have htrace : WordTrace (prefixWord ++ tailWord_2273788) baseStart_2273788 baseEnd_2273788 := by
    simpa [prefixWord, tailWord_2273788, baseEnd_2273788] using wordTrace_append hprefix tailTrace_2273788
  have hstable : (prefixWord ++ tailWord_2273788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273788).length < 2 ^ (prefixWord ++ tailWord_2273788).sum := by decide
  have hdescent : baseEnd_2273788 < baseStart_2273788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273832 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 6]
def baseStart_2273832 : Nat := 118140960795 + 2273832 * 2 ^ 59
def prefixEnd_2273832 : Nat := 4983230072969 + 3 ^ 40 * 2273832 * 2
def baseEnd_2273832 : Nat := 129729860397139206171427

theorem tailTrace_2273832 : CollatzResearch.WordTrace tailWord_2273832 prefixEnd_2273832 129729860397139206171427 := by
  unfold tailWord_2273832
  simp only [CollatzResearch.WordTrace]
  refine ⟨41466733149151239216707875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55288977532201652288943833 41466733149151239216707875)
  ·
    refine ⟨62200099723726858825061813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41466733149151239216707875 62200099723726858825061813)
    ·
      refine ⟨5831259349099393014849545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62200099723726858825061813 5831259349099393014849545)
      ·
        refine ⟨4373444511824544761137159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5831259349099393014849545 4373444511824544761137159)
        ·
          refine ⟨6560166767736817141705739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373444511824544761137159 6560166767736817141705739)
          ·
            refine ⟨9840250151605225712558609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560166767736817141705739 9840250151605225712558609)
            ·
              refine ⟨7380187613703919284418957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9840250151605225712558609 7380187613703919284418957)
              ·
                refine ⟨2767570355138969731657109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7380187613703919284418957 2767570355138969731657109)
                ·
                  refine ⟨129729860397139206171427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2767570355138969731657109 129729860397139206171427)
                  ·
                    rfl

theorem cell23_2273832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 6].length) (baseStart_2273832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273832 prefixEnd_2273832 := by exact prefixLift 2273832
  have htrace : WordTrace (prefixWord ++ tailWord_2273832) baseStart_2273832 baseEnd_2273832 := by
    simpa [prefixWord, tailWord_2273832, baseEnd_2273832] using wordTrace_append hprefix tailTrace_2273832
  have hstable : (prefixWord ++ tailWord_2273832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273832).length < 2 ^ (prefixWord ++ tailWord_2273832).sum := by decide
  have hdescent : baseEnd_2273832 < baseStart_2273832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273842 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_2273842 : Nat := 118140960795 + 2273842 * 2 ^ 59
def prefixEnd_2273842 : Nat := 4983230072969 + 3 ^ 40 * 2273842 * 2
def baseEnd_2273842 : Nat := 1167573878380797816417797

theorem tailTrace_2273842 : CollatzResearch.WordTrace tailWord_2273842 prefixEnd_2273842 1167573878380797816417797 := by
  unfold tailWord_2273842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20733457757066562535319945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55289220685510833427519853 20733457757066562535319945)
  ·
    refine ⟨15550093317799921901489959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20733457757066562535319945 15550093317799921901489959)
    ·
      refine ⟨23325139976699882852234939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15550093317799921901489959 23325139976699882852234939)
      ·
        refine ⟨34987709965049824278352409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23325139976699882852234939 34987709965049824278352409)
        ·
          refine ⟨26240782473787368208764307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34987709965049824278352409 26240782473787368208764307)
          ·
            refine ⟨39361173710681052313146461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26240782473787368208764307 39361173710681052313146461)
            ·
              refine ⟨14760440141505394617429923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39361173710681052313146461 14760440141505394617429923)
              ·
                refine ⟨22140660212258091926144885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14760440141505394617429923 22140660212258091926144885)
                ·
                  refine ⟨2075686894899196118076083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22140660212258091926144885 2075686894899196118076083)
                  ·
                    refine ⟨3113530342348794177114125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2075686894899196118076083 3113530342348794177114125)
                    ·
                      refine ⟨1167573878380797816417797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3113530342348794177114125 1167573878380797816417797)
                      ·
                        rfl

theorem cell23_2273842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_2273842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273842 prefixEnd_2273842 := by exact prefixLift 2273842
  have htrace : WordTrace (prefixWord ++ tailWord_2273842) baseStart_2273842 baseEnd_2273842 := by
    simpa [prefixWord, tailWord_2273842, baseEnd_2273842] using wordTrace_append hprefix tailTrace_2273842
  have hstable : (prefixWord ++ tailWord_2273842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273842).length < 2 ^ (prefixWord ++ tailWord_2273842).sum := by decide
  have hdescent : baseEnd_2273842 < baseStart_2273842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273845 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_2273845 : Nat := 118140960795 + 2273845 * 2 ^ 59
def prefixEnd_2273845 : Nat := 4983230072969 + 3 ^ 40 * 2273845 * 2
def baseEnd_2273845 : Nat := 389191806274253768226761

theorem tailTrace_2273845 : CollatzResearch.WordTrace tailWord_2273845 prefixEnd_2273845 389191806274253768226761 := by
  unfold tailWord_2273845
  simp only [CollatzResearch.WordTrace]
  refine ⟨82933940447255381653638989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55289293631503587769092659 82933940447255381653638989)
  ·
    refine ⟨31100227667720768120114621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82933940447255381653638989 31100227667720768120114621)
    ·
      refine ⟨11662585375395288045042983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31100227667720768120114621 11662585375395288045042983)
      ·
        refine ⟨17493878063092932067564475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11662585375395288045042983 17493878063092932067564475)
        ·
          refine ⟨26240817094639398101346713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17493878063092932067564475 26240817094639398101346713)
          ·
            refine ⟨19680612820979548576010035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26240817094639398101346713 19680612820979548576010035)
            ·
              refine ⟨29520919231469322864015053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19680612820979548576010035 29520919231469322864015053)
              ·
                refine ⟨11070344711800996074005645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29520919231469322864015053 11070344711800996074005645)
                ·
                  refine ⟨4151379266925373527752117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11070344711800996074005645 4151379266925373527752117)
                  ·
                    refine ⟨389191806274253768226761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4151379266925373527752117 389191806274253768226761)
                    ·
                      rfl

theorem cell23_2273845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_2273845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273845 prefixEnd_2273845 := by exact prefixLift 2273845
  have htrace : WordTrace (prefixWord ++ tailWord_2273845) baseStart_2273845 baseEnd_2273845 := by
    simpa [prefixWord, tailWord_2273845, baseEnd_2273845] using wordTrace_append hprefix tailTrace_2273845
  have hstable : (prefixWord ++ tailWord_2273845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273845).length < 2 ^ (prefixWord ++ tailWord_2273845).sum := by decide
  have hdescent : baseEnd_2273845 < baseStart_2273845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273846 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2273846 : Nat := 118140960795 + 2273846 * 2 ^ 59
def prefixEnd_2273846 : Nat := 4983230072969 + 3 ^ 40 * 2273846 * 2
def baseEnd_2273846 : Nat := 1167575932303415800767779

theorem tailTrace_2273846 : CollatzResearch.WordTrace tailWord_2273846 prefixEnd_2273846 1167575932303415800767779 := by
  unfold tailWord_2273846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5183373557515734926526587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55289317946834505882950261 5183373557515734926526587)
  ·
    refine ⟨7775060336273602389789881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5183373557515734926526587 7775060336273602389789881)
    ·
      refine ⟨5831295252205201792342411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7775060336273602389789881 5831295252205201792342411)
      ·
        refine ⟨8746942878307802688513617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5831295252205201792342411 8746942878307802688513617)
        ·
          refine ⟨6560207158730852016385213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8746942878307802688513617 6560207158730852016385213)
          ·
            refine ⟨2460077684524069506144455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6560207158730852016385213 2460077684524069506144455)
            ·
              refine ⟨3690116526786104259216683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460077684524069506144455 3690116526786104259216683)
              ·
                refine ⟨5535174790179156388825025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3690116526786104259216683 5535174790179156388825025)
                ·
                  refine ⟨4151381092634367291618769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5535174790179156388825025 4151381092634367291618769)
                  ·
                    refine ⟨3113535819475775468714077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4151381092634367291618769 3113535819475775468714077)
                    ·
                      refine ⟨1167575932303415800767779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3113535819475775468714077 1167575932303415800767779)
                      ·
                        rfl

theorem cell23_2273846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2273846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273846 prefixEnd_2273846 := by exact prefixLift 2273846
  have htrace : WordTrace (prefixWord ++ tailWord_2273846) baseStart_2273846 baseEnd_2273846 := by
    simpa [prefixWord, tailWord_2273846, baseEnd_2273846] using wordTrace_append hprefix tailTrace_2273846
  have hstable : (prefixWord ++ tailWord_2273846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273846).length < 2 ^ (prefixWord ++ tailWord_2273846).sum := by decide
  have hdescent : baseEnd_2273846 < baseStart_2273846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273876 : List Nat := [2, 4, 1, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_2273876 : Nat := 118140960795 + 2273876 * 2 ^ 59
def prefixEnd_2273876 : Nat := 4983230072969 + 3 ^ 40 * 2273876 * 2
def baseEnd_2273876 : Nat := 1167591336723050683392641

theorem tailTrace_2273876 : CollatzResearch.WordTrace tailWord_2273876 prefixEnd_2273876 1167591336723050683392641 := by
  unfold tailWord_2273876
  simp only [CollatzResearch.WordTrace]
  refine ⟨41467535555071536974008741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55290047406762049298678321 41467535555071536974008741)
  ·
    refine ⟨7775162916575913182626639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41467535555071536974008741 7775162916575913182626639)
    ·
      refine ⟨11662744374863869773939959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7775162916575913182626639 11662744374863869773939959)
      ·
        refine ⟨17494116562295804660909939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11662744374863869773939959 17494116562295804660909939)
        ·
          refine ⟨26241174843443706991364909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17494116562295804660909939 26241174843443706991364909)
          ·
            refine ⟨9840440566291390121761841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26241174843443706991364909 9840440566291390121761841)
            ·
              refine ⟨7380330424718542591321381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9840440566291390121761841 7380330424718542591321381)
              ·
                refine ⟨1383811954634726735872759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7380330424718542591321381 1383811954634726735872759)
                ·
                  refine ⟨2075717931952090103809139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383811954634726735872759 2075717931952090103809139)
                  ·
                    refine ⟨3113576897928135155713709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2075717931952090103809139 3113576897928135155713709)
                    ·
                      refine ⟨1167591336723050683392641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3113576897928135155713709 1167591336723050683392641)
                      ·
                        rfl

theorem cell23_2273876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_2273876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273876 prefixEnd_2273876 := by exact prefixLift 2273876
  have htrace : WordTrace (prefixWord ++ tailWord_2273876) baseStart_2273876 baseEnd_2273876 := by
    simpa [prefixWord, tailWord_2273876, baseEnd_2273876] using wordTrace_append hprefix tailTrace_2273876
  have hstable : (prefixWord ++ tailWord_2273876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273876).length < 2 ^ (prefixWord ++ tailWord_2273876).sum := by decide
  have hdescent : baseEnd_2273876 < baseStart_2273876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273910 : List Nat := [5, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_2273910 : Nat := 118140960795 + 2273910 * 2 ^ 59
def prefixEnd_2273910 : Nat := 4983230072969 + 3 ^ 40 * 2273910 * 2
def baseEnd_2273910 : Nat := 1167608795065303550367485

theorem tailTrace_2273910 : CollatzResearch.WordTrace tailWord_2273910 prefixEnd_2273910 1167608795065303550367485 := by
  unfold tailWord_2273910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5183519449501243609672199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55290874128013265169836789 5183519449501243609672199)
  ·
    refine ⟨7775279174251865414508299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5183519449501243609672199 7775279174251865414508299)
    ·
      refine ⟨11662918761377798121762449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7775279174251865414508299 11662918761377798121762449)
      ·
        refine ⟨8747189071033348591321837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11662918761377798121762449 8747189071033348591321837)
        ·
          refine ⟨3280195901637505721745689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8747189071033348591321837 3280195901637505721745689)
          ·
            refine ⟨2460146926228129291309267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3280195901637505721745689 2460146926228129291309267)
            ·
              refine ⟨3690220389342193936963901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460146926228129291309267 3690220389342193936963901)
              ·
                refine ⟨1383832646003322726361463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3690220389342193936963901 1383832646003322726361463)
                ·
                  refine ⟨2075748969004984089542195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383832646003322726361463 2075748969004984089542195)
                  ·
                    refine ⟨3113623453507476134313293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2075748969004984089542195 3113623453507476134313293)
                    ·
                      refine ⟨1167608795065303550367485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3113623453507476134313293 1167608795065303550367485)
                      ·
                        rfl

theorem cell23_2273910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_2273910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273910 prefixEnd_2273910 := by exact prefixLift 2273910
  have htrace : WordTrace (prefixWord ++ tailWord_2273910) baseStart_2273910 baseEnd_2273910 := by
    simpa [prefixWord, tailWord_2273910, baseEnd_2273910] using wordTrace_append hprefix tailTrace_2273910
  have hstable : (prefixWord ++ tailWord_2273910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273910).length < 2 ^ (prefixWord ++ tailWord_2273910).sum := by decide
  have hdescent : baseEnd_2273910 < baseStart_2273910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273953 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 1, 2, 3]
def baseStart_2273953 : Nat := 118140960795 + 2273953 * 2 ^ 59
def prefixEnd_2273953 : Nat := 4983230072969 + 3 ^ 40 * 2273953 * 2
def baseEnd_2273953 : Nat := 1167630874733446882129787

theorem tailTrace_2273953 : CollatzResearch.WordTrace tailWord_2273953 prefixEnd_2273953 1167630874733446882129787 := by
  unfold tailWord_2273953
  simp only [CollatzResearch.WordTrace]
  refine ⟨82937879530864116098570513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55291919687242744065713675 82937879530864116098570513)
  ·
    refine ⟨62203409648148087073927885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82937879530864116098570513 62203409648148087073927885)
    ·
      refine ⟨23326278618055532652722957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62203409648148087073927885 23326278618055532652722957)
      ·
        refine ⟨8747354481770824744771109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23326278618055532652722957 8747354481770824744771109)
        ·
          refine ⟨1640128965332029639644583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8747354481770824744771109 1640128965332029639644583)
          ·
            refine ⟨2460193447998044459466875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640128965332029639644583 2460193447998044459466875)
            ·
              refine ⟨3690290171997066689200313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460193447998044459466875 3690290171997066689200313)
              ·
                refine ⟨2767717628997800016900235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3690290171997066689200313 2767717628997800016900235)
                ·
                  refine ⟨4151576443496700025350353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767717628997800016900235 4151576443496700025350353)
                  ·
                    refine ⟨3113682332622525019012765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4151576443496700025350353 3113682332622525019012765)
                    ·
                      refine ⟨1167630874733446882129787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3113682332622525019012765 1167630874733446882129787)
                      ·
                        rfl

theorem cell23_2273953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_2273953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273953 prefixEnd_2273953 := by exact prefixLift 2273953
  have htrace : WordTrace (prefixWord ++ tailWord_2273953) baseStart_2273953 baseEnd_2273953 := by
    simpa [prefixWord, tailWord_2273953, baseEnd_2273953] using wordTrace_append hprefix tailTrace_2273953
  have hstable : (prefixWord ++ tailWord_2273953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273953).length < 2 ^ (prefixWord ++ tailWord_2273953).sum := by decide
  have hdescent : baseEnd_2273953 < baseStart_2273953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273955 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 4]
def baseStart_2273955 : Nat := 118140960795 + 2273955 * 2 ^ 59
def prefixEnd_2273955 : Nat := 4983230072969 + 3 ^ 40 * 2273955 * 2
def baseEnd_2273955 : Nat := 1167631901694755874304777

theorem tailTrace_2273955 : CollatzResearch.WordTrace tailWord_2273955 prefixEnd_2273955 1167631901694755874304777 := by
  unfold tailWord_2273955
  simp only [CollatzResearch.WordTrace]
  refine ⟨82937952476856870440143319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55291968317904580293428879 82937952476856870440143319)
  ·
    refine ⟨124406928715285305660214979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82937952476856870440143319 124406928715285305660214979)
    ·
      refine ⟨186610393072927958490322469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124406928715285305660214979 186610393072927958490322469)
      ·
        refine ⟨34989448701173992216935463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186610393072927958490322469 34989448701173992216935463)
        ·
          refine ⟨52484173051760988325403195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34989448701173992216935463 52484173051760988325403195)
          ·
            refine ⟨78726259577641482488104793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52484173051760988325403195 78726259577641482488104793)
            ·
              refine ⟨59044694683231111866078595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78726259577641482488104793 59044694683231111866078595)
              ·
                refine ⟨88567042024846667799117893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59044694683231111866078595 88567042024846667799117893)
                ·
                  refine ⟨16606320379658750212334605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88567042024846667799117893 16606320379658750212334605)
                  ·
                    refine ⟨6227370142372031329625477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16606320379658750212334605 6227370142372031329625477)
                    ·
                      refine ⟨1167631901694755874304777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6227370142372031329625477 1167631901694755874304777)
                      ·
                        rfl

theorem cell23_2273955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_2273955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273955 prefixEnd_2273955 := by exact prefixLift 2273955
  have htrace : WordTrace (prefixWord ++ tailWord_2273955) baseStart_2273955 baseEnd_2273955 := by
    simpa [prefixWord, tailWord_2273955, baseEnd_2273955] using wordTrace_append hprefix tailTrace_2273955
  have hstable : (prefixWord ++ tailWord_2273955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273955).length < 2 ^ (prefixWord ++ tailWord_2273955).sum := by decide
  have hdescent : baseEnd_2273955 < baseStart_2273955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273966 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2273966 : Nat := 118140960795 + 2273966 * 2 ^ 59
def prefixEnd_2273966 : Nat := 4983230072969 + 3 ^ 40 * 2273966 * 2
def baseEnd_2273966 : Nat := 1167637549981955331267227

theorem tailTrace_2273966 : CollatzResearch.WordTrace tailWord_2273966 prefixEnd_2273966 1167637549981955331267227 := by
  unfold tailWord_2273966
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367294209977127414849219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55292235786544679545862501 10367294209977127414849219)
  ·
    refine ⟨15550941314965691122273829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10367294209977127414849219 15550941314965691122273829)
    ·
      refine ⟨2915801496556067085426343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15550941314965691122273829 2915801496556067085426343)
      ·
        refine ⟨4373702244834100628139515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2915801496556067085426343 4373702244834100628139515)
        ·
          refine ⟨6560553367251150942209273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373702244834100628139515 6560553367251150942209273)
          ·
            refine ⟨4920415025438363206656955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6560553367251150942209273 4920415025438363206656955)
            ·
              refine ⟨7380622538157544809985433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4920415025438363206656955 7380622538157544809985433)
              ·
                refine ⟨5535466903618158607489075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7380622538157544809985433 5535466903618158607489075)
                ·
                  refine ⟨8303200355427237911233613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5535466903618158607489075 8303200355427237911233613)
                  ·
                    refine ⟨3113700133285214216712605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8303200355427237911233613 3113700133285214216712605)
                    ·
                      refine ⟨1167637549981955331267227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3113700133285214216712605 1167637549981955331267227)
                      ·
                        rfl

theorem cell23_2273966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2273966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273966 prefixEnd_2273966 := by exact prefixLift 2273966
  have htrace : WordTrace (prefixWord ++ tailWord_2273966) baseStart_2273966 baseEnd_2273966 := by
    simpa [prefixWord, tailWord_2273966, baseEnd_2273966] using wordTrace_append hprefix tailTrace_2273966
  have hstable : (prefixWord ++ tailWord_2273966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273966).length < 2 ^ (prefixWord ++ tailWord_2273966).sum := by decide
  have hdescent : baseEnd_2273966 < baseStart_2273966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273982 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_2273982 : Nat := 118140960795 + 2273982 * 2 ^ 59
def prefixEnd_2273982 : Nat := 4983230072969 + 3 ^ 40 * 2273982 * 2
def baseEnd_2273982 : Nat := 389215255224142422889051

theorem tailTrace_2273982 : CollatzResearch.WordTrace tailWord_2273982 prefixEnd_2273982 389215255224142422889051 := by
  unfold tailWord_2273982
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367367155969881756422025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55292624831839369367584133 10367367155969881756422025)
  ·
    refine ⟨7775525366977411317316519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10367367155969881756422025 7775525366977411317316519)
    ·
      refine ⟨11663288050466116975974779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7775525366977411317316519 11663288050466116975974779)
      ·
        refine ⟨17494932075699175463962169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11663288050466116975974779 17494932075699175463962169)
        ·
          refine ⟨13121199056774381597971627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17494932075699175463962169 13121199056774381597971627)
          ·
            refine ⟨19681798585161572396957441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13121199056774381597971627 19681798585161572396957441)
            ·
              refine ⟨14761348938871179297718081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19681798585161572396957441 14761348938871179297718081)
              ·
                refine ⟨11071011704153384473288561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14761348938871179297718081 11071011704153384473288561)
                ·
                  refine ⟨8303258778115038354966421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11071011704153384473288561 8303258778115038354966421)
                  ·
                    refine ⟨389215255224142422889051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8303258778115038354966421 389215255224142422889051)
                    ·
                      rfl

theorem cell23_2273982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_2273982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273982 prefixEnd_2273982 := by exact prefixLift 2273982
  have htrace : WordTrace (prefixWord ++ tailWord_2273982) baseStart_2273982 baseEnd_2273982 := by
    simpa [prefixWord, tailWord_2273982, baseEnd_2273982] using wordTrace_append hprefix tailTrace_2273982
  have hstable : (prefixWord ++ tailWord_2273982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273982).length < 2 ^ (prefixWord ++ tailWord_2273982).sum := by decide
  have hdescent : baseEnd_2273982 < baseStart_2273982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273992 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_2273992 : Nat := 118140960795 + 2273992 * 2 ^ 59
def prefixEnd_2273992 : Nat := 4983230072969 + 3 ^ 40 * 2273992 * 2
def baseEnd_2273992 : Nat := 1167650900478972229542107

theorem tailTrace_2273992 : CollatzResearch.WordTrace tailWord_2273992 prefixEnd_2273992 1167650900478972229542107 := by
  unfold tailWord_2273992
  simp only [CollatzResearch.WordTrace]
  refine ⟨41469650988861412879620115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55292867985148550506160153 41469650988861412879620115)
  ·
    refine ⟨62204476483292119319430173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41469650988861412879620115 62204476483292119319430173)
    ·
      refine ⟨23326678681234544744786315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62204476483292119319430173 23326678681234544744786315)
      ·
        refine ⟨34990018021851817117179473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23326678681234544744786315 34990018021851817117179473)
        ·
          refine ⟨26242513516388862837884605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34990018021851817117179473 26242513516388862837884605)
          ·
            refine ⟨9840942568645823564206727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26242513516388862837884605 9840942568645823564206727)
            ·
              refine ⟨14761413852968735346310091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9840942568645823564206727 14761413852968735346310091)
              ·
                refine ⟨22142120779453103019465137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14761413852968735346310091 22142120779453103019465137)
                ·
                  refine ⟨16606590584589827264598853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22142120779453103019465137 16606590584589827264598853)
                  ·
                    refine ⟨3113735734610592612112285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16606590584589827264598853 3113735734610592612112285)
                    ·
                      refine ⟨1167650900478972229542107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3113735734610592612112285 1167650900478972229542107)
                      ·
                        rfl

theorem cell23_2273992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_2273992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2273992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2273992 prefixEnd_2273992 := by exact prefixLift 2273992
  have htrace : WordTrace (prefixWord ++ tailWord_2273992) baseStart_2273992 baseEnd_2273992 := by
    simpa [prefixWord, tailWord_2273992, baseEnd_2273992] using wordTrace_append hprefix tailTrace_2273992
  have hstable : (prefixWord ++ tailWord_2273992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273992).length < 2 ^ (prefixWord ++ tailWord_2273992).sum := by decide
  have hdescent : baseEnd_2273992 < baseStart_2273992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274042 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_2274042 : Nat := 118140960795 + 2274042 * 2 ^ 59
def prefixEnd_2274042 : Nat := 4983230072969 + 3 ^ 40 * 2274042 * 2
def baseEnd_2274042 : Nat := 389225524837232344638959

theorem tailTrace_2274042 : CollatzResearch.WordTrace tailWord_2274042 prefixEnd_2274042 389225524837232344638959 := by
  unfold tailWord_2274042
  simp only [CollatzResearch.WordTrace]
  refine ⟨20735281406885421074640095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55294083751694456199040253 20735281406885421074640095)
  ·
    refine ⟨31102922110328131611960143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20735281406885421074640095 31102922110328131611960143)
    ·
      refine ⟨46654383165492197417940215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31102922110328131611960143 46654383165492197417940215)
      ·
        refine ⟨69981574748238296126910323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46654383165492197417940215 69981574748238296126910323)
        ·
          refine ⟨104972362122357444190365485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69981574748238296126910323 104972362122357444190365485)
          ·
            refine ⟨39364635795884041571387057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104972362122357444190365485 39364635795884041571387057)
            ·
              refine ⟨29523476846913031178540293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39364635795884041571387057 29523476846913031178540293)
              ·
                refine ⟨5535651908796193345976305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29523476846913031178540293 5535651908796193345976305)
                ·
                  refine ⟨4151738931597145009482229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5535651908796193345976305 4151738931597145009482229)
                  ·
                    refine ⟨389225524837232344638959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4151738931597145009482229 389225524837232344638959)
                    ·
                      rfl

theorem cell23_2274042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_2274042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274042 prefixEnd_2274042 := by exact prefixLift 2274042
  have htrace : WordTrace (prefixWord ++ tailWord_2274042) baseStart_2274042 baseEnd_2274042 := by
    simpa [prefixWord, tailWord_2274042, baseEnd_2274042] using wordTrace_append hprefix tailTrace_2274042
  have hstable : (prefixWord ++ tailWord_2274042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274042).length < 2 ^ (prefixWord ++ tailWord_2274042).sum := by decide
  have hdescent : baseEnd_2274042 < baseStart_2274042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274046 : List Nat := [4, 2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_2274046 : Nat := 118140960795 + 2274046 * 2 ^ 59
def prefixEnd_2274046 : Nat := 4983230072969 + 3 ^ 40 * 2274046 * 2
def baseEnd_2274046 : Nat := 129742069826035002029651

theorem tailTrace_2274046 : CollatzResearch.WordTrace tailWord_2274046 prefixEnd_2274046 129742069826035002029651 := by
  unfold tailWord_2274046
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367658939940899122713249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55294181013018128654470661 10367658939940899122713249)
  ·
    refine ⟨7775744204955674342034937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10367658939940899122713249 7775744204955674342034937)
    ·
      refine ⟨5831808153716755756526203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7775744204955674342034937 5831808153716755756526203)
      ·
        refine ⟨8747712230575133634789305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5831808153716755756526203 8747712230575133634789305)
        ·
          refine ⟨6560784172931350226091979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8747712230575133634789305 6560784172931350226091979)
          ·
            refine ⟨9841176259397025339137969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560784172931350226091979 9841176259397025339137969)
            ·
              refine ⟨7380882194547769004353477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9841176259397025339137969 7380882194547769004353477)
              ·
                refine ⟨1383915411477706688316277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7380882194547769004353477 1383915411477706688316277)
                ·
                  refine ⟨129742069826035002029651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1383915411477706688316277 129742069826035002029651)
                  ·
                    rfl

theorem cell23_2274046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_2274046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274046 prefixEnd_2274046 := by exact prefixLift 2274046
  have htrace : WordTrace (prefixWord ++ tailWord_2274046) baseStart_2274046 baseEnd_2274046 := by
    simpa [prefixWord, tailWord_2274046, baseEnd_2274046] using wordTrace_append hprefix tailTrace_2274046
  have hstable : (prefixWord ++ tailWord_2274046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274046).length < 2 ^ (prefixWord ++ tailWord_2274046).sum := by decide
  have hdescent : baseEnd_2274046 < baseStart_2274046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274052 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2274052 : Nat := 118140960795 + 2274052 * 2 ^ 59
def prefixEnd_2274052 : Nat := 4983230072969 + 3 ^ 40 * 2274052 * 2
def baseEnd_2274052 : Nat := 1167681709318241994791831

theorem tailTrace_2274052 : CollatzResearch.WordTrace tailWord_2274052 prefixEnd_2274052 1167681709318241994791831 := by
  unfold tailWord_2274052
  simp only [CollatzResearch.WordTrace]
  refine ⟨41470745178752728003212205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55294326905003637337616273 41470745178752728003212205)
  ·
    refine ⟨15551529442032273001204577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41470745178752728003212205 15551529442032273001204577)
    ·
      refine ⟨11663647081524204750903433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15551529442032273001204577 11663647081524204750903433)
      ·
        refine ⟨8747735311143153563177575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11663647081524204750903433 8747735311143153563177575)
        ·
          refine ⟨13121602966714730344766363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8747735311143153563177575 13121602966714730344766363)
          ·
            refine ⟨19682404450072095517149545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13121602966714730344766363 19682404450072095517149545)
            ·
              refine ⟨14761803337554071637862159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19682404450072095517149545 14761803337554071637862159)
              ·
                refine ⟨22142705006331107456793239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14761803337554071637862159 22142705006331107456793239)
                ·
                  refine ⟨33214057509496661185189859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22142705006331107456793239 33214057509496661185189859)
                  ·
                    refine ⟨49821086264244991777784789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33214057509496661185189859 49821086264244991777784789)
                    ·
                      refine ⟨1167681709318241994791831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49821086264244991777784789 1167681709318241994791831)
                      ·
                        rfl

theorem cell23_2274052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2274052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274052 prefixEnd_2274052 := by exact prefixLift 2274052
  have htrace : WordTrace (prefixWord ++ tailWord_2274052) baseStart_2274052 baseEnd_2274052 := by
    simpa [prefixWord, tailWord_2274052, baseEnd_2274052] using wordTrace_append hprefix tailTrace_2274052
  have hstable : (prefixWord ++ tailWord_2274052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274052).length < 2 ^ (prefixWord ++ tailWord_2274052).sum := by decide
  have hdescent : baseEnd_2274052 < baseStart_2274052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274093 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2274093 : Nat := 118140960795 + 2274093 * 2 ^ 59
def prefixEnd_2274093 : Nat := 4983230072969 + 3 ^ 40 * 2274093 * 2
def baseEnd_2274093 : Nat := 389234254008358778126381

theorem tailTrace_2274093 : CollatzResearch.WordTrace tailWord_2274093 prefixEnd_2274093 389234254008358778126381 := by
  unfold tailWord_2274093
  simp only [CollatzResearch.WordTrace]
  refine ⟨82942985750356920008666933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55295323833571280005777955 82942985750356920008666933)
  ·
    refine ⟨7775904914095961250812525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82942985750356920008666933 7775904914095961250812525)
    ·
      refine ⟨2915964342785985469054697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7775904914095961250812525 2915964342785985469054697)
      ·
        refine ⟨2186973257089489101791023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2915964342785985469054697 2186973257089489101791023)
        ·
          refine ⟨3280459885634233652686535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186973257089489101791023 3280459885634233652686535)
          ·
            refine ⟨4920689828451350479029803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3280459885634233652686535 4920689828451350479029803)
            ·
              refine ⟨7381034742677025718544705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4920689828451350479029803 7381034742677025718544705)
              ·
                refine ⟨5535776057007769288908529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7381034742677025718544705 5535776057007769288908529)
                ·
                  refine ⟨4151832042755826966681397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5535776057007769288908529 4151832042755826966681397)
                  ·
                    refine ⟨389234254008358778126381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4151832042755826966681397 389234254008358778126381)
                    ·
                      rfl

theorem cell23_2274093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2274093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274093 prefixEnd_2274093 := by exact prefixLift 2274093
  have htrace : WordTrace (prefixWord ++ tailWord_2274093) baseStart_2274093 baseEnd_2274093 := by
    simpa [prefixWord, tailWord_2274093, baseEnd_2274093] using wordTrace_append hprefix tailTrace_2274093
  have hstable : (prefixWord ++ tailWord_2274093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274093).length < 2 ^ (prefixWord ++ tailWord_2274093).sum := by decide
  have hdescent : baseEnd_2274093 < baseStart_2274093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274099 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 3]
def baseStart_2274099 : Nat := 118140960795 + 2274099 * 2 ^ 59
def prefixEnd_2274099 : Nat := 4983230072969 + 3 ^ 40 * 2274099 * 2
def baseEnd_2274099 : Nat := 1167705842909003310904115

theorem tailTrace_2274099 : CollatzResearch.WordTrace tailWord_2274099 prefixEnd_2274099 1167705842909003310904115 := by
  unfold tailWord_2274099
  simp only [CollatzResearch.WordTrace]
  refine ⟨82943204588335183033385351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55295469725556788688923567 82943204588335183033385351)
  ·
    refine ⟨124414806882502774550078027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82943204588335183033385351 124414806882502774550078027)
    ·
      refine ⟨186622210323754161825117041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124414806882502774550078027 186622210323754161825117041)
      ·
        refine ⟨139966657742815621368837781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186622210323754161825117041 139966657742815621368837781)
        ·
          refine ⟨6560937081694482251664271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139966657742815621368837781 6560937081694482251664271)
          ·
            refine ⟨9841405622541723377496407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560937081694482251664271 9841405622541723377496407)
            ·
              refine ⟨14762108433812585066244611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9841405622541723377496407 14762108433812585066244611)
              ·
                refine ⟨22143162650718877599366917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14762108433812585066244611 22143162650718877599366917)
                ·
                  refine ⟨4151842997009789549881297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22143162650718877599366917 4151842997009789549881297)
                  ·
                    refine ⟨3113882247757342162410973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4151842997009789549881297 3113882247757342162410973)
                    ·
                      refine ⟨1167705842909003310904115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3113882247757342162410973 1167705842909003310904115)
                      ·
                        rfl

theorem cell23_2274099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 3].length) (baseStart_2274099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274099 prefixEnd_2274099 := by exact prefixLift 2274099
  have htrace : WordTrace (prefixWord ++ tailWord_2274099) baseStart_2274099 baseEnd_2274099 := by
    simpa [prefixWord, tailWord_2274099, baseEnd_2274099] using wordTrace_append hprefix tailTrace_2274099
  have hstable : (prefixWord ++ tailWord_2274099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274099).length < 2 ^ (prefixWord ++ tailWord_2274099).sum := by decide
  have hdescent : baseEnd_2274099 < baseStart_2274099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274149 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 1, 5]
def baseStart_2274149 : Nat := 118140960795 + 2274149 * 2 ^ 59
def prefixEnd_2274149 : Nat := 4983230072969 + 3 ^ 40 * 2274149 * 2
def baseEnd_2274149 : Nat := 389243838980576038426295

theorem tailTrace_2274149 : CollatzResearch.WordTrace tailWord_2274149 prefixEnd_2274149 389243838980576038426295 := by
  unfold tailWord_2274149
  simp only [CollatzResearch.WordTrace]
  refine ⟨82945028238154041572705501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55296685492102694381803667 82945028238154041572705501)
  ·
    refine ⟨31104385589307765589764563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82945028238154041572705501 31104385589307765589764563)
    ·
      refine ⟨46656578383961648384646845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31104385589307765589764563 46656578383961648384646845)
      ·
        refine ⟨17496216893985618144242567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46656578383961648384646845 17496216893985618144242567)
        ·
          refine ⟨26244325340978427216363851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17496216893985618144242567 26244325340978427216363851)
          ·
            refine ⟨39366488011467640824545777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26244325340978427216363851 39366488011467640824545777)
            ·
              refine ⟨29524866008600730618409333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39366488011467640824545777 29524866008600730618409333)
              ·
                refine ⟨2767956188306318495475875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29524866008600730618409333 2767956188306318495475875)
                ·
                  refine ⟨4151934282459477743213813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767956188306318495475875 4151934282459477743213813)
                  ·
                    refine ⟨389243838980576038426295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4151934282459477743213813 389243838980576038426295)
                    ·
                      rfl

theorem cell23_2274149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_2274149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274149 prefixEnd_2274149 := by exact prefixLift 2274149
  have htrace : WordTrace (prefixWord ++ tailWord_2274149) baseStart_2274149 baseEnd_2274149 := by
    simpa [prefixWord, tailWord_2274149, baseEnd_2274149] using wordTrace_append hprefix tailTrace_2274149
  have hstable : (prefixWord ++ tailWord_2274149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274149).length < 2 ^ (prefixWord ++ tailWord_2274149).sum := by decide
  have hdescent : baseEnd_2274149 < baseStart_2274149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274156 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 2, 3, 2]
def baseStart_2274156 : Nat := 118140960795 + 2274156 * 2 ^ 59
def prefixEnd_2274156 : Nat := 4983230072969 + 3 ^ 40 * 2274156 * 2
def baseEnd_2274156 : Nat := 1167735111306309587891353

theorem tailTrace_2274156 : CollatzResearch.WordTrace tailWord_2274156 prefixEnd_2274156 1167735111306309587891353 := by
  unfold tailWord_2274156
  simp only [CollatzResearch.WordTrace]
  refine ⟨41472641774564340884105161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55296855699419121178806881 41472641774564340884105161)
  ·
    refine ⟨31104481330923255663078871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41472641774564340884105161 31104481330923255663078871)
    ·
      refine ⟨46656721996384883494618307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31104481330923255663078871 46656721996384883494618307)
      ·
        refine ⟨69985082994577325241927461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46656721996384883494618307 69985082994577325241927461)
        ·
          refine ⟨13122203061483248482861399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69985082994577325241927461 13122203061483248482861399)
          ·
            refine ⟨19683304592224872724292099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13122203061483248482861399 19683304592224872724292099)
            ·
              refine ⟨29524956888337309086438149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19683304592224872724292099 29524956888337309086438149)
              ·
                refine ⟨5535929416563245453707153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29524956888337309086438149 5535929416563245453707153)
                ·
                  refine ⟨4151947062422434090280365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5535929416563245453707153 4151947062422434090280365)
                  ·
                    refine ⟨1556980148408412783855137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4151947062422434090280365 1556980148408412783855137)
                    ·
                      refine ⟨1167735111306309587891353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1556980148408412783855137 1167735111306309587891353)
                      ·
                        rfl

theorem cell23_2274156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 3, 2].length) (baseStart_2274156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274156 prefixEnd_2274156 := by exact prefixLift 2274156
  have htrace : WordTrace (prefixWord ++ tailWord_2274156) baseStart_2274156 baseEnd_2274156 := by
    simpa [prefixWord, tailWord_2274156, baseEnd_2274156] using wordTrace_append hprefix tailTrace_2274156
  have hstable : (prefixWord ++ tailWord_2274156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274156).length < 2 ^ (prefixWord ++ tailWord_2274156).sum := by decide
  have hdescent : baseEnd_2274156 < baseStart_2274156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274166 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_2274166 : Nat := 118140960795 + 2274166 * 2 ^ 59
def prefixEnd_2274166 : Nat := 4983230072969 + 3 ^ 40 * 2274166 * 2
def baseEnd_2274166 : Nat := 389246748704284849588769

theorem tailTrace_2274166 : CollatzResearch.WordTrace tailWord_2274166 prefixEnd_2274166 389246748704284849588769 := by
  unfold tailWord_2274166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5184103017443278342254647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55297098852728302317382901 5184103017443278342254647)
  ·
    refine ⟨7776154526164917513381971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5184103017443278342254647 7776154526164917513381971)
    ·
      refine ⟨11664231789247376270072957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7776154526164917513381971 11664231789247376270072957)
      ·
        refine ⟨4374086920967766101277359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11664231789247376270072957 4374086920967766101277359)
        ·
          refine ⟨6561130381451649151916039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374086920967766101277359 6561130381451649151916039)
          ·
            refine ⟨9841695572177473727874059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6561130381451649151916039 9841695572177473727874059)
            ·
              refine ⟨14762543358266210591811089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9841695572177473727874059 14762543358266210591811089)
              ·
                refine ⟨11071907518699657943858317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14762543358266210591811089 11071907518699657943858317)
                ·
                  refine ⟨4151965319512371728946869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11071907518699657943858317 4151965319512371728946869)
                  ·
                    refine ⟨389246748704284849588769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4151965319512371728946869 389246748704284849588769)
                    ·
                      rfl

theorem cell23_2274166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_2274166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274166 prefixEnd_2274166 := by exact prefixLift 2274166
  have htrace : WordTrace (prefixWord ++ tailWord_2274166) baseStart_2274166 baseEnd_2274166 := by
    simpa [prefixWord, tailWord_2274166, baseEnd_2274166] using wordTrace_append hprefix tailTrace_2274166
  have hstable : (prefixWord ++ tailWord_2274166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274166).length < 2 ^ (prefixWord ++ tailWord_2274166).sum := by decide
  have hdescent : baseEnd_2274166 < baseStart_2274166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274169 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 4]
def baseStart_2274169 : Nat := 118140960795 + 2274169 * 2 ^ 59
def prefixEnd_2274169 : Nat := 4983230072969 + 3 ^ 40 * 2274169 * 2
def baseEnd_2274169 : Nat := 1167741786554818037028793

theorem tailTrace_2274169 : CollatzResearch.WordTrace tailWord_2274169 prefixEnd_2274169 1167741786554818037028793 := by
  unfold tailWord_2274169
  simp only [CollatzResearch.WordTrace]
  refine ⟨82945757698081584988433561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55297171798721056658955707 82945757698081584988433561)
  ·
    refine ⟨62209318273561188741325171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82945757698081584988433561 62209318273561188741325171)
    ·
      refine ⟨93313977410341783111987757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62209318273561188741325171 93313977410341783111987757)
      ·
        refine ⟨34992741528878168666995409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93313977410341783111987757 34992741528878168666995409)
        ·
          refine ⟨26244556146658626500246557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34992741528878168666995409 26244556146658626500246557)
          ·
            refine ⟨9841708554996984937592459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26244556146658626500246557 9841708554996984937592459)
            ·
              refine ⟨14762562832495477406388689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9841708554996984937592459 14762562832495477406388689)
              ·
                refine ⟨11071922124371608054791517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14762562832495477406388689 11071922124371608054791517)
                ·
                  refine ⟨4151970796639353020546819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11071922124371608054791517 4151970796639353020546819)
                  ·
                    refine ⟨6227956194959029530820229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4151970796639353020546819 6227956194959029530820229)
                    ·
                      refine ⟨1167741786554818037028793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6227956194959029530820229 1167741786554818037028793)
                      ·
                        rfl

theorem cell23_2274169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_2274169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274169 prefixEnd_2274169 := by exact prefixLift 2274169
  have htrace : WordTrace (prefixWord ++ tailWord_2274169) baseStart_2274169 baseEnd_2274169 := by
    simpa [prefixWord, tailWord_2274169, baseEnd_2274169] using wordTrace_append hprefix tailTrace_2274169
  have hstable : (prefixWord ++ tailWord_2274169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274169).length < 2 ^ (prefixWord ++ tailWord_2274169).sum := by decide
  have hdescent : baseEnd_2274169 < baseStart_2274169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274179 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 1, 6]
def baseStart_2274179 : Nat := 118140960795 + 2274179 * 2 ^ 59
def prefixEnd_2274179 : Nat := 4983230072969 + 3 ^ 40 * 2274179 * 2
def baseEnd_2274179 : Nat := 389248973787120999301249

theorem tailTrace_2274179 : CollatzResearch.WordTrace tailWord_2274179 prefixEnd_2274179 389248973787120999301249 := by
  unfold tailWord_2274179
  simp only [CollatzResearch.WordTrace]
  refine ⟨82946122428045356696297591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55297414952030237797531727 82946122428045356696297591)
  ·
    refine ⟨124419183642068035044446387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82946122428045356696297591 124419183642068035044446387)
    ·
      refine ⟨186628775463102052566669581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124419183642068035044446387 186628775463102052566669581)
      ·
        refine ⟨69985790798663269712501093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186628775463102052566669581 69985790798663269712501093)
        ·
          refine ⟨13122335774749363071093955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69985790798663269712501093 13122335774749363071093955)
          ·
            refine ⟨19683503662124044606640933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13122335774749363071093955 19683503662124044606640933)
            ·
              refine ⟨3690656936648258363745175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19683503662124044606640933 3690656936648258363745175)
              ·
                refine ⟨5535985404972387545617763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3690656936648258363745175 5535985404972387545617763)
                ·
                  refine ⟨8303978107458581318426645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5535985404972387545617763 8303978107458581318426645)
                  ·
                    refine ⟨389248973787120999301249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8303978107458581318426645 389248973787120999301249)
                    ·
                      rfl

theorem cell23_2274179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 6].length) (baseStart_2274179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274179 prefixEnd_2274179 := by exact prefixLift 2274179
  have htrace : WordTrace (prefixWord ++ tailWord_2274179) baseStart_2274179 baseEnd_2274179 := by
    simpa [prefixWord, tailWord_2274179, baseEnd_2274179] using wordTrace_append hprefix tailTrace_2274179
  have hstable : (prefixWord ++ tailWord_2274179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274179).length < 2 ^ (prefixWord ++ tailWord_2274179).sum := by decide
  have hdescent : baseEnd_2274179 < baseStart_2274179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274186 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2274186 : Nat := 118140960795 + 2274186 * 2 ^ 59
def prefixEnd_2274186 : Nat := 4983230072969 + 3 ^ 40 * 2274186 * 2
def baseEnd_2274186 : Nat := 1167750515725944470516215

theorem tailTrace_2274186 : CollatzResearch.WordTrace tailWord_2274186 prefixEnd_2274186 1167750515725944470516215 := by
  unfold tailWord_2274186
  simp only [CollatzResearch.WordTrace]
  refine ⟨20736594434754999222950603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55297585159346664594534941 20736594434754999222950603)
  ·
    refine ⟨31104891652132498834425905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20736594434754999222950603 31104891652132498834425905)
    ·
      refine ⟨23328668739099374125819429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31104891652132498834425905 23328668739099374125819429)
      ·
        refine ⟨4374125388581132648591143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23328668739099374125819429 4374125388581132648591143)
        ·
          refine ⟨6561188082871698972886715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374125388581132648591143 6561188082871698972886715)
          ·
            refine ⟨9841782124307548459330073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6561188082871698972886715 9841782124307548459330073)
            ·
              refine ⟨7381336593230661344497555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9841782124307548459330073 7381336593230661344497555)
              ·
                refine ⟨11072004889845992016746333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7381336593230661344497555 11072004889845992016746333)
                ·
                  refine ⟨4152001833692247006279875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11072004889845992016746333 4152001833692247006279875)
                  ·
                    refine ⟨6228002750538370509419813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4152001833692247006279875 6228002750538370509419813)
                    ·
                      refine ⟨1167750515725944470516215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6228002750538370509419813 1167750515725944470516215)
                      ·
                        rfl

theorem cell23_2274186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2274186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274186 prefixEnd_2274186 := by exact prefixLift 2274186
  have htrace : WordTrace (prefixWord ++ tailWord_2274186) baseStart_2274186 baseEnd_2274186 := by
    simpa [prefixWord, tailWord_2274186, baseEnd_2274186] using wordTrace_append hprefix tailTrace_2274186
  have hstable : (prefixWord ++ tailWord_2274186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274186).length < 2 ^ (prefixWord ++ tailWord_2274186).sum := by decide
  have hdescent : baseEnd_2274186 < baseStart_2274186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274196 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_2274196 : Nat := 118140960795 + 2274196 * 2 ^ 59
def prefixEnd_2274196 : Nat := 4983230072969 + 3 ^ 40 * 2274196 * 2
def baseEnd_2274196 : Nat := 389251883510829810463723

theorem tailTrace_2274196 : CollatzResearch.WordTrace tailWord_2274196 prefixEnd_2274196 389251883510829810463723 := by
  unfold tailWord_2274196
  simp only [CollatzResearch.WordTrace]
  refine ⟨41473371234491884299833221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55297828312655845733110961 41473371234491884299833221)
  ·
    refine ⟨7776257106467228306218729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41473371234491884299833221 7776257106467228306218729)
    ·
      refine ⟨5832192829850421229664047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7776257106467228306218729 5832192829850421229664047)
      ·
        refine ⟨8748289244775631844496071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5832192829850421229664047 8748289244775631844496071)
        ·
          refine ⟨13122433867163447766744107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8748289244775631844496071 13122433867163447766744107)
          ·
            refine ⟨19683650800745171650116161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13122433867163447766744107 19683650800745171650116161)
            ·
              refine ⟨14762738100558878737587121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19683650800745171650116161 14762738100558878737587121)
              ·
                refine ⟨11072053575419159053190341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14762738100558878737587121 11072053575419159053190341)
                ·
                  refine ⟨2076010045391092322473189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11072053575419159053190341 2076010045391092322473189)
                  ·
                    refine ⟨389251883510829810463723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2076010045391092322473189 389251883510829810463723)
                    ·
                      rfl

theorem cell23_2274196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_2274196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274196 prefixEnd_2274196 := by exact prefixLift 2274196
  have htrace : WordTrace (prefixWord ++ tailWord_2274196) baseStart_2274196 baseEnd_2274196 := by
    simpa [prefixWord, tailWord_2274196, baseEnd_2274196] using wordTrace_append hprefix tailTrace_2274196
  have hstable : (prefixWord ++ tailWord_2274196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274196).length < 2 ^ (prefixWord ++ tailWord_2274196).sum := by decide
  have hdescent : baseEnd_2274196 < baseStart_2274196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274199 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_2274199 : Nat := 118140960795 + 2274199 * 2 ^ 59
def prefixEnd_2274199 : Nat := 4983230072969 + 3 ^ 40 * 2274199 * 2
def baseEnd_2274199 : Nat := 1167757190974452919653655

theorem tailTrace_2274199 : CollatzResearch.WordTrace tailWord_2274199 prefixEnd_2274199 1167757190974452919653655 := by
  unfold tailWord_2274199
  simp only [CollatzResearch.WordTrace]
  refine ⟨82946851887972900112025651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55297901258648600074683767 82946851887972900112025651)
  ·
    refine ⟨124420277831959350168038477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82946851887972900112025651 124420277831959350168038477)
    ·
      refine ⟨46657604186984756313014429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124420277831959350168038477 46657604186984756313014429)
      ·
        refine ⟨17496601570119283617380411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46657604186984756313014429 17496601570119283617380411)
        ·
          refine ⟨26244902355178925426070617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17496601570119283617380411 26244902355178925426070617)
          ·
            refine ⟨19683676766384194069552963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26244902355178925426070617 19683676766384194069552963)
            ·
              refine ⟨29525515149576291104329445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19683676766384194069552963 29525515149576291104329445)
              ·
                refine ⟨5536034090545554582061771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29525515149576291104329445 5536034090545554582061771)
                ·
                  refine ⟨8304051135818331873092657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5536034090545554582061771 8304051135818331873092657)
                  ·
                    refine ⟨6228038351863748904819493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8304051135818331873092657 6228038351863748904819493)
                    ·
                      refine ⟨1167757190974452919653655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6228038351863748904819493 1167757190974452919653655)
                      ·
                        rfl

theorem cell23_2274199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_2274199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274199 prefixEnd_2274199 := by exact prefixLift 2274199
  have htrace : WordTrace (prefixWord ++ tailWord_2274199) baseStart_2274199 baseEnd_2274199 := by
    simpa [prefixWord, tailWord_2274199, baseEnd_2274199] using wordTrace_append hprefix tailTrace_2274199
  have hstable : (prefixWord ++ tailWord_2274199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274199).length < 2 ^ (prefixWord ++ tailWord_2274199).sum := by decide
  have hdescent : baseEnd_2274199 < baseStart_2274199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274209 : List Nat := [1, 2, 3, 4, 1, 2, 10]
def baseStart_2274209 : Nat := 118140960795 + 2274209 * 2 ^ 59
def prefixEnd_2274209 : Nat := 4983230072969 + 3 ^ 40 * 2274209 * 2
def baseEnd_2274209 : Nat := 14416818836802442969489

theorem tailTrace_2274209 : CollatzResearch.WordTrace tailWord_2274209 prefixEnd_2274209 14416818836802442969489 := by
  unfold tailWord_2274209
  simp only [CollatzResearch.WordTrace]
  refine ⟨82947216617936671819889681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55298144411957781213259787 82947216617936671819889681)
  ·
    refine ⟨62210412463452503864917261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82947216617936671819889681 62210412463452503864917261)
    ·
      refine ⟨23328904673794688949343973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62210412463452503864917261 23328904673794688949343973)
      ·
        refine ⟨4374169626336504178001995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23328904673794688949343973 4374169626336504178001995)
        ·
          refine ⟨6561254439504756267002993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374169626336504178001995 6561254439504756267002993)
          ·
            refine ⟨4920940829628567200252245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6561254439504756267002993 4920940829628567200252245)
            ·
              refine ⟨14416818836802442969489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4920940829628567200252245 14416818836802442969489)
              ·
                rfl

theorem cell23_2274209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 10].length) (baseStart_2274209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274209 prefixEnd_2274209 := by exact prefixLift 2274209
  have htrace : WordTrace (prefixWord ++ tailWord_2274209) baseStart_2274209 baseEnd_2274209 := by
    simpa [prefixWord, tailWord_2274209, baseEnd_2274209] using wordTrace_append hprefix tailTrace_2274209
  have hstable : (prefixWord ++ tailWord_2274209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274209).length < 2 ^ (prefixWord ++ tailWord_2274209).sum := by decide
  have hdescent : baseEnd_2274209 < baseStart_2274209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274276 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 5, 4, 2]
def baseStart_2274276 : Nat := 118140960795 + 2274276 * 2 ^ 59
def prefixEnd_2274276 : Nat := 4983230072969 + 3 ^ 40 * 2274276 * 2
def baseEnd_2274276 : Nat := 1167796728984849118390801

theorem tailTrace_2274276 : CollatzResearch.WordTrace tailWord_2274276 prefixEnd_2274276 1167796728984849118390801 := by
  unfold tailWord_2274276
  simp only [CollatzResearch.WordTrace]
  refine ⟨41474830154346971131289341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55299773539129294841719121 41474830154346971131289341)
  ·
    refine ⟨15553061307880114174233503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41474830154346971131289341 15553061307880114174233503)
    ·
      refine ⟨23329591961820171261350255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15553061307880114174233503 23329591961820171261350255)
      ·
        refine ⟨34994387942730256892025383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23329591961820171261350255 34994387942730256892025383)
        ·
          refine ⟨52491581914095385338038075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34994387942730256892025383 52491581914095385338038075)
          ·
            refine ⟨78737372871143078007057113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52491581914095385338038075 78737372871143078007057113)
            ·
              refine ⟨59053029653357308505292835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78737372871143078007057113 59053029653357308505292835)
              ·
                refine ⟨88579544480035962757939253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59053029653357308505292835 88579544480035962757939253)
                ·
                  refine ⟨8304332295003371508556805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88579544480035962757939253 8304332295003371508556805)
                  ·
                    refine ⟨1557062305313132157854401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8304332295003371508556805 1557062305313132157854401)
                    ·
                      refine ⟨1167796728984849118390801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1557062305313132157854401 1167796728984849118390801)
                      ·
                        rfl

theorem cell23_2274276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_2274276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274276 prefixEnd_2274276 := by exact prefixLift 2274276
  have htrace : WordTrace (prefixWord ++ tailWord_2274276) baseStart_2274276 baseEnd_2274276 := by
    simpa [prefixWord, tailWord_2274276, baseEnd_2274276] using wordTrace_append hprefix tailTrace_2274276
  have hstable : (prefixWord ++ tailWord_2274276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274276).length < 2 ^ (prefixWord ++ tailWord_2274276).sum := by decide
  have hdescent : baseEnd_2274276 < baseStart_2274276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274327 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 2, 2, 2]
def baseStart_2274327 : Nat := 118140960795 + 2274327 * 2 ^ 59
def prefixEnd_2274327 : Nat := 4983230072969 + 3 ^ 40 * 2274327 * 2
def baseEnd_2274327 : Nat := 1167822916498228418853067

theorem tailTrace_2274327 : CollatzResearch.WordTrace tailWord_2274327 prefixEnd_2274327 1167822916498228418853067 := by
  unfold tailWord_2274327
  simp only [CollatzResearch.WordTrace]
  refine ⟨82951520431509177972685235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55301013621006118648456823 82951520431509177972685235)
  ·
    refine ⟨124427280647263766959027853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82951520431509177972685235 124427280647263766959027853)
    ·
      refine ⟨46660230242723912609635445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124427280647263766959027853 46660230242723912609635445)
      ·
        refine ⟨4374396585255366807153323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46660230242723912609635445 4374396585255366807153323)
        ·
          refine ⟨6561594877883050210729985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374396585255366807153323 6561594877883050210729985)
          ·
            refine ⟨4921196158412287658047489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6561594877883050210729985 4921196158412287658047489)
            ·
              refine ⟨3690897118809215743535617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4921196158412287658047489 3690897118809215743535617)
              ·
                refine ⟨2768172839106911807651713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3690897118809215743535617 2768172839106911807651713)
                ·
                  refine ⟨2076129629330183855738785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2768172839106911807651713 2076129629330183855738785)
                  ·
                    refine ⟨1557097221997637891804089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2076129629330183855738785 1557097221997637891804089)
                    ·
                      refine ⟨1167822916498228418853067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1557097221997637891804089 1167822916498228418853067)
                      ·
                        rfl

theorem cell23_2274327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_2274327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274327 prefixEnd_2274327 := by exact prefixLift 2274327
  have htrace : WordTrace (prefixWord ++ tailWord_2274327) baseStart_2274327 baseEnd_2274327 := by
    simpa [prefixWord, tailWord_2274327, baseEnd_2274327] using wordTrace_append hprefix tailTrace_2274327
  have hstable : (prefixWord ++ tailWord_2274327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274327).length < 2 ^ (prefixWord ++ tailWord_2274327).sum := by decide
  have hdescent : baseEnd_2274327 < baseStart_2274327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274343 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2274343 : Nat := 118140960795 + 2274343 * 2 ^ 59
def prefixEnd_2274343 : Nat := 4983230072969 + 3 ^ 40 * 2274343 * 2
def baseEnd_2274343 : Nat := 1167831132188700356252993

theorem tailTrace_2274343 : CollatzResearch.WordTrace tailWord_2274343 prefixEnd_2274343 1167831132188700356252993 := by
  unfold tailWord_2274343
  simp only [CollatzResearch.WordTrace]
  refine ⟨82952103999451212705267683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55301402666300808470178455 82952103999451212705267683)
  ·
    refine ⟨124428155999176819057901525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82952103999451212705267683 124428155999176819057901525)
    ·
      refine ⟨2916284906230706696669567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 124428155999176819057901525 2916284906230706696669567)
      ·
        refine ⟨4374427359346060045004351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2916284906230706696669567 4374427359346060045004351)
        ·
          refine ⟨6561641039019090067506527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374427359346060045004351 6561641039019090067506527)
          ·
            refine ⟨9842461558528635101259791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6561641039019090067506527 9842461558528635101259791)
            ·
              refine ⟨14763692337792952651889687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9842461558528635101259791 14763692337792952651889687)
              ·
                refine ⟨22145538506689428977834531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14763692337792952651889687 22145538506689428977834531)
                ·
                  refine ⟨33218307760034143466751797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22145538506689428977834531 33218307760034143466751797)
                  ·
                    refine ⟨3114216352503200950007981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33218307760034143466751797 3114216352503200950007981)
                    ·
                      refine ⟨1167831132188700356252993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3114216352503200950007981 1167831132188700356252993)
                      ·
                        rfl

theorem cell23_2274343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2274343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274343 prefixEnd_2274343 := by exact prefixLift 2274343
  have htrace : WordTrace (prefixWord ++ tailWord_2274343) baseStart_2274343 baseEnd_2274343 := by
    simpa [prefixWord, tailWord_2274343, baseEnd_2274343] using wordTrace_append hprefix tailTrace_2274343
  have hstable : (prefixWord ++ tailWord_2274343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274343).length < 2 ^ (prefixWord ++ tailWord_2274343).sum := by decide
  have hdescent : baseEnd_2274343 < baseStart_2274343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274376 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 5, 4]
def baseStart_2274376 : Nat := 118140960795 + 2274376 * 2 ^ 59
def prefixEnd_2274376 : Nat := 4983230072969 + 3 ^ 40 * 2274376 * 2
def baseEnd_2274376 : Nat := 389282692350099575713447

theorem tailTrace_2274376 : CollatzResearch.WordTrace tailWord_2274376 prefixEnd_2274376 389282692350099575713447 := by
  unfold tailWord_2274376
  simp only [CollatzResearch.WordTrace]
  refine ⟨41476653804165829670609491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55302205072221106227479321 41476653804165829670609491)
  ·
    refine ⟨62214980706248744505914237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41476653804165829670609491 62214980706248744505914237)
    ·
      refine ⟨23330617764843279189717839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62214980706248744505914237 23330617764843279189717839)
      ·
        refine ⟨34995926647264918784576759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23330617764843279189717839 34995926647264918784576759)
        ·
          refine ⟨52493889970897378176865139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34995926647264918784576759 52493889970897378176865139)
          ·
            refine ⟨78740834956346067265297709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52493889970897378176865139 78740834956346067265297709)
            ·
              refine ⟨29527813108629775224486641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78740834956346067265297709 29527813108629775224486641)
              ·
                refine ⟨22145859831472331418364981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29527813108629775224486641 22145859831472331418364981)
                ·
                  refine ⟨2076174359200531070471717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22145859831472331418364981 2076174359200531070471717)
                  ·
                    refine ⟨389282692350099575713447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2076174359200531070471717 389282692350099575713447)
                    ·
                      rfl

theorem cell23_2274376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_2274376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274376 prefixEnd_2274376 := by exact prefixLift 2274376
  have htrace : WordTrace (prefixWord ++ tailWord_2274376) baseStart_2274376 baseEnd_2274376 := by
    simpa [prefixWord, tailWord_2274376, baseEnd_2274376] using wordTrace_append hprefix tailTrace_2274376
  have hstable : (prefixWord ++ tailWord_2274376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274376).length < 2 ^ (prefixWord ++ tailWord_2274376).sum := by decide
  have hdescent : baseEnd_2274376 < baseStart_2274376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274396 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2274396 : Nat := 118140960795 + 2274396 * 2 ^ 59
def prefixEnd_2274396 : Nat := 4983230072969 + 3 ^ 40 * 2274396 * 2
def baseEnd_2274396 : Nat := 1167858346663388648890249

theorem tailTrace_2274396 : CollatzResearch.WordTrace tailWord_2274396 prefixEnd_2274396 1167858346663388648890249 := by
  unfold tailWord_2274396
  simp only [CollatzResearch.WordTrace]
  refine ⟨41477018534129601378473521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55302691378839468504631361 41477018534129601378473521)
  ·
    refine ⟨31107763900597201033855141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41477018534129601378473521 31107763900597201033855141)
    ·
      refine ⟨5832705731361975193847839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31107763900597201033855141 5832705731361975193847839)
      ·
        refine ⟨8749058597042962790771759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5832705731361975193847839 8749058597042962790771759)
        ·
          refine ⟨13123587895564444186157639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8749058597042962790771759 13123587895564444186157639)
          ·
            refine ⟨19685381843346666279236459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13123587895564444186157639 19685381843346666279236459)
            ·
              refine ⟨29528072765019999418854689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19685381843346666279236459 29528072765019999418854689)
              ·
                refine ⟨22146054573764999564141017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29528072765019999418854689 22146054573764999564141017)
                ·
                  refine ⟨16609540930323749673105763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22146054573764999564141017 16609540930323749673105763)
                  ·
                    refine ⟨24914311395485624509658645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16609540930323749673105763 24914311395485624509658645)
                    ·
                      refine ⟨1167858346663388648890249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24914311395485624509658645 1167858346663388648890249)
                      ·
                        rfl

theorem cell23_2274396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2274396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274396 prefixEnd_2274396 := by exact prefixLift 2274396
  have htrace : WordTrace (prefixWord ++ tailWord_2274396) baseStart_2274396 baseEnd_2274396 := by
    simpa [prefixWord, tailWord_2274396, baseEnd_2274396] using wordTrace_append hprefix tailTrace_2274396
  have hstable : (prefixWord ++ tailWord_2274396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274396).length < 2 ^ (prefixWord ++ tailWord_2274396).sum := by decide
  have hdescent : baseEnd_2274396 < baseStart_2274396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274416 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 3]
def baseStart_2274416 : Nat := 118140960795 + 2274416 * 2 ^ 59
def prefixEnd_2274416 : Nat := 4983230072969 + 3 ^ 40 * 2274416 * 2
def baseEnd_2274416 : Nat := 1167868616276478570640157

theorem tailTrace_2274416 : CollatzResearch.WordTrace tailWord_2274416 prefixEnd_2274416 1167868616276478570640157 := by
  unfold tailWord_2274416
  simp only [CollatzResearch.WordTrace]
  refine ⟨41477383264093373086337551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55303177685457830781783401 41477383264093373086337551)
  ·
    refine ⟨62216074896140059629506327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41477383264093373086337551 62216074896140059629506327)
    ·
      refine ⟨93324112344210089444259491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62216074896140059629506327 93324112344210089444259491)
      ·
        refine ⟨139986168516315134166389237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93324112344210089444259491 139986168516315134166389237)
        ·
          refine ⟨13123703298404543828098991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139986168516315134166389237 13123703298404543828098991)
          ·
            refine ⟨19685554947606815742148487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13123703298404543828098991 19685554947606815742148487)
            ·
              refine ⟨29528332421410223613222731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19685554947606815742148487 29528332421410223613222731)
              ·
                refine ⟨44292498632115335419834097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29528332421410223613222731 44292498632115335419834097)
                ·
                  refine ⟨33219373974086501564875573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44292498632115335419834097 33219373974086501564875573)
                  ·
                    refine ⟨3114316310070609521707085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33219373974086501564875573 3114316310070609521707085)
                    ·
                      refine ⟨1167868616276478570640157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3114316310070609521707085 1167868616276478570640157)
                      ·
                        rfl

theorem cell23_2274416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 3].length) (baseStart_2274416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274416 prefixEnd_2274416 := by exact prefixLift 2274416
  have htrace : WordTrace (prefixWord ++ tailWord_2274416) baseStart_2274416 baseEnd_2274416 := by
    simpa [prefixWord, tailWord_2274416, baseEnd_2274416] using wordTrace_append hprefix tailTrace_2274416
  have hstable : (prefixWord ++ tailWord_2274416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274416).length < 2 ^ (prefixWord ++ tailWord_2274416).sum := by decide
  have hdescent : baseEnd_2274416 < baseStart_2274416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274419 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 4, 9]
def baseStart_2274419 : Nat := 118140960795 + 2274419 * 2 ^ 59
def prefixEnd_2274419 : Nat := 4983230072969 + 3 ^ 40 * 2274419 * 2
def baseEnd_2274419 : Nat := 389290052239480686300881

theorem tailTrace_2274419 : CollatzResearch.WordTrace tailWord_2274419 prefixEnd_2274419 389290052239480686300881 := by
  unfold tailWord_2274419
  simp only [CollatzResearch.WordTrace]
  refine ⟨82954875947175877685034311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55303250631450585123356207 82954875947175877685034311)
  ·
    refine ⟨124432313920763816527551467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82954875947175877685034311 124432313920763816527551467)
    ·
      refine ⟨186648470881145724791327201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124432313920763816527551467 186648470881145724791327201)
      ·
        refine ⟨139986353160859293593495401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186648470881145724791327201 139986353160859293593495401)
        ·
          refine ⟨104989764870644470195121551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139986353160859293593495401 104989764870644470195121551)
          ·
            refine ⟨157484647305966705292682327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104989764870644470195121551 157484647305966705292682327)
            ·
              refine ⟨236226970958950057939023491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157484647305966705292682327 236226970958950057939023491)
              ·
                refine ⟨354340456438425086908535237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236226970958950057939023491 354340456438425086908535237)
                ·
                  refine ⟨66438835582204703795350357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354340456438425086908535237 66438835582204703795350357)
                  ·
                    refine ⟨389290052239480686300881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 66438835582204703795350357 389290052239480686300881)
                    ·
                      rfl

theorem cell23_2274419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 9].length) (baseStart_2274419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274419 prefixEnd_2274419 := by exact prefixLift 2274419
  have htrace : WordTrace (prefixWord ++ tailWord_2274419) baseStart_2274419 baseEnd_2274419 := by
    simpa [prefixWord, tailWord_2274419, baseEnd_2274419] using wordTrace_append hprefix tailTrace_2274419
  have hstable : (prefixWord ++ tailWord_2274419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274419).length < 2 ^ (prefixWord ++ tailWord_2274419).sum := by decide
  have hdescent : baseEnd_2274419 < baseStart_2274419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274493 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_2274493 : Nat := 118140960795 + 2274493 * 2 ^ 59
def prefixEnd_2274493 : Nat := 4983230072969 + 3 ^ 40 * 2274493 * 2
def baseEnd_2274493 : Nat := 1167908154286874769377303

theorem tailTrace_2274493 : CollatzResearch.WordTrace tailWord_2274493 prefixEnd_2274493 1167908154286874769377303 := by
  unfold tailWord_2274493
  simp only [CollatzResearch.WordTrace]
  refine ⟨82957574948907788323228133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55305049965938525548818755 82957574948907788323228133)
  ·
    refine ⟨15554545302920210310605275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82957574948907788323228133 15554545302920210310605275)
    ·
      refine ⟨23331817954380315465907913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15554545302920210310605275 23331817954380315465907913)
      ·
        refine ⟨17498863465785236599430935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23331817954380315465907913 17498863465785236599430935)
        ·
          refine ⟨26248295198677854899146403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17498863465785236599430935 26248295198677854899146403)
          ·
            refine ⟨39372442798016782348719605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26248295198677854899146403 39372442798016782348719605)
            ·
              refine ⟨3691166512314073345192463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39372442798016782348719605 3691166512314073345192463)
              ·
                refine ⟨5536749768471110017788695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691166512314073345192463 5536749768471110017788695)
                ·
                  refine ⟨8305124652706665026683043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5536749768471110017788695 8305124652706665026683043)
                  ·
                    refine ⟨12457686979059997540024565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8305124652706665026683043 12457686979059997540024565)
                    ·
                      refine ⟨1167908154286874769377303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12457686979059997540024565 1167908154286874769377303)
                      ·
                        rfl

theorem cell23_2274493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_2274493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274493 prefixEnd_2274493 := by exact prefixLift 2274493
  have htrace : WordTrace (prefixWord ++ tailWord_2274493) baseStart_2274493 baseEnd_2274493 := by
    simpa [prefixWord, tailWord_2274493, baseEnd_2274493] using wordTrace_append hprefix tailTrace_2274493
  have hstable : (prefixWord ++ tailWord_2274493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274493).length < 2 ^ (prefixWord ++ tailWord_2274493).sum := by decide
  have hdescent : baseEnd_2274493 < baseStart_2274493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274496 : List Nat := [2, 1, 1, 2, 6, 11]
def baseStart_2274496 : Nat := 118140960795 + 2274496 * 2 ^ 59
def prefixEnd_2274496 : Nat := 4983230072969 + 3 ^ 40 * 2274496 * 2
def baseEnd_2274496 : Nat := 4806212735509622459423

theorem tailTrace_2274496 : CollatzResearch.WordTrace tailWord_2274496 prefixEnd_2274496 4806212735509622459423 := by
  unfold tailWord_2274496
  simp only [CollatzResearch.WordTrace]
  refine ⟨41478842183948459917793671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55305122911931279890391561 41478842183948459917793671)
  ·
    refine ⟨62218263275922689876690507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41478842183948459917793671 62218263275922689876690507)
    ·
      refine ⟨93327394913884034815035761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62218263275922689876690507 93327394913884034815035761)
      ·
        refine ⟨69995546185413026111276821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93327394913884034815035761 69995546185413026111276821)
        ·
          refine ⟨3281041227441235598966101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69995546185413026111276821 3281041227441235598966101)
          ·
            refine ⟨4806212735509622459423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3281041227441235598966101 4806212735509622459423)
            ·
              rfl

theorem cell23_2274496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 11].length) (baseStart_2274496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274496 prefixEnd_2274496 := by exact prefixLift 2274496
  have htrace : WordTrace (prefixWord ++ tailWord_2274496) baseStart_2274496 baseEnd_2274496 := by
    simpa [prefixWord, tailWord_2274496, baseEnd_2274496] using wordTrace_append hprefix tailTrace_2274496
  have hstable : (prefixWord ++ tailWord_2274496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274496).length < 2 ^ (prefixWord ++ tailWord_2274496).sum := by decide
  have hdescent : baseEnd_2274496 < baseStart_2274496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274520 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 1, 2, 4]
def baseStart_2274520 : Nat := 118140960795 + 2274520 * 2 ^ 59
def prefixEnd_2274520 : Nat := 4983230072969 + 3 ^ 40 * 2274520 * 2
def baseEnd_2274520 : Nat := 1167922018264546163739679

theorem tailTrace_2274520 : CollatzResearch.WordTrace tailWord_2274520 prefixEnd_2274520 1167922018264546163739679 := by
  unfold tailWord_2274520
  simp only [CollatzResearch.WordTrace]
  refine ⟨41479279859904985967230507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55305706479873314622974009 41479279859904985967230507)
  ·
    refine ⟨62218919789857478950845761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41479279859904985967230507 62218919789857478950845761)
    ·
      refine ⟨46664189842393109213134321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62218919789857478950845761 46664189842393109213134321)
      ·
        refine ⟨34998142381794831909850741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46664189842393109213134321 34998142381794831909850741)
        ·
          refine ⟨3281075848293265491548507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34998142381794831909850741 3281075848293265491548507)
          ·
            refine ⟨4921613772439898237322761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281075848293265491548507 4921613772439898237322761)
            ·
              refine ⟨3691210329329923677992071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4921613772439898237322761 3691210329329923677992071)
              ·
                refine ⟨5536815493994885516988107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691210329329923677992071 5536815493994885516988107)
                ·
                  refine ⟨8305223240992328275482161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5536815493994885516988107 8305223240992328275482161)
                  ·
                    refine ⟨6228917430744246206611621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8305223240992328275482161 6228917430744246206611621)
                    ·
                      refine ⟨1167922018264546163739679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6228917430744246206611621 1167922018264546163739679)
                      ·
                        rfl

theorem cell23_2274520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_2274520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274520 prefixEnd_2274520 := by exact prefixLift 2274520
  have htrace : WordTrace (prefixWord ++ tailWord_2274520) baseStart_2274520 baseEnd_2274520 := by
    simpa [prefixWord, tailWord_2274520, baseEnd_2274520] using wordTrace_append hprefix tailTrace_2274520
  have hstable : (prefixWord ++ tailWord_2274520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274520).length < 2 ^ (prefixWord ++ tailWord_2274520).sum := by decide
  have hdescent : baseEnd_2274520 < baseStart_2274520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274541 : List Nat := [1, 5, 1, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_2274541 : Nat := 118140960795 + 2274541 * 2 ^ 59
def prefixEnd_2274541 : Nat := 4983230072969 + 3 ^ 40 * 2274541 * 2
def baseEnd_2274541 : Nat := 1167932801358290581577083

theorem tailTrace_2274541 : CollatzResearch.WordTrace tailWord_2274541 prefixEnd_2274541 1167932801358290581577083 := by
  unfold tailWord_2274541
  simp only [CollatzResearch.WordTrace]
  refine ⟨82959325652733892520975477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55306217101822595013983651 82959325652733892520975477)
  ·
    refine ⟨7777436779943802423841451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82959325652733892520975477 7777436779943802423841451)
    ·
      refine ⟨11666155169915703635762177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7777436779943802423841451 11666155169915703635762177)
      ·
        refine ⟨8749616377436777726821633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11666155169915703635762177 8749616377436777726821633)
        ·
          refine ⟨6562212283077583295116225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8749616377436777726821633 6562212283077583295116225)
          ·
            refine ⟨4921659212308187471337169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6562212283077583295116225 4921659212308187471337169)
            ·
              refine ⟨3691244409231140603502877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4921659212308187471337169 3691244409231140603502877)
              ·
                refine ⟨1384216653461677726313579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3691244409231140603502877 1384216653461677726313579)
                ·
                  refine ⟨2076324980192516589470369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1384216653461677726313579 2076324980192516589470369)
                  ·
                    refine ⟨1557243735144387442102777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2076324980192516589470369 1557243735144387442102777)
                    ·
                      refine ⟨1167932801358290581577083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1557243735144387442102777 1167932801358290581577083)
                      ·
                        rfl

theorem cell23_2274541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_2274541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274541 prefixEnd_2274541 := by exact prefixLift 2274541
  have htrace : WordTrace (prefixWord ++ tailWord_2274541) baseStart_2274541 baseEnd_2274541 := by
    simpa [prefixWord, tailWord_2274541, baseEnd_2274541] using wordTrace_append hprefix tailTrace_2274541
  have hstable : (prefixWord ++ tailWord_2274541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274541).length < 2 ^ (prefixWord ++ tailWord_2274541).sum := by decide
  have hdescent : baseEnd_2274541 < baseStart_2274541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274574 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3]
def baseStart_2274574 : Nat := 118140960795 + 2274574 * 2 ^ 59
def prefixEnd_2274574 : Nat := 4983230072969 + 3 ^ 40 * 2274574 * 2
def baseEnd_2274574 : Nat := 1167949746219888952464431

theorem tailTrace_2274574 : CollatzResearch.WordTrace tailWord_2274574 prefixEnd_2274574 1167949746219888952464431 := by
  unfold tailWord_2274574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10370066157701792394615847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55307019507742892771284517 10370066157701792394615847)
  ·
    refine ⟨15555099236552688591923771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10370066157701792394615847 15555099236552688591923771)
    ·
      refine ⟨23332648854829032887885657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15555099236552688591923771 23332648854829032887885657)
      ·
        refine ⟨17499486641121774665914243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23332648854829032887885657 17499486641121774665914243)
        ·
          refine ⟨26249229961682661998871365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17499486641121774665914243 26249229961682661998871365)
          ·
            refine ⟨4921730617815499124788381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26249229961682661998871365 4921730617815499124788381)
            ·
              refine ⟨1845648981680812171795643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4921730617815499124788381 1845648981680812171795643)
              ·
                refine ⟨2768473472521218257693465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845648981680812171795643 2768473472521218257693465)
                ·
                  refine ⟨2076355104390913693270099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2768473472521218257693465 2076355104390913693270099)
                  ·
                    refine ⟨3114532656586370539905149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2076355104390913693270099 3114532656586370539905149)
                    ·
                      refine ⟨1167949746219888952464431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3114532656586370539905149 1167949746219888952464431)
                      ·
                        rfl

theorem cell23_2274574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_2274574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274574 prefixEnd_2274574 := by exact prefixLift 2274574
  have htrace : WordTrace (prefixWord ++ tailWord_2274574) baseStart_2274574 baseEnd_2274574 := by
    simpa [prefixWord, tailWord_2274574, baseEnd_2274574] using wordTrace_append hprefix tailTrace_2274574
  have hstable : (prefixWord ++ tailWord_2274574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274574).length < 2 ^ (prefixWord ++ tailWord_2274574).sum := by decide
  have hdescent : baseEnd_2274574 < baseStart_2274574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274583 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2274583 : Nat := 118140960795 + 2274583 * 2 ^ 59
def prefixEnd_2274583 : Nat := 4983230072969 + 3 ^ 40 * 2274583 * 2
def baseEnd_2274583 : Nat := 1167954367545779417251889

theorem tailTrace_2274583 : CollatzResearch.WordTrace tailWord_2274583 prefixEnd_2274583 1167954367545779417251889 := by
  unfold tailWord_2274583
  simp only [CollatzResearch.WordTrace]
  refine ⟨82960857518581733694004403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55307238345721155796002935 82960857518581733694004403)
  ·
    refine ⟨124441286277872600541006605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82960857518581733694004403 124441286277872600541006605)
    ·
      refine ⟨46665482354202225202877477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124441286277872600541006605 46665482354202225202877477)
      ·
        refine ⟨8749777941412917225539527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46665482354202225202877477 8749777941412917225539527)
        ·
          refine ⟨13124666912119375838309291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8749777941412917225539527 13124666912119375838309291)
          ·
            refine ⟨19687000368179063757463937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13124666912119375838309291 19687000368179063757463937)
            ·
              refine ⟨14765250276134297818097953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19687000368179063757463937 14765250276134297818097953)
              ·
                refine ⟨11073937707100723363573465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14765250276134297818097953 11073937707100723363573465)
                ·
                  refine ⟨8305453280325542522680099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11073937707100723363573465 8305453280325542522680099)
                  ·
                    refine ⟨12458179920488313784020149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8305453280325542522680099 12458179920488313784020149)
                    ·
                      refine ⟨1167954367545779417251889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12458179920488313784020149 1167954367545779417251889)
                      ·
                        rfl

theorem cell23_2274583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2274583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274583 prefixEnd_2274583 := by exact prefixLift 2274583
  have htrace : WordTrace (prefixWord ++ tailWord_2274583) baseStart_2274583 baseEnd_2274583 := by
    simpa [prefixWord, tailWord_2274583, baseEnd_2274583] using wordTrace_append hprefix tailTrace_2274583
  have hstable : (prefixWord ++ tailWord_2274583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274583).length < 2 ^ (prefixWord ++ tailWord_2274583).sum := by decide
  have hdescent : baseEnd_2274583 < baseStart_2274583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274597 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 4, 2, 2]
def baseStart_2274597 : Nat := 118140960795 + 2274597 * 2 ^ 59
def prefixEnd_2274597 : Nat := 4983230072969 + 3 ^ 40 * 2274597 * 2
def baseEnd_2274597 : Nat := 1167961556274942362476825

theorem tailTrace_2274597 : CollatzResearch.WordTrace tailWord_2274597 prefixEnd_2274597 1167961556274942362476825 := by
  unfold tailWord_2274597
  simp only [CollatzResearch.WordTrace]
  refine ⟨82961368140531014085014045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55307578760354009390009363 82961368140531014085014045)
  ·
    refine ⟨31110513052699130281880267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82961368140531014085014045 31110513052699130281880267)
    ·
      refine ⟨46665769579048695422820401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31110513052699130281880267 46665769579048695422820401)
      ·
        refine ⟨34999327184286521567115301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46665769579048695422820401 34999327184286521567115301)
        ·
          refine ⟨6562373847053722793834119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34999327184286521567115301 6562373847053722793834119)
          ·
            refine ⟨9843560770580584190751179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6562373847053722793834119 9843560770580584190751179)
            ·
              refine ⟨14765341155870876286126769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9843560770580584190751179 14765341155870876286126769)
              ·
                refine ⟨11074005866903157214595077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14765341155870876286126769 11074005866903157214595077)
                ·
                  refine ⟨2076376100044341977736577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11074005866903157214595077 2076376100044341977736577)
                  ·
                    refine ⟨1557282075033256483302433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2076376100044341977736577 1557282075033256483302433)
                    ·
                      refine ⟨1167961556274942362476825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1557282075033256483302433 1167961556274942362476825)
                      ·
                        rfl

theorem cell23_2274597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_2274597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274597 prefixEnd_2274597 := by exact prefixLift 2274597
  have htrace : WordTrace (prefixWord ++ tailWord_2274597) baseStart_2274597 baseEnd_2274597 := by
    simpa [prefixWord, tailWord_2274597, baseEnd_2274597] using wordTrace_append hprefix tailTrace_2274597
  have hstable : (prefixWord ++ tailWord_2274597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274597).length < 2 ^ (prefixWord ++ tailWord_2274597).sum := by decide
  have hdescent : baseEnd_2274597 < baseStart_2274597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274600 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2274600 : Nat := 118140960795 + 2274600 * 2 ^ 59
def prefixEnd_2274600 : Nat := 4983230072969 + 3 ^ 40 * 2274600 * 2
def baseEnd_2274600 : Nat := 1167963096716905850739311

theorem tailTrace_2274600 : CollatzResearch.WordTrace tailWord_2274600 prefixEnd_2274600 1167963096716905850739311 := by
  unfold tailWord_2274600
  simp only [CollatzResearch.WordTrace]
  refine ⟨41480738779760072798686627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55307651706346763731582169 41480738779760072798686627)
  ·
    refine ⟨62221108169640109198029941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41480738779760072798686627 62221108169640109198029941)
    ·
      refine ⟨5833228890903760237315307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62221108169640109198029941 5833228890903760237315307)
      ·
        refine ⟨8749843336355640355972961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5833228890903760237315307 8749843336355640355972961)
        ·
          refine ⟨6562382502266730266979721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8749843336355640355972961 6562382502266730266979721)
          ·
            refine ⟨4921786876700047700234791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6562382502266730266979721 4921786876700047700234791)
            ·
              refine ⟨7382680315050071550352187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921786876700047700234791 7382680315050071550352187)
              ·
                refine ⟨11074020472575107325528281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7382680315050071550352187 11074020472575107325528281)
                ·
                  refine ⟨8305515354431330494146211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11074020472575107325528281 8305515354431330494146211)
                  ·
                    refine ⟨12458273031646995741219317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8305515354431330494146211 12458273031646995741219317)
                    ·
                      refine ⟨1167963096716905850739311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12458273031646995741219317 1167963096716905850739311)
                      ·
                        rfl

theorem cell23_2274600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2274600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274600 prefixEnd_2274600 := by exact prefixLift 2274600
  have htrace : WordTrace (prefixWord ++ tailWord_2274600) baseStart_2274600 baseEnd_2274600 := by
    simpa [prefixWord, tailWord_2274600, baseEnd_2274600] using wordTrace_append hprefix tailTrace_2274600
  have hstable : (prefixWord ++ tailWord_2274600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274600).length < 2 ^ (prefixWord ++ tailWord_2274600).sum := by decide
  have hdescent : baseEnd_2274600 < baseStart_2274600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274620 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 7]
def baseStart_2274620 : Nat := 118140960795 + 2274620 * 2 ^ 59
def prefixEnd_2274620 : Nat := 4983230072969 + 3 ^ 40 * 2274620 * 2
def baseEnd_2274620 : Nat := 129774818481110641387691

theorem tailTrace_2274620 : CollatzResearch.WordTrace tailWord_2274620 prefixEnd_2274620 129774818481110641387691 := by
  unfold tailWord_2274620
  simp only [CollatzResearch.WordTrace]
  refine ⟨41481103509723844506550657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55308138012965126008734209 41481103509723844506550657)
  ·
    refine ⟨31110827632292883379912993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41481103509723844506550657 31110827632292883379912993)
    ·
      refine ⟨23333120724219662534934745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31110827632292883379912993 23333120724219662534934745)
      ·
        refine ⟨17499840543164746901201059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23333120724219662534934745 17499840543164746901201059)
        ·
          refine ⟨26249760814747120351801589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17499840543164746901201059 26249760814747120351801589)
          ·
            refine ⟨2460915076382542532981399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26249760814747120351801589 2460915076382542532981399)
            ·
              refine ⟨3691372614573813799472099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460915076382542532981399 3691372614573813799472099)
              ·
                refine ⟨5537058921860720699208149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691372614573813799472099 5537058921860720699208149)
                ·
                  refine ⟨129774818481110641387691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5537058921860720699208149 129774818481110641387691)
                  ·
                    rfl

theorem cell23_2274620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_2274620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274620 prefixEnd_2274620 := by exact prefixLift 2274620
  have htrace : WordTrace (prefixWord ++ tailWord_2274620) baseStart_2274620 baseEnd_2274620 := by
    simpa [prefixWord, tailWord_2274620, baseEnd_2274620] using wordTrace_append hprefix tailTrace_2274620
  have hstable : (prefixWord ++ tailWord_2274620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274620).length < 2 ^ (prefixWord ++ tailWord_2274620).sum := by decide
  have hdescent : baseEnd_2274620 < baseStart_2274620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274631 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 2, 2, 2]
def baseStart_2274631 : Nat := 118140960795 + 2274631 * 2 ^ 59
def prefixEnd_2274631 : Nat := 4983230072969 + 3 ^ 40 * 2274631 * 2
def baseEnd_2274631 : Nat := 1167979014617195229451669

theorem tailTrace_2274631 : CollatzResearch.WordTrace tailWord_2274631 prefixEnd_2274631 1167979014617195229451669 := by
  unfold tailWord_2274631
  simp only [CollatzResearch.WordTrace]
  refine ⟨82962608222407837891751747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55308405481605225261167831 82962608222407837891751747)
  ·
    refine ⟨124443912333611756837627621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82962608222407837891751747 124443912333611756837627621)
    ·
      refine ⟨23333233562552204407055179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124443912333611756837627621 23333233562552204407055179)
      ·
        refine ⟨34999850343828306610582769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23333233562552204407055179 34999850343828306610582769)
        ·
          refine ⟨26249887757871229957937077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34999850343828306610582769 26249887757871229957937077)
          ·
            refine ⟨2460926977300427808556601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26249887757871229957937077 2460926977300427808556601)
            ·
              refine ⟨1845695232975320856417451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2460926977300427808556601 1845695232975320856417451)
              ·
                refine ⟨2768542849462981284626177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845695232975320856417451 2768542849462981284626177)
                ·
                  refine ⟨2076407137097235963469633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2768542849462981284626177 2076407137097235963469633)
                  ·
                    refine ⟨1557305352822926972602225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2076407137097235963469633 1557305352822926972602225)
                    ·
                      refine ⟨1167979014617195229451669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1557305352822926972602225 1167979014617195229451669)
                      ·
                        rfl

theorem cell23_2274631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_2274631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274631 prefixEnd_2274631 := by exact prefixLift 2274631
  have htrace : WordTrace (prefixWord ++ tailWord_2274631) baseStart_2274631 baseEnd_2274631 := by
    simpa [prefixWord, tailWord_2274631, baseEnd_2274631] using wordTrace_append hprefix tailTrace_2274631
  have hstable : (prefixWord ++ tailWord_2274631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274631).length < 2 ^ (prefixWord ++ tailWord_2274631).sum := by decide
  have hdescent : baseEnd_2274631 < baseStart_2274631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274697 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 3, 4]
def baseStart_2274697 : Nat := 118140960795 + 2274697 * 2 ^ 59
def prefixEnd_2274697 : Nat := 4983230072969 + 3 ^ 40 * 2274697 * 2
def baseEnd_2274697 : Nat := 389337634780130657075455

theorem tailTrace_2274697 : CollatzResearch.WordTrace tailWord_2274697 prefixEnd_2274697 389337634780130657075455 := by
  unfold tailWord_2274697
  simp only [CollatzResearch.WordTrace]
  refine ⟨82965015440168731163654345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55310010293445820775769563 82965015440168731163654345)
  ·
    refine ⟨62223761580126548372740759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82965015440168731163654345 62223761580126548372740759)
    ·
      refine ⟨93335642370189822559111139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62223761580126548372740759 93335642370189822559111139)
      ·
        refine ⟨140003463555284733838666709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93335642370189822559111139 140003463555284733838666709)
        ·
          refine ⟨3281331177076985949343751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 140003463555284733838666709 3281331177076985949343751)
          ·
            refine ⟨4921996765615478924015627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281331177076985949343751 4921996765615478924015627)
            ·
              refine ⟨7382995148423218386023441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921996765615478924015627 7382995148423218386023441)
              ·
                refine ⟨5537246361317413789517581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7382995148423218386023441 5537246361317413789517581)
                ·
                  refine ⟨2076467385494030171069093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5537246361317413789517581 2076467385494030171069093)
                  ·
                    refine ⟨389337634780130657075455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2076467385494030171069093 389337634780130657075455)
                    ·
                      rfl

theorem cell23_2274697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 4].length) (baseStart_2274697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274697 prefixEnd_2274697 := by exact prefixLift 2274697
  have htrace : WordTrace (prefixWord ++ tailWord_2274697) baseStart_2274697 baseEnd_2274697 := by
    simpa [prefixWord, tailWord_2274697, baseEnd_2274697] using wordTrace_append hprefix tailTrace_2274697
  have hstable : (prefixWord ++ tailWord_2274697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274697).length < 2 ^ (prefixWord ++ tailWord_2274697).sum := by decide
  have hdescent : baseEnd_2274697 < baseStart_2274697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274714 : List Nat := [3, 1, 1, 4, 1, 1, 4, 3, 1, 4]
def baseStart_2274714 : Nat := 118140960795 + 2274714 * 2 ^ 59
def prefixEnd_2274714 : Nat := 4983230072969 + 3 ^ 40 * 2274714 * 2
def baseEnd_2274714 : Nat := 389340544503839468237929

theorem tailTrace_2274714 : CollatzResearch.WordTrace tailWord_2274714 prefixEnd_2274714 389340544503839468237929 := by
  unfold tailWord_2274714
  simp only [CollatzResearch.WordTrace]
  refine ⟨20741408870276785766755799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55310423654071428711348797 20741408870276785766755799)
  ·
    refine ⟨31112113305415178650133699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20741408870276785766755799 31112113305415178650133699)
    ·
      refine ⟨46668169958122767975200549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31112113305415178650133699 46668169958122767975200549)
      ·
        refine ⟨8750281867148018995350103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46668169958122767975200549 8750281867148018995350103)
        ·
          refine ⟨13125422800722028493025155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8750281867148018995350103 13125422800722028493025155)
          ·
            refine ⟨19688134201083042739537733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13125422800722028493025155 19688134201083042739537733)
            ·
              refine ⟨3691525162703070513663325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19688134201083042739537733 3691525162703070513663325)
              ·
                refine ⟨1384321936013651442623747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3691525162703070513663325 1384321936013651442623747)
                ·
                  refine ⟨2076482904020477163935621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1384321936013651442623747 2076482904020477163935621)
                  ·
                    refine ⟨389340544503839468237929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2076482904020477163935621 389340544503839468237929)
                    ·
                      rfl

theorem cell23_2274714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_2274714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274714 prefixEnd_2274714 := by exact prefixLift 2274714
  have htrace : WordTrace (prefixWord ++ tailWord_2274714) baseStart_2274714 baseEnd_2274714 := by
    simpa [prefixWord, tailWord_2274714, baseEnd_2274714] using wordTrace_append hprefix tailTrace_2274714
  have hstable : (prefixWord ++ tailWord_2274714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274714).length < 2 ^ (prefixWord ++ tailWord_2274714).sum := by decide
  have hdescent : baseEnd_2274714 < baseStart_2274714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274774 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2274774 : Nat := 118140960795 + 2274774 * 2 ^ 59
def prefixEnd_2274774 : Nat := 4983230072969 + 3 ^ 40 * 2274774 * 2
def baseEnd_2274774 : Nat := 389350814116929389987837

theorem tailTrace_2274774 : CollatzResearch.WordTrace tailWord_2274774 prefixEnd_2274774 389350814116929389987837 := by
  unfold tailWord_2274774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5185488991305610832137961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55311882573926515542804917 5185488991305610832137961)
  ·
    refine ⟨3889116743479208124103471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5185488991305610832137961 3889116743479208124103471)
    ·
      refine ⟨5833675115218812186155207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3889116743479208124103471 5833675115218812186155207)
      ·
        refine ⟨8750512672828218279232811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5833675115218812186155207 8750512672828218279232811)
        ·
          refine ⟨13125769009242327418849217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8750512672828218279232811 13125769009242327418849217)
          ·
            refine ⟨9844326756931745564136913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13125769009242327418849217 9844326756931745564136913)
            ·
              refine ⟨7383245067698809173102685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9844326756931745564136913 7383245067698809173102685)
              ·
                refine ⟨2768716900387053439913507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7383245067698809173102685 2768716900387053439913507)
                ·
                  refine ⟨4153075350580580159870261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768716900387053439913507 4153075350580580159870261)
                  ·
                    refine ⟨389350814116929389987837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4153075350580580159870261 389350814116929389987837)
                    ·
                      rfl

theorem cell23_2274774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2274774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274774 prefixEnd_2274774 := by exact prefixLift 2274774
  have htrace : WordTrace (prefixWord ++ tailWord_2274774) baseStart_2274774 baseEnd_2274774 := by
    simpa [prefixWord, tailWord_2274774, baseEnd_2274774] using wordTrace_append hprefix tailTrace_2274774
  have hstable : (prefixWord ++ tailWord_2274774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274774).length < 2 ^ (prefixWord ++ tailWord_2274774).sum := by decide
  have hdescent : baseEnd_2274774 < baseStart_2274774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274777 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 4]
def baseStart_2274777 : Nat := 118140960795 + 2274777 * 2 ^ 59
def prefixEnd_2274777 : Nat := 4983230072969 + 3 ^ 40 * 2274777 * 2
def baseEnd_2274777 : Nat := 1168053982792751658225997

theorem tailTrace_2274777 : CollatzResearch.WordTrace tailWord_2274777 prefixEnd_2274777 1168053982792751658225997 := by
  unfold tailWord_2274777
  simp only [CollatzResearch.WordTrace]
  refine ⟨82967933279878904826566585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55311955519919269884377723 82967933279878904826566585)
  ·
    refine ⟨62225949959909178619924939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82967933279878904826566585 62225949959909178619924939)
    ·
      refine ⟨93338924939863767929887409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62225949959909178619924939 93338924939863767929887409)
      ·
        refine ⟨70004193704897825947415557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93338924939863767929887409 70004193704897825947415557)
        ·
          refine ⟨13125786319668342365140417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70004193704897825947415557 13125786319668342365140417)
          ·
            refine ⟨9844339739751256773855313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13125786319668342365140417 9844339739751256773855313)
            ·
              refine ⟨7383254804813442580391485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9844339739751256773855313 7383254804813442580391485)
              ·
                refine ⟨2768720551805040967646807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7383254804813442580391485 2768720551805040967646807)
                ·
                  refine ⟨4153080827707561451470211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768720551805040967646807 4153080827707561451470211)
                  ·
                    refine ⟨6229621241561342177205317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4153080827707561451470211 6229621241561342177205317)
                    ·
                      refine ⟨1168053982792751658225997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6229621241561342177205317 1168053982792751658225997)
                      ·
                        rfl

theorem cell23_2274777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_2274777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274777 prefixEnd_2274777 := by exact prefixLift 2274777
  have htrace : WordTrace (prefixWord ++ tailWord_2274777) baseStart_2274777 baseEnd_2274777 := by
    simpa [prefixWord, tailWord_2274777, baseEnd_2274777] using wordTrace_append hprefix tailTrace_2274777
  have hstable : (prefixWord ++ tailWord_2274777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274777).length < 2 ^ (prefixWord ++ tailWord_2274777).sum := by decide
  have hdescent : baseEnd_2274777 < baseStart_2274777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274787 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 4, 4]
def baseStart_2274787 : Nat := 118140960795 + 2274787 * 2 ^ 59
def prefixEnd_2274787 : Nat := 4983230072969 + 3 ^ 40 * 2274787 * 2
def baseEnd_2274787 : Nat := 389353039199765539700317

theorem tailTrace_2274787 : CollatzResearch.WordTrace tailWord_2274787 prefixEnd_2274787 389353039199765539700317 := by
  unfold tailWord_2274787
  simp only [CollatzResearch.WordTrace]
  refine ⟨82968298009842676534430615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55312198673228451022953743 82968298009842676534430615)
  ·
    refine ⟨124452447014764014801645923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82968298009842676534430615 124452447014764014801645923)
    ·
      refine ⟨186678670522146022202468885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124452447014764014801645923 186678670522146022202468885)
      ·
        refine ⟨8750562680725594790740729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 186678670522146022202468885 8750562680725594790740729)
        ·
          refine ⟨6562922010544196093055547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8750562680725594790740729 6562922010544196093055547)
          ·
            refine ⟨9844383015816294139583321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6562922010544196093055547 9844383015816294139583321)
            ·
              refine ⟨7383287261862220604687491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9844383015816294139583321 7383287261862220604687491)
              ·
                refine ⟨11074930892793330907031237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7383287261862220604687491 11074930892793330907031237)
                ·
                  refine ⟨2076549542398749545068357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11074930892793330907031237 2076549542398749545068357)
                  ·
                    refine ⟨389353039199765539700317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2076549542398749545068357 389353039199765539700317)
                    ·
                      rfl

theorem cell23_2274787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 4].length) (baseStart_2274787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274787 prefixEnd_2274787 := by exact prefixLift 2274787
  have htrace : WordTrace (prefixWord ++ tailWord_2274787) baseStart_2274787 baseEnd_2274787 := by
    simpa [prefixWord, tailWord_2274787, baseEnd_2274787] using wordTrace_append hprefix tailTrace_2274787
  have hstable : (prefixWord ++ tailWord_2274787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274787).length < 2 ^ (prefixWord ++ tailWord_2274787).sum := by decide
  have hdescent : baseEnd_2274787 < baseStart_2274787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274800 : List Nat := [2, 1, 1, 1, 3, 5, 2, 8]
def baseStart_2274800 : Nat := 118140960795 + 2274800 * 2 ^ 59
def prefixEnd_2274800 : Nat := 4983230072969 + 3 ^ 40 * 2274800 * 2
def baseEnd_2274800 : Nat := 43261696031400187712533

theorem tailTrace_2274800 : CollatzResearch.WordTrace tailWord_2274800 prefixEnd_2274800 43261696031400187712533 := by
  unfold tailWord_2274800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41484386079397789877326927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55312514772530386503102569 41484386079397789877326927)
  ·
    refine ⟨62226579119096684815990391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41484386079397789877326927 62226579119096684815990391)
    ·
      refine ⟨93339868678645027223985587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62226579119096684815990391 93339868678645027223985587)
      ·
        refine ⟨140009803017967540835978381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93339868678645027223985587 140009803017967540835978381)
        ·
          refine ⟨52503676131737827813491893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140009803017967540835978381 52503676131737827813491893)
          ·
            refine ⟨4922219637350421357514865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52503676131737827813491893 4922219637350421357514865)
            ·
              refine ⟨3691664728012816018136149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4922219637350421357514865 3691664728012816018136149)
              ·
                refine ⟨43261696031400187712533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3691664728012816018136149 43261696031400187712533)
                ·
                  rfl

theorem cell23_2274800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 8].length) (baseStart_2274800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274800 prefixEnd_2274800 := by exact prefixLift 2274800
  have htrace : WordTrace (prefixWord ++ tailWord_2274800) baseStart_2274800 baseEnd_2274800 := by
    simpa [prefixWord, tailWord_2274800, baseEnd_2274800] using wordTrace_append hprefix tailTrace_2274800
  have hstable : (prefixWord ++ tailWord_2274800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274800).length < 2 ^ (prefixWord ++ tailWord_2274800).sum := by decide
  have hdescent : baseEnd_2274800 < baseStart_2274800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274880 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 4]
def baseStart_2274880 : Nat := 118140960795 + 2274880 * 2 ^ 59
def prefixEnd_2274880 : Nat := 4983230072969 + 3 ^ 40 * 2274880 * 2
def baseEnd_2274880 : Nat := 1168106871300164755238023

theorem tailTrace_2274880 : CollatzResearch.WordTrace tailWord_2274880 prefixEnd_2274880 1168106871300164755238023 := by
  unfold tailWord_2274880
  simp only [CollatzResearch.WordTrace]
  refine ⟨41485844999252876708783047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55314459999003835611710729 41485844999252876708783047)
  ·
    refine ⟨62228767498879315063174571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41485844999252876708783047 62228767498879315063174571)
    ·
      refine ⟨93343151248318972594761857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62228767498879315063174571 93343151248318972594761857)
      ·
        refine ⟨70007363436239229446071393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93343151248318972594761857 70007363436239229446071393)
        ·
          refine ⟨52505522577179422084553545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70007363436239229446071393 52505522577179422084553545)
          ·
            refine ⟨39379141932884566563415159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52505522577179422084553545 39379141932884566563415159)
            ·
              refine ⟨59068712899326849845122739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39379141932884566563415159 59068712899326849845122739)
              ·
                refine ⟨88603069348990274767684109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59068712899326849845122739 88603069348990274767684109)
                ·
                  refine ⟨33226151005871353037881541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88603069348990274767684109 33226151005871353037881541)
                  ·
                    refine ⟨6229903313600878694602789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33226151005871353037881541 6229903313600878694602789)
                    ·
                      refine ⟨1168106871300164755238023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6229903313600878694602789 1168106871300164755238023)
                      ·
                        rfl

theorem cell23_2274880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_2274880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274880 prefixEnd_2274880 := by exact prefixLift 2274880
  have htrace : WordTrace (prefixWord ++ tailWord_2274880) baseStart_2274880 baseEnd_2274880 := by
    simpa [prefixWord, tailWord_2274880, baseEnd_2274880] using wordTrace_append hprefix tailTrace_2274880
  have hstable : (prefixWord ++ tailWord_2274880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274880).length < 2 ^ (prefixWord ++ tailWord_2274880).sum := by decide
  have hdescent : baseEnd_2274880 < baseStart_2274880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274890 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 9]
def baseStart_2274890 : Nat := 118140960795 + 2274890 * 2 ^ 59
def prefixEnd_2274890 : Nat := 4983230072969 + 3 ^ 40 * 2274890 * 2
def baseEnd_2274890 : Nat := 129790222900745524012553

theorem tailTrace_2274890 : CollatzResearch.WordTrace tailWord_2274890 prefixEnd_2274890 129790222900745524012553 := by
  unfold tailWord_2274890
  simp only [CollatzResearch.WordTrace]
  refine ⟨20743013682117381281357531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55314703152313016750286749 20743013682117381281357531)
  ·
    refine ⟨31114520523176071922036297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20743013682117381281357531 31114520523176071922036297)
    ·
      refine ⟨23335890392382053941527223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31114520523176071922036297 23335890392382053941527223)
      ·
        refine ⟨35003835588573080912290835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23335890392382053941527223 35003835588573080912290835)
        ·
          refine ⟨52505753382859621368436253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35003835588573080912290835 52505753382859621368436253)
          ·
            refine ⟨19689657518572358013163595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52505753382859621368436253 19689657518572358013163595)
            ·
              refine ⟨29534486277858537019745393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19689657518572358013163595 29534486277858537019745393)
              ·
                refine ⟨22150864708393902764809045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29534486277858537019745393 22150864708393902764809045)
                ·
                  refine ⟨129790222900745524012553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22150864708393902764809045 129790222900745524012553)
                  ·
                    rfl

theorem cell23_2274890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_2274890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274890 prefixEnd_2274890 := by exact prefixLift 2274890
  have htrace : WordTrace (prefixWord ++ tailWord_2274890) baseStart_2274890 baseEnd_2274890 := by
    simpa [prefixWord, tailWord_2274890, baseEnd_2274890] using wordTrace_append hprefix tailTrace_2274890
  have hstable : (prefixWord ++ tailWord_2274890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274890).length < 2 ^ (prefixWord ++ tailWord_2274890).sum := by decide
  have hdescent : baseEnd_2274890 < baseStart_2274890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274937 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 2, 5]
def baseStart_2274937 : Nat := 118140960795 + 2274937 * 2 ^ 59
def prefixEnd_2274937 : Nat := 4983230072969 + 3 ^ 40 * 2274937 * 2
def baseEnd_2274937 : Nat := 389378713232490344075087

theorem tailTrace_2274937 : CollatzResearch.WordTrace tailWord_2274937 prefixEnd_2274937 389378713232490344075087 := by
  unfold tailWord_2274937
  simp only [CollatzResearch.WordTrace]
  refine ⟨82973768959299252152391065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55315845972866168101594043 82973768959299252152391065)
  ·
    refine ⟨62230326719474439114293299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82973768959299252152391065 62230326719474439114293299)
    ·
      refine ⟨93345490079211658671439949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62230326719474439114293299 93345490079211658671439949)
      ·
        refine ⟨35004558779704372001789981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93345490079211658671439949 35004558779704372001789981)
        ·
          refine ⟨13126709542389139500671243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35004558779704372001789981 13126709542389139500671243)
          ·
            refine ⟨19690064313583709251006865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13126709542389139500671243 19690064313583709251006865)
            ·
              refine ⟨14767548235187781938255149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19690064313583709251006865 14767548235187781938255149)
              ·
                refine ⟨5537830588195418226845681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14767548235187781938255149 5537830588195418226845681)
                ·
                  refine ⟨4153372941146563670134261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5537830588195418226845681 4153372941146563670134261)
                  ·
                    refine ⟨389378713232490344075087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4153372941146563670134261 389378713232490344075087)
                    ·
                      rfl

theorem cell23_2274937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_2274937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274937 prefixEnd_2274937 := by exact prefixLift 2274937
  have htrace : WordTrace (prefixWord ++ tailWord_2274937) baseStart_2274937 baseEnd_2274937 := by
    simpa [prefixWord, tailWord_2274937, baseEnd_2274937] using wordTrace_append hprefix tailTrace_2274937
  have hstable : (prefixWord ++ tailWord_2274937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274937).length < 2 ^ (prefixWord ++ tailWord_2274937).sum := by decide
  have hdescent : baseEnd_2274937 < baseStart_2274937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274941 : List Nat := [1, 4, 1, 1, 4, 3, 1, 3, 5]
def baseStart_2274941 : Nat := 118140960795 + 2274941 * 2 ^ 59
def prefixEnd_2274941 : Nat := 4983230072969 + 3 ^ 40 * 2274941 * 2
def baseEnd_2274941 : Nat := 129793132624454335175027

theorem tailTrace_2274941 : CollatzResearch.WordTrace tailWord_2274941 prefixEnd_2274941 129793132624454335175027 := by
  unfold tailWord_2274941
  simp only [CollatzResearch.WordTrace]
  refine ⟨82973914851284760835536677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55315943234189840557024451 82973914851284760835536677)
  ·
    refine ⟨15557609034615892656663127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82973914851284760835536677 15557609034615892656663127)
    ·
      refine ⟨23336413551923838984994691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15557609034615892656663127 23336413551923838984994691)
      ·
        refine ⟨35004620327885758477492037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23336413551923838984994691 35004620327885758477492037)
        ·
          refine ⟨6563366311478579714529757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35004620327885758477492037 6563366311478579714529757)
          ·
            refine ⟨2461262366804467392948659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6563366311478579714529757 2461262366804467392948659)
            ·
              refine ⟨3691893550206701089422989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2461262366804467392948659 3691893550206701089422989)
              ·
                refine ⟨1384460081327512908533621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3691893550206701089422989 1384460081327512908533621)
                ·
                  refine ⟨129793132624454335175027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1384460081327512908533621 129793132624454335175027)
                  ·
                    rfl

theorem cell23_2274941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_2274941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274941 prefixEnd_2274941 := by exact prefixLift 2274941
  have htrace : WordTrace (prefixWord ++ tailWord_2274941) baseStart_2274941 baseEnd_2274941 := by
    simpa [prefixWord, tailWord_2274941, baseEnd_2274941] using wordTrace_append hprefix tailTrace_2274941
  have hstable : (prefixWord ++ tailWord_2274941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274941).length < 2 ^ (prefixWord ++ tailWord_2274941).sum := by decide
  have hdescent : baseEnd_2274941 < baseStart_2274941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274954 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_2274954 : Nat := 118140960795 + 2274954 * 2 ^ 59
def prefixEnd_2274954 : Nat := 4983230072969 + 3 ^ 40 * 2274954 * 2
def baseEnd_2274954 : Nat := 389381622956199155237561

theorem tailTrace_2274954 : CollatzResearch.WordTrace tailWord_2274954 prefixEnd_2274954 389381622956199155237561 := by
  unfold tailWord_2274954
  simp only [CollatzResearch.WordTrace]
  refine ⟨20743597250059416013939979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55316259333491776037173277 20743597250059416013939979)
  ·
    refine ⟨31115395875089124020909969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20743597250059416013939979 31115395875089124020909969)
    ·
      refine ⟨23336546906316843015682477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31115395875089124020909969 23336546906316843015682477)
      ·
        refine ⟨8751205089868816130880929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23336546906316843015682477 8751205089868816130880929)
        ·
          refine ⟨6563403817401612098160697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8751205089868816130880929 6563403817401612098160697)
          ·
            refine ⟨4922552863051209073620523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6563403817401612098160697 4922552863051209073620523)
            ·
              refine ⟨7383829294576813610430785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4922552863051209073620523 7383829294576813610430785)
              ·
                refine ⟨5537871970932610207823089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7383829294576813610430785 5537871970932610207823089)
                ·
                  refine ⟨4153403978199457655867317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5537871970932610207823089 4153403978199457655867317)
                  ·
                    refine ⟨389381622956199155237561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4153403978199457655867317 389381622956199155237561)
                    ·
                      rfl

theorem cell23_2274954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_2274954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274954 prefixEnd_2274954 := by exact prefixLift 2274954
  have htrace : WordTrace (prefixWord ++ tailWord_2274954) baseStart_2274954 baseEnd_2274954 := by
    simpa [prefixWord, tailWord_2274954, baseEnd_2274954] using wordTrace_append hprefix tailTrace_2274954
  have hstable : (prefixWord ++ tailWord_2274954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274954).length < 2 ^ (prefixWord ++ tailWord_2274954).sum := by decide
  have hdescent : baseEnd_2274954 < baseStart_2274954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2274994 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_2274994 : Nat := 118140960795 + 2274994 * 2 ^ 59
def prefixEnd_2274994 : Nat := 4983230072969 + 3 ^ 40 * 2274994 * 2
def baseEnd_2274994 : Nat := 1168165408094777309212499

theorem tailTrace_2274994 : CollatzResearch.WordTrace tailWord_2274994 prefixEnd_2274994 1168165408094777309212499 := by
  unfold tailWord_2274994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20743961980023187721804009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55317231946728500591477357 20743961980023187721804009)
  ·
    refine ⟨15557971485017390791353007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20743961980023187721804009 15557971485017390791353007)
    ·
      refine ⟨23336957227526086187029511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15557971485017390791353007 23336957227526086187029511)
      ·
        refine ⟨35005435841289129280544267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23336957227526086187029511 35005435841289129280544267)
        ·
          refine ⟨52508153761933693920816401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35005435841289129280544267 52508153761933693920816401)
          ·
            refine ⟨39381115321450270440612301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52508153761933693920816401 39381115321450270440612301)
            ·
              refine ⟨14767918245543851415229613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39381115321450270440612301 14767918245543851415229613)
              ·
                refine ⟨5537969342078944280711105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14767918245543851415229613 5537969342078944280711105)
                ·
                  refine ⟨4153477006559208210533329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5537969342078944280711105 4153477006559208210533329)
                  ·
                    refine ⟨3115107754919406157899997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4153477006559208210533329 3115107754919406157899997)
                    ·
                      refine ⟨1168165408094777309212499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3115107754919406157899997 1168165408094777309212499)
                      ·
                        rfl

theorem cell23_2274994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_2274994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2274994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2274994 prefixEnd_2274994 := by exact prefixLift 2274994
  have htrace : WordTrace (prefixWord ++ tailWord_2274994) baseStart_2274994 baseEnd_2274994 := by
    simpa [prefixWord, tailWord_2274994, baseEnd_2274994] using wordTrace_append hprefix tailTrace_2274994
  have hstable : (prefixWord ++ tailWord_2274994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2274994).length < 2 ^ (prefixWord ++ tailWord_2274994).sum := by decide
  have hdescent : baseEnd_2274994 < baseStart_2274994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2274994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275018 : List Nat := [3, 1, 2, 1, 5, 1, 1, 4, 1, 4]
def baseStart_2275018 : Nat := 118140960795 + 2275018 * 2 ^ 59
def prefixEnd_2275018 : Nat := 4983230072969 + 3 ^ 40 * 2275018 * 2
def baseEnd_2275018 : Nat := 389392577210161738437463

theorem tailTrace_2275018 : CollatzResearch.WordTrace tailWord_2275018 prefixEnd_2275018 389392577210161738437463 := by
  unfold tailWord_2275018
  simp only [CollatzResearch.WordTrace]
  refine ⟨20744180818001450746522427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55317815514670535324059805 20744180818001450746522427)
  ·
    refine ⟨31116271227002176119783641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20744180818001450746522427 31116271227002176119783641)
    ·
      refine ⟨23337203420251632089837731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31116271227002176119783641 23337203420251632089837731)
      ·
        refine ⟨35005805130377448134756597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23337203420251632089837731 35005805130377448134756597)
        ·
          refine ⟨3281794230972885762633431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35005805130377448134756597 3281794230972885762633431)
          ·
            refine ⟨4922691346459328643950147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281794230972885762633431 4922691346459328643950147)
            ·
              refine ⟨7384037019688992965925221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4922691346459328643950147 7384037019688992965925221)
              ·
                refine ⟨1384506941191686181110979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7384037019688992965925221 1384506941191686181110979)
                ·
                  refine ⟨2076760411787529271666469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1384506941191686181110979 2076760411787529271666469)
                  ·
                    refine ⟨389392577210161738437463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2076760411787529271666469 389392577210161738437463)
                    ·
                      rfl

theorem cell23_2275018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_2275018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275018 prefixEnd_2275018 := by exact prefixLift 2275018
  have htrace : WordTrace (prefixWord ++ tailWord_2275018) baseStart_2275018 baseEnd_2275018 := by
    simpa [prefixWord, tailWord_2275018, baseEnd_2275018] using wordTrace_append hprefix tailTrace_2275018
  have hstable : (prefixWord ++ tailWord_2275018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275018).length < 2 ^ (prefixWord ++ tailWord_2275018).sum := by decide
  have hdescent : baseEnd_2275018 < baseStart_2275018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275044 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_2275044 : Nat := 118140960795 + 2275044 * 2 ^ 59
def prefixEnd_2275044 : Nat := 4983230072969 + 3 ^ 40 * 2275044 * 2
def baseEnd_2275044 : Nat := 389397027375834037862423

theorem tailTrace_2275044 : CollatzResearch.WordTrace tailWord_2275044 prefixEnd_2275044 389397027375834037862423 := by
  unfold tailWord_2275044
  simp only [CollatzResearch.WordTrace]
  refine ⟨41488835784955804713268093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55318447713274406284357457 41488835784955804713268093)
  ·
    refine ⟨15558313419358426767475535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41488835784955804713268093 15558313419358426767475535)
    ·
      refine ⟨23337470129037640151213303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15558313419358426767475535 23337470129037640151213303)
      ·
        refine ⟨35006205193556460226819955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23337470129037640151213303 35006205193556460226819955)
        ·
          refine ⟨52509307790334690340229933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35006205193556460226819955 52509307790334690340229933)
          ·
            refine ⟨19690990421375508877586225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52509307790334690340229933 19690990421375508877586225)
            ·
              refine ⟨14768242816031631658189669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19690990421375508877586225 14768242816031631658189669)
              ·
                refine ⟨2769045528005930935910563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14768242816031631658189669 2769045528005930935910563)
                ·
                  refine ⟨4153568292008896403865845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769045528005930935910563 4153568292008896403865845)
                  ·
                    refine ⟨389397027375834037862423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4153568292008896403865845 389397027375834037862423)
                    ·
                      rfl

theorem cell23_2275044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_2275044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275044 prefixEnd_2275044 := by exact prefixLift 2275044
  have htrace : WordTrace (prefixWord ++ tailWord_2275044) baseStart_2275044 baseEnd_2275044 := by
    simpa [prefixWord, tailWord_2275044, baseEnd_2275044] using wordTrace_append hprefix tailTrace_2275044
  have hstable : (prefixWord ++ tailWord_2275044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275044).length < 2 ^ (prefixWord ++ tailWord_2275044).sum := by decide
  have hdescent : baseEnd_2275044 < baseStart_2275044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275051 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 2, 3, 2]
def baseStart_2275051 : Nat := 118140960795 + 2275051 * 2 ^ 59
def prefixEnd_2275051 : Nat := 4983230072969 + 3 ^ 40 * 2275051 * 2
def baseEnd_2275051 : Nat := 1168194676492083586199737

theorem tailTrace_2275051 : CollatzResearch.WordTrace tailWord_2275051 prefixEnd_2275051 1168194676492083586199737 := by
  unfold tailWord_2275051
  simp only [CollatzResearch.WordTrace]
  refine ⟨82977926880886249622041007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55318617920590833081360671 82977926880886249622041007)
  ·
    refine ⟨124466890321329374433061511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82977926880886249622041007 124466890321329374433061511)
    ·
      refine ⟨186700335481994061649592267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124466890321329374433061511 186700335481994061649592267)
      ·
        refine ⟨280050503222991092474388401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186700335481994061649592267 280050503222991092474388401)
        ·
          refine ⟨210037877417243319355791301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280050503222991092474388401 210037877417243319355791301)
          ·
            refine ⟨39382102015733122379210869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210037877417243319355791301 39382102015733122379210869)
            ·
              refine ⟨3692072063974980223051019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39382102015733122379210869 3692072063974980223051019)
              ·
                refine ⟨5538108095962470334576529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3692072063974980223051019 5538108095962470334576529)
                ·
                  refine ⟨4153581071971852750932397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5538108095962470334576529 4153581071971852750932397)
                  ·
                    refine ⟨1557592901989444781599649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4153581071971852750932397 1557592901989444781599649)
                    ·
                      refine ⟨1168194676492083586199737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1557592901989444781599649 1168194676492083586199737)
                      ·
                        rfl

theorem cell23_2275051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 3, 2].length) (baseStart_2275051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275051 prefixEnd_2275051 := by exact prefixLift 2275051
  have htrace : WordTrace (prefixWord ++ tailWord_2275051) baseStart_2275051 baseEnd_2275051 := by
    simpa [prefixWord, tailWord_2275051, baseEnd_2275051] using wordTrace_append hprefix tailTrace_2275051
  have hstable : (prefixWord ++ tailWord_2275051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275051).length < 2 ^ (prefixWord ++ tailWord_2275051).sum := by decide
  have hdescent : baseEnd_2275051 < baseStart_2275051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275077 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_2275077 : Nat := 118140960795 + 2275077 * 2 ^ 59
def prefixEnd_2275077 : Nat := 4983230072969 + 3 ^ 40 * 2275077 * 2
def baseEnd_2275077 : Nat := 1168208026989100484474617

theorem tailTrace_2275077 : CollatzResearch.WordTrace tailWord_2275077 prefixEnd_2275077 1168208026989100484474617 := by
  unfold tailWord_2275077
  simp only [CollatzResearch.WordTrace]
  refine ⟨82978875178792056062487485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55319250119194704041658323 82978875178792056062487485)
  ·
    refine ⟨31117078192047021023432807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82978875178792056062487485 31117078192047021023432807)
    ·
      refine ⟨46675617288070531535149211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31117078192047021023432807 46675617288070531535149211)
      ·
        refine ⟨70013425932105797302723817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46675617288070531535149211 70013425932105797302723817)
        ·
          refine ⟨52510069449079347977042863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70013425932105797302723817 52510069449079347977042863)
          ·
            refine ⟨78765104173619021965564295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52510069449079347977042863 78765104173619021965564295)
            ·
              refine ⟨118147656260428532948346443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78765104173619021965564295 118147656260428532948346443)
              ·
                refine ⟨177221484390642799422519665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118147656260428532948346443 177221484390642799422519665)
                ·
                  refine ⟨132916113292982099566889749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177221484390642799422519665 132916113292982099566889749)
                  ·
                    refine ⟨6230442810608535917197957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 132916113292982099566889749 6230442810608535917197957)
                    ·
                      refine ⟨1168208026989100484474617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6230442810608535917197957 1168208026989100484474617)
                      ·
                        rfl

theorem cell23_2275077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_2275077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275077 prefixEnd_2275077 := by exact prefixLift 2275077
  have htrace : WordTrace (prefixWord ++ tailWord_2275077) baseStart_2275077 baseEnd_2275077 := by
    simpa [prefixWord, tailWord_2275077, baseEnd_2275077] using wordTrace_append hprefix tailTrace_2275077
  have hstable : (prefixWord ++ tailWord_2275077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275077).length < 2 ^ (prefixWord ++ tailWord_2275077).sum := by decide
  have hdescent : baseEnd_2275077 < baseStart_2275077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275084 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 5, 2, 3]
def baseStart_2275084 : Nat := 118140960795 + 2275084 * 2 ^ 59
def prefixEnd_2275084 : Nat := 4983230072969 + 3 ^ 40 * 2275084 * 2
def baseEnd_2275084 : Nat := 1168211621353681957087085

theorem tailTrace_2275084 : CollatzResearch.WordTrace tailWord_2275084 prefixEnd_2275084 1168211621353681957087085 := by
  unfold tailWord_2275084
  simp only [CollatzResearch.WordTrace]
  refine ⟨41489565244883348128996153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55319420326511130838661537 41489565244883348128996153)
  ·
    refine ⟨31117173933662511096747115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41489565244883348128996153 31117173933662511096747115)
    ·
      refine ⟨46675760900493766645120673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31117173933662511096747115 46675760900493766645120673)
      ·
        refine ⟨35006820675370324983840505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46675760900493766645120673 35006820675370324983840505)
        ·
          refine ⟨26255115506527743737880379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35006820675370324983840505 26255115506527743737880379)
          ·
            refine ⟨39382673259791615606820569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26255115506527743737880379 39382673259791615606820569)
            ·
              refine ⟨29537004944843711705115427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39382673259791615606820569 29537004944843711705115427)
              ·
                refine ⟨44305507417265567557673141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29537004944843711705115427 44305507417265567557673141)
                ·
                  refine ⟨4153641320368646958531857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44305507417265567557673141 4153641320368646958531857)
                  ·
                    refine ⟨3115230990276485218898893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4153641320368646958531857 3115230990276485218898893)
                    ·
                      refine ⟨1168211621353681957087085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3115230990276485218898893 1168211621353681957087085)
                      ·
                        rfl

theorem cell23_2275084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_2275084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275084 prefixEnd_2275084 := by exact prefixLift 2275084
  have htrace : WordTrace (prefixWord ++ tailWord_2275084) baseStart_2275084 baseEnd_2275084 := by
    simpa [prefixWord, tailWord_2275084, baseEnd_2275084] using wordTrace_append hprefix tailTrace_2275084
  have hstable : (prefixWord ++ tailWord_2275084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275084).length < 2 ^ (prefixWord ++ tailWord_2275084).sum := by decide
  have hdescent : baseEnd_2275084 < baseStart_2275084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275098 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2]
def baseStart_2275098 : Nat := 118140960795 + 2275098 * 2 ^ 59
def prefixEnd_2275098 : Nat := 4983230072969 + 3 ^ 40 * 2275098 * 2
def baseEnd_2275098 : Nat := 1168218810082844902312021

theorem tailTrace_2275098 : CollatzResearch.WordTrace tailWord_2275098 prefixEnd_2275098 1168218810082844902312021 := by
  unfold tailWord_2275098
  simp only [CollatzResearch.WordTrace]
  refine ⟨20744910277928994162250487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55319760741143984432667965 20744910277928994162250487)
  ·
    refine ⟨31117365416893491243375731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20744910277928994162250487 31117365416893491243375731)
    ·
      refine ⟨46676048125340236865063597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31117365416893491243375731 46676048125340236865063597)
      ·
        refine ⟨17503518047002588824398849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46676048125340236865063597 17503518047002588824398849)
        ·
          refine ⟨13127638535251941618299137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17503518047002588824398849 13127638535251941618299137)
          ·
            refine ⟨9845728901438956213724353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13127638535251941618299137 9845728901438956213724353)
            ·
              refine ⟨7384296676079217160293265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9845728901438956213724353 7384296676079217160293265)
              ·
                refine ⟨5538222507059412870219949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7384296676079217160293265 5538222507059412870219949)
                ·
                  refine ⟨2076833440147279826332481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5538222507059412870219949 2076833440147279826332481)
                  ·
                    refine ⟨1557625080110459869749361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2076833440147279826332481 1557625080110459869749361)
                    ·
                      refine ⟨1168218810082844902312021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1557625080110459869749361 1168218810082844902312021)
                      ·
                        rfl

theorem cell23_2275098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_2275098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275098 prefixEnd_2275098 := by exact prefixLift 2275098
  have htrace : WordTrace (prefixWord ++ tailWord_2275098) baseStart_2275098 baseEnd_2275098 := by
    simpa [prefixWord, tailWord_2275098, baseEnd_2275098] using wordTrace_append hprefix tailTrace_2275098
  have hstable : (prefixWord ++ tailWord_2275098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275098).length < 2 ^ (prefixWord ++ tailWord_2275098).sum := by decide
  have hdescent : baseEnd_2275098 < baseStart_2275098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275118 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2275118 : Nat := 118140960795 + 2275118 * 2 ^ 59
def prefixEnd_2275118 : Nat := 4983230072969 + 3 ^ 40 * 2275118 * 2
def baseEnd_2275118 : Nat := 1168229079695934824061929

theorem tailTrace_2275118 : CollatzResearch.WordTrace tailWord_2275118 prefixEnd_2275118 1168229079695934824061929 := by
  unfold tailWord_2275118
  simp only [CollatzResearch.WordTrace]
  refine ⟨10372546321455440008091251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55320247047762346709820005 10372546321455440008091251)
  ·
    refine ⟨15558819482183160012136877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10372546321455440008091251 15558819482183160012136877)
    ·
      refine ⟨5834557305818685004551329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15558819482183160012136877 5834557305818685004551329)
      ·
        refine ⟨4375917979364013753413497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5834557305818685004551329 4375917979364013753413497)
        ·
          refine ⟨3281938484523010315060123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4375917979364013753413497 3281938484523010315060123)
          ·
            refine ⟨4922907726784515472590185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281938484523010315060123 4922907726784515472590185)
            ·
              refine ⟨3692180795088386604442639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4922907726784515472590185 3692180795088386604442639)
              ·
                refine ⟨5538271192632579906663959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3692180795088386604442639 5538271192632579906663959)
                ·
                  refine ⟨8307406788948869859995939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5538271192632579906663959 8307406788948869859995939)
                  ·
                    refine ⟨12461110183423304789993909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8307406788948869859995939 12461110183423304789993909)
                    ·
                      refine ⟨1168229079695934824061929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12461110183423304789993909 1168229079695934824061929)
                      ·
                        rfl

theorem cell23_2275118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2275118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275118 prefixEnd_2275118 := by exact prefixLift 2275118
  have htrace : WordTrace (prefixWord ++ tailWord_2275118) baseStart_2275118 baseEnd_2275118 := by
    simpa [prefixWord, tailWord_2275118, baseEnd_2275118] using wordTrace_append hprefix tailTrace_2275118
  have hstable : (prefixWord ++ tailWord_2275118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275118).length < 2 ^ (prefixWord ++ tailWord_2275118).sum := by decide
  have hdescent : baseEnd_2275118 < baseStart_2275118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275141 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 3, 3, 2]
def baseStart_2275141 : Nat := 118140960795 + 2275141 * 2 ^ 59
def prefixEnd_2275141 : Nat := 4983230072969 + 3 ^ 40 * 2275141 * 2
def baseEnd_2275141 : Nat := 1168240889750988234074323

theorem tailTrace_2275141 : CollatzResearch.WordTrace tailWord_2275141 prefixEnd_2275141 1168240889750988234074323 := by
  unfold tailWord_2275141
  simp only [CollatzResearch.WordTrace]
  refine ⟨82981209450560194992817277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55320806300373463328544851 82981209450560194992817277)
  ·
    refine ⟨31117953543960073122306479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82981209450560194992817277 31117953543960073122306479)
    ·
      refine ⟨46676930315940109683459719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31117953543960073122306479 46676930315940109683459719)
      ·
        refine ⟨70015395473910164525189579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46676930315940109683459719 70015395473910164525189579)
        ·
          refine ⟨105023093210865246787784369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70015395473910164525189579 105023093210865246787784369)
          ·
            refine ⟨78767319908148935090838277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105023093210865246787784369 78767319908148935090838277)
            ·
              refine ⟨14768872482777925329532177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78767319908148935090838277 14768872482777925329532177)
              ·
                refine ⟨11076654362083443997149133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14768872482777925329532177 11076654362083443997149133)
                ·
                  refine ⟨4153745385781291498930925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11076654362083443997149133 4153745385781291498930925)
                  ·
                    refine ⟨1557654519667984312099097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4153745385781291498930925 1557654519667984312099097)
                    ·
                      refine ⟨1168240889750988234074323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1557654519667984312099097 1168240889750988234074323)
                      ·
                        rfl

theorem cell23_2275141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 3, 2].length) (baseStart_2275141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275141 prefixEnd_2275141 := by exact prefixLift 2275141
  have htrace : WordTrace (prefixWord ++ tailWord_2275141) baseStart_2275141 baseEnd_2275141 := by
    simpa [prefixWord, tailWord_2275141, baseEnd_2275141] using wordTrace_append hprefix tailTrace_2275141
  have hstable : (prefixWord ++ tailWord_2275141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275141).length < 2 ^ (prefixWord ++ tailWord_2275141).sum := by decide
  have hdescent : baseEnd_2275141 < baseStart_2275141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275142 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_2275142 : Nat := 118140960795 + 2275142 * 2 ^ 59
def prefixEnd_2275142 : Nat := 4983230072969 + 3 ^ 40 * 2275142 * 2
def baseEnd_2275142 : Nat := 389413801077214243387273

theorem tailTrace_2275142 : CollatzResearch.WordTrace tailWord_2275142 prefixEnd_2275142 389413801077214243387273 := by
  unfold tailWord_2275142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2593163935111142880112615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55320830615704381442402453 2593163935111142880112615)
  ·
    refine ⟨3889745902666714320168923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2593163935111142880112615 3889745902666714320168923)
    ·
      refine ⟨5834618854000071480253385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3889745902666714320168923 5834618854000071480253385)
      ·
        refine ⟨4375964140500053610190039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5834618854000071480253385 4375964140500053610190039)
        ·
          refine ⟨6563946210750080415285059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4375964140500053610190039 6563946210750080415285059)
          ·
            refine ⟨9845919316125120622927589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6563946210750080415285059 9845919316125120622927589)
            ·
              refine ⟨1846109871773460116798923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9845919316125120622927589 1846109871773460116798923)
              ·
                refine ⟨2769164807660190175198385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846109871773460116798923 2769164807660190175198385)
                ·
                  refine ⟨2076873605745142631398789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2769164807660190175198385 2076873605745142631398789)
                  ·
                    refine ⟨389413801077214243387273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2076873605745142631398789 389413801077214243387273)
                    ·
                      rfl

theorem cell23_2275142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_2275142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275142 prefixEnd_2275142 := by exact prefixLift 2275142
  have htrace : WordTrace (prefixWord ++ tailWord_2275142) baseStart_2275142 baseEnd_2275142 := by
    simpa [prefixWord, tailWord_2275142, baseEnd_2275142] using wordTrace_append hprefix tailTrace_2275142
  have hstable : (prefixWord ++ tailWord_2275142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275142).length < 2 ^ (prefixWord ++ tailWord_2275142).sum := by decide
  have hdescent : baseEnd_2275142 < baseStart_2275142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275175 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_2275175 : Nat := 118140960795 + 2275175 * 2 ^ 59
def prefixEnd_2275175 : Nat := 4983230072969 + 3 ^ 40 * 2275175 * 2
def baseEnd_2275175 : Nat := 1168258348093241101049167

theorem tailTrace_2275175 : CollatzResearch.WordTrace tailWord_2275175 prefixEnd_2275175 1168258348093241101049167 := by
  unfold tailWord_2275175
  simp only [CollatzResearch.WordTrace]
  refine ⟨82982449532437018799554979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55321633021624679199703319 82982449532437018799554979)
  ·
    refine ⟨124473674298655528199332469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82982449532437018799554979 124473674298655528199332469)
    ·
      refine ⟨11669406965498955768687419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124473674298655528199332469 11669406965498955768687419)
      ·
        refine ⟨17504110448248433653031129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11669406965498955768687419 17504110448248433653031129)
        ·
          refine ⟨13128082836186325239773347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17504110448248433653031129 13128082836186325239773347)
          ·
            refine ⟨19692124254279487859660021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13128082836186325239773347 19692124254279487859660021)
            ·
              refine ⟨1846136648838701986843127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19692124254279487859660021 1846136648838701986843127)
              ·
                refine ⟨2769204973258052980264691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846136648838701986843127 2769204973258052980264691)
                ·
                  refine ⟨4153807459887079470397037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769204973258052980264691 4153807459887079470397037)
                  ·
                    refine ⟨1557677797457654801398889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4153807459887079470397037 1557677797457654801398889)
                    ·
                      refine ⟨1168258348093241101049167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1557677797457654801398889 1168258348093241101049167)
                      ·
                        rfl

theorem cell23_2275175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_2275175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275175 prefixEnd_2275175 := by exact prefixLift 2275175
  have htrace : WordTrace (prefixWord ++ tailWord_2275175) baseStart_2275175 baseEnd_2275175 := by
    simpa [prefixWord, tailWord_2275175, baseEnd_2275175] using wordTrace_append hprefix tailTrace_2275175
  have hstable : (prefixWord ++ tailWord_2275175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275175).length < 2 ^ (prefixWord ++ tailWord_2275175).sum := by decide
  have hdescent : baseEnd_2275175 < baseStart_2275175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275184 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 4]
def baseStart_2275184 : Nat := 118140960795 + 2275184 * 2 ^ 59
def prefixEnd_2275184 : Nat := 4983230072969 + 3 ^ 40 * 2275184 * 2
def baseEnd_2275184 : Nat := 1168262969419131565836625

theorem tailTrace_2275184 : CollatzResearch.WordTrace tailWord_2275184 prefixEnd_2275184 1168262969419131565836625 := by
  unfold tailWord_2275184
  simp only [CollatzResearch.WordTrace]
  refine ⟨41491388894702206668316303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55321851859602942224421737 41491388894702206668316303)
  ·
    refine ⟨62237083342053310002474455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41491388894702206668316303 62237083342053310002474455)
    ·
      refine ⟨93355625013079965003711683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62237083342053310002474455 93355625013079965003711683)
      ·
        refine ⟨140033437519619947505567525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93355625013079965003711683 140033437519619947505567525)
        ·
          refine ⟨26256269534928740157293911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140033437519619947505567525 26256269534928740157293911)
          ·
            refine ⟨39384404302393110235940867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26256269534928740157293911 39384404302393110235940867)
            ·
              refine ⟨59076606453589665353911301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39384404302393110235940867 59076606453589665353911301)
              ·
                refine ⟨11076863710048062253858369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59076606453589665353911301 11076863710048062253858369)
                ·
                  refine ⟨8307647782536046690393777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11076863710048062253858369 8307647782536046690393777)
                  ·
                    refine ⟨6230735836902035017795333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8307647782536046690393777 6230735836902035017795333)
                    ·
                      refine ⟨1168262969419131565836625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6230735836902035017795333 1168262969419131565836625)
                      ·
                        rfl

theorem cell23_2275184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_2275184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275184 prefixEnd_2275184 := by exact prefixLift 2275184
  have htrace : WordTrace (prefixWord ++ tailWord_2275184) baseStart_2275184 baseEnd_2275184 := by
    simpa [prefixWord, tailWord_2275184, baseEnd_2275184] using wordTrace_append hprefix tailTrace_2275184
  have hstable : (prefixWord ++ tailWord_2275184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275184).length < 2 ^ (prefixWord ++ tailWord_2275184).sum := by decide
  have hdescent : baseEnd_2275184 < baseStart_2275184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275198 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2275198 : Nat := 118140960795 + 2275198 * 2 ^ 59
def prefixEnd_2275198 : Nat := 4983230072969 + 3 ^ 40 * 2275198 * 2
def baseEnd_2275198 : Nat := 389423386049431503687187

theorem tailTrace_2275198 : CollatzResearch.WordTrace tailWord_2275198 prefixEnd_2275198 389423386049431503687187 := by
  unfold tailWord_2275198
  simp only [CollatzResearch.WordTrace]
  refine ⟨10372911051419211715955281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55322192274235795818428165 10372911051419211715955281)
  ·
    refine ⟨7779683288564408786966461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10372911051419211715955281 7779683288564408786966461)
    ·
      refine ⟨2917381233211653295112423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7779683288564408786966461 2917381233211653295112423)
      ·
        refine ⟨4376071849817479942668635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2917381233211653295112423 4376071849817479942668635)
        ·
          refine ⟨6564107774726219914002953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4376071849817479942668635 6564107774726219914002953)
          ·
            refine ⟨4923080831044664935502215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6564107774726219914002953 4923080831044664935502215)
            ·
              refine ⟨7384621246566997403253323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923080831044664935502215 7384621246566997403253323)
              ·
                refine ⟨11076931869850496104879985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7384621246566997403253323 11076931869850496104879985)
                ·
                  refine ⟨8307698902387872078659989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11076931869850496104879985 8307698902387872078659989)
                  ·
                    refine ⟨389423386049431503687187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8307698902387872078659989 389423386049431503687187)
                    ·
                      rfl

theorem cell23_2275198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2275198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275198 prefixEnd_2275198 := by exact prefixLift 2275198
  have htrace : WordTrace (prefixWord ++ tailWord_2275198) baseStart_2275198 baseEnd_2275198 := by
    simpa [prefixWord, tailWord_2275198, baseEnd_2275198] using wordTrace_append hprefix tailTrace_2275198
  have hstable : (prefixWord ++ tailWord_2275198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275198).length < 2 ^ (prefixWord ++ tailWord_2275198).sum := by decide
  have hdescent : baseEnd_2275198 < baseStart_2275198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275228 : List Nat := [2, 2, 3, 3, 1, 1, 1, 5, 5]
def baseStart_2275228 : Nat := 118140960795 + 2275228 * 2 ^ 59
def prefixEnd_2275228 : Nat := 4983230072969 + 3 ^ 40 * 2275228 * 2
def baseEnd_2275228 : Nat := 129809506951992154854047

theorem tailTrace_2275228 : CollatzResearch.WordTrace tailWord_2275228 prefixEnd_2275228 129809506951992154854047 := by
  unfold tailWord_2275228
  simp only [CollatzResearch.WordTrace]
  refine ⟨41492191300622504425617169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55322921734163339234156225 41492191300622504425617169)
  ·
    refine ⟨31119143475466878319212877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41492191300622504425617169 31119143475466878319212877)
    ·
      refine ⟨11669678803300079369704829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31119143475466878319212877 11669678803300079369704829)
      ·
        refine ⟨4376129551237529763639311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11669678803300079369704829 4376129551237529763639311)
        ·
          refine ⟨6564194326856294645458967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4376129551237529763639311 6564194326856294645458967)
          ·
            refine ⟨9846291490284441968188451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6564194326856294645458967 9846291490284441968188451)
            ·
              refine ⟨14769437235426662952282677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9846291490284441968188451 14769437235426662952282677)
              ·
                refine ⟨1384634740821249651776501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14769437235426662952282677 1384634740821249651776501)
                ·
                  refine ⟨129809506951992154854047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1384634740821249651776501 129809506951992154854047)
                  ·
                    rfl

theorem cell23_2275228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_2275228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275228 prefixEnd_2275228 := by exact prefixLift 2275228
  have htrace : WordTrace (prefixWord ++ tailWord_2275228) baseStart_2275228 baseEnd_2275228 := by
    simpa [prefixWord, tailWord_2275228, baseEnd_2275228] using wordTrace_append hprefix tailTrace_2275228
  have hstable : (prefixWord ++ tailWord_2275228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275228).length < 2 ^ (prefixWord ++ tailWord_2275228).sum := by decide
  have hdescent : baseEnd_2275228 < baseStart_2275228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275244 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_2275244 : Nat := 118140960795 + 2275244 * 2 ^ 59
def prefixEnd_2275244 : Nat := 4983230072969 + 3 ^ 40 * 2275244 * 2
def baseEnd_2275244 : Nat := 1168293778258401331086349

theorem tailTrace_2275244 : CollatzResearch.WordTrace tailWord_2275244 prefixEnd_2275244 1168293778258401331086349 := by
  unfold tailWord_2275244
  simp only [CollatzResearch.WordTrace]
  refine ⟨41492483084593521791908393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55323310779458029055877857 41492483084593521791908393)
  ·
    refine ⟨31119362313445141343931295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41492483084593521791908393 31119362313445141343931295)
    ·
      refine ⟨46679043470167712015896943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31119362313445141343931295 46679043470167712015896943)
      ·
        refine ⟨70018565205251568023845415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46679043470167712015896943 70018565205251568023845415)
        ·
          refine ⟨105027847807877352035768123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70018565205251568023845415 105027847807877352035768123)
          ·
            refine ⟨157541771711816028053652185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105027847807877352035768123 157541771711816028053652185)
            ·
              refine ⟨118156328783862021040239139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157541771711816028053652185 118156328783862021040239139)
              ·
                refine ⟨177234493175793031560358709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118156328783862021040239139 177234493175793031560358709)
                ·
                  refine ⟨16615733735230596708783629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177234493175793031560358709 16615733735230596708783629)
                  ·
                    refine ⟨6230900150711473765793861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16615733735230596708783629 6230900150711473765793861)
                    ·
                      refine ⟨1168293778258401331086349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6230900150711473765793861 1168293778258401331086349)
                      ·
                        rfl

theorem cell23_2275244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_2275244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275244 prefixEnd_2275244 := by exact prefixLift 2275244
  have htrace : WordTrace (prefixWord ++ tailWord_2275244) baseStart_2275244 baseEnd_2275244 := by
    simpa [prefixWord, tailWord_2275244, baseEnd_2275244] using wordTrace_append hprefix tailTrace_2275244
  have hstable : (prefixWord ++ tailWord_2275244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275244).length < 2 ^ (prefixWord ++ tailWord_2275244).sum := by decide
  have hdescent : baseEnd_2275244 < baseStart_2275244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275261 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_2275261 : Nat := 118140960795 + 2275261 * 2 ^ 59
def prefixEnd_2275261 : Nat := 4983230072969 + 3 ^ 40 * 2275261 * 2
def baseEnd_2275261 : Nat := 1168302507429527764573771

theorem tailTrace_2275261 : CollatzResearch.WordTrace tailWord_2275261 prefixEnd_2275261 1168302507429527764573771 := by
  unfold tailWord_2275261
  simp only [CollatzResearch.WordTrace]
  refine ⟨82985586210125455487185637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55323724140083636991457091 82985586210125455487185637)
  ·
    refine ⟨15559797414398522903847307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82985586210125455487185637 15559797414398522903847307)
    ·
      refine ⟨23339696121597784355770961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15559797414398522903847307 23339696121597784355770961)
      ·
        refine ⟨17504772091198338266828221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23339696121597784355770961 17504772091198338266828221)
        ·
          refine ⟨6564289534199376850060583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17504772091198338266828221 6564289534199376850060583)
          ·
            refine ⟨9846434301299065275090875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6564289534199376850060583 9846434301299065275090875)
            ·
              refine ⟨14769651451948597912636313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9846434301299065275090875 14769651451948597912636313)
              ·
                refine ⟨11077238588961448434477235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14769651451948597912636313 11077238588961448434477235)
                ·
                  refine ⟨16615857883442172651715853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11077238588961448434477235 16615857883442172651715853)
                  ·
                    refine ⟨6230946706290814744393445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16615857883442172651715853 6230946706290814744393445)
                    ·
                      refine ⟨1168302507429527764573771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6230946706290814744393445 1168302507429527764573771)
                      ·
                        rfl

theorem cell23_2275261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_2275261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275261 prefixEnd_2275261 := by exact prefixLift 2275261
  have htrace : WordTrace (prefixWord ++ tailWord_2275261) baseStart_2275261 baseEnd_2275261 := by
    simpa [prefixWord, tailWord_2275261, baseEnd_2275261] using wordTrace_append hprefix tailTrace_2275261
  have hstable : (prefixWord ++ tailWord_2275261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275261).length < 2 ^ (prefixWord ++ tailWord_2275261).sum := by decide
  have hdescent : baseEnd_2275261 < baseStart_2275261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275292 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2275292 : Nat := 118140960795 + 2275292 * 2 ^ 59
def prefixEnd_2275292 : Nat := 4983230072969 + 3 ^ 40 * 2275292 * 2
def baseEnd_2275292 : Nat := 389439475109939047762043

theorem tailTrace_2275292 : CollatzResearch.WordTrace tailWord_2275292 prefixEnd_2275292 389439475109939047762043 := by
  unfold tailWord_2275292
  simp only [CollatzResearch.WordTrace]
  refine ⟨41493358436506573890782065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55324477915342098521042753 41493358436506573890782065)
  ·
    refine ⟨31120018827379930418086549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41493358436506573890782065 31120018827379930418086549)
    ·
      refine ⟨1458750882533434238347807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31120018827379930418086549 1458750882533434238347807)
      ·
        refine ⟨2188126323800151357521711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1458750882533434238347807 2188126323800151357521711)
        ·
          refine ⟨3282189485700227036282567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188126323800151357521711 3282189485700227036282567)
          ·
            refine ⟨4923284228550340554423851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3282189485700227036282567 4923284228550340554423851)
            ·
              refine ⟨7384926342825510831635777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923284228550340554423851 7384926342825510831635777)
              ·
                refine ⟨5538694757119133123726833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7384926342825510831635777 5538694757119133123726833)
                ·
                  refine ⟨4154021067839349842795125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5538694757119133123726833 4154021067839349842795125)
                  ·
                    refine ⟨389439475109939047762043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4154021067839349842795125 389439475109939047762043)
                    ·
                      rfl

theorem cell23_2275292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2275292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275292 prefixEnd_2275292 := by exact prefixLift 2275292
  have htrace : WordTrace (prefixWord ++ tailWord_2275292) baseStart_2275292 baseEnd_2275292 := by
    simpa [prefixWord, tailWord_2275292, baseEnd_2275292] using wordTrace_append hprefix tailTrace_2275292
  have hstable : (prefixWord ++ tailWord_2275292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275292).length < 2 ^ (prefixWord ++ tailWord_2275292).sum := by decide
  have hdescent : baseEnd_2275292 < baseStart_2275292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275332 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2275332 : Nat := 118140960795 + 2275332 * 2 ^ 59
def prefixEnd_2275332 : Nat := 4983230072969 + 3 ^ 40 * 2275332 * 2
def baseEnd_2275332 : Nat := 1168338964555996986785945

theorem tailTrace_2275332 : CollatzResearch.WordTrace tailWord_2275332 prefixEnd_2275332 1168338964555996986785945 := by
  unfold tailWord_2275332
  simp only [CollatzResearch.WordTrace]
  refine ⟨41494087896434117306510125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55325450528578823075346833 41494087896434117306510125)
  ·
    refine ⟨15560282961162793989941297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41494087896434117306510125 15560282961162793989941297)
    ·
      refine ⟨11670212220872095492455973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15560282961162793989941297 11670212220872095492455973)
      ·
        refine ⟨2188164791413517904835495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11670212220872095492455973 2188164791413517904835495)
        ·
          refine ⟨3282247187120276857253243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188164791413517904835495 3282247187120276857253243)
          ·
            refine ⟨4923370780680415285879865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3282247187120276857253243 4923370780680415285879865)
            ·
              refine ⟨3692528085510311464409899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4923370780680415285879865 3692528085510311464409899)
              ·
                refine ⟨5538792128265467196614849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3692528085510311464409899 5538792128265467196614849)
                ·
                  refine ⟨4154094096199100397461137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5538792128265467196614849 4154094096199100397461137)
                  ·
                    refine ⟨3115570572149325298095853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4154094096199100397461137 3115570572149325298095853)
                    ·
                      refine ⟨1168338964555996986785945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3115570572149325298095853 1168338964555996986785945)
                      ·
                        rfl

theorem cell23_2275332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2275332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275332 prefixEnd_2275332 := by exact prefixLift 2275332
  have htrace : WordTrace (prefixWord ++ tailWord_2275332) baseStart_2275332 baseEnd_2275332 := by
    simpa [prefixWord, tailWord_2275332, baseEnd_2275332] using wordTrace_append hprefix tailTrace_2275332
  have hstable : (prefixWord ++ tailWord_2275332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275332).length < 2 ^ (prefixWord ++ tailWord_2275332).sum := by decide
  have hdescent : baseEnd_2275332 < baseStart_2275332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275362 : List Nat := [3, 3, 1, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_2275362 : Nat := 118140960795 + 2275362 * 2 ^ 59
def prefixEnd_2275362 : Nat := 4983230072969 + 3 ^ 40 * 2275362 * 2
def baseEnd_2275362 : Nat := 1168354368975631869410807

theorem tailTrace_2275362 : CollatzResearch.WordTrace tailWord_2275362 prefixEnd_2275362 1168354368975631869410807 := by
  unfold tailWord_2275362
  simp only [CollatzResearch.WordTrace]
  refine ⟨20747317495689887434153085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55326179988506366491074893 20747317495689887434153085)
  ·
    refine ⟨7780244060883707787807407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20747317495689887434153085 7780244060883707787807407)
    ·
      refine ⟨11670366091325561681711111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7780244060883707787807407 11670366091325561681711111)
      ·
        refine ⟨17505549136988342522566667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11670366091325561681711111 17505549136988342522566667)
        ·
          refine ⟨26258323705482513783850001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17505549136988342522566667 26258323705482513783850001)
          ·
            refine ⟨19693742779111885337887501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26258323705482513783850001 19693742779111885337887501)
            ·
              refine ⟨7385153542166957001707813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19693742779111885337887501 7385153542166957001707813)
              ·
                refine ⟨1384716289156304437820215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7385153542166957001707813 1384716289156304437820215)
                ·
                  refine ⟨2077074433734456656730323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1384716289156304437820215 2077074433734456656730323)
                  ·
                    refine ⟨3115611650601684985095485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2077074433734456656730323 3115611650601684985095485)
                    ·
                      refine ⟨1168354368975631869410807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3115611650601684985095485 1168354368975631869410807)
                      ·
                        rfl

theorem cell23_2275362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_2275362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275362 prefixEnd_2275362 := by exact prefixLift 2275362
  have htrace : WordTrace (prefixWord ++ tailWord_2275362) baseStart_2275362 baseEnd_2275362 := by
    simpa [prefixWord, tailWord_2275362, baseEnd_2275362] using wordTrace_append hprefix tailTrace_2275362
  have hstable : (prefixWord ++ tailWord_2275362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275362).length < 2 ^ (prefixWord ++ tailWord_2275362).sum := by decide
  have hdescent : baseEnd_2275362 < baseStart_2275362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275378 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_2275378 : Nat := 118140960795 + 2275378 * 2 ^ 59
def prefixEnd_2275378 : Nat := 4983230072969 + 3 ^ 40 * 2275378 * 2
def baseEnd_2275378 : Nat := 389454194888701268936911

theorem tailTrace_2275378 : CollatzResearch.WordTrace tailWord_2275378 prefixEnd_2275378 389454194888701268936911 := by
  unfold tailWord_2275378
  simp only [CollatzResearch.WordTrace]
  refine ⟨20747463387675396117298697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55326569033801056312796525 20747463387675396117298697)
  ·
    refine ⟨15560597540756547087974023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20747463387675396117298697 15560597540756547087974023)
    ·
      refine ⟨23340896311134820631961035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15560597540756547087974023 23340896311134820631961035)
      ·
        refine ⟨35011344466702230947941553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23340896311134820631961035 35011344466702230947941553)
        ·
          refine ⟨26258508350026673210956165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35011344466702230947941553 26258508350026673210956165)
          ·
            refine ⟨4923470315630001227054281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26258508350026673210956165 4923470315630001227054281)
            ·
              refine ⟨3692602736722500920290711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4923470315630001227054281 3692602736722500920290711)
              ·
                refine ⟨5538904105083751380436067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3692602736722500920290711 5538904105083751380436067)
                ·
                  refine ⟨8308356157625627070654101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5538904105083751380436067 8308356157625627070654101)
                  ·
                    refine ⟨389454194888701268936911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8308356157625627070654101 389454194888701268936911)
                    ·
                      rfl

theorem cell23_2275378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_2275378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275378 prefixEnd_2275378 := by exact prefixLift 2275378
  have htrace : WordTrace (prefixWord ++ tailWord_2275378) baseStart_2275378 baseEnd_2275378 := by
    simpa [prefixWord, tailWord_2275378, baseEnd_2275378] using wordTrace_append hprefix tailTrace_2275378
  have hstable : (prefixWord ++ tailWord_2275378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275378).length < 2 ^ (prefixWord ++ tailWord_2275378).sum := by decide
  have hdescent : baseEnd_2275378 < baseStart_2275378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275381 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_2275381 : Nat := 118140960795 + 2275381 * 2 ^ 59
def prefixEnd_2275381 : Nat := 4983230072969 + 3 ^ 40 * 2275381 * 2
def baseEnd_2275381 : Nat := 1168364125108067295073219

theorem tailTrace_2275381 : CollatzResearch.WordTrace tailWord_2275381 prefixEnd_2275381 1168364125108067295073219 := by
  unfold tailWord_2275381
  simp only [CollatzResearch.WordTrace]
  refine ⟨82989962969690715981553997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55326641979793810654369331 82989962969690715981553997)
  ·
    refine ⟨31121236113634018493082749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82989962969690715981553997 31121236113634018493082749)
    ·
      refine ⟨11670463542612756934906031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31121236113634018493082749 11670463542612756934906031)
      ·
        refine ⟨17505695313919135402359047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11670463542612756934906031 17505695313919135402359047)
        ·
          refine ⟨26258542970878703103538571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17505695313919135402359047 26258542970878703103538571)
          ·
            refine ⟨39387814456318054655307857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26258542970878703103538571 39387814456318054655307857)
            ·
              refine ⟨29540860842238540991480893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39387814456318054655307857 29540860842238540991480893)
              ·
                refine ⟨11077822815839452871805335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29540860842238540991480893 11077822815839452871805335)
                ·
                  refine ⟨16616734223759179307708003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11077822815839452871805335 16616734223759179307708003)
                  ·
                    refine ⟨24925101335638768961562005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16616734223759179307708003 24925101335638768961562005)
                    ·
                      refine ⟨1168364125108067295073219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24925101335638768961562005 1168364125108067295073219)
                      ·
                        rfl

theorem cell23_2275381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_2275381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275381 prefixEnd_2275381 := by exact prefixLift 2275381
  have htrace : WordTrace (prefixWord ++ tailWord_2275381) baseStart_2275381 baseEnd_2275381 := by
    simpa [prefixWord, tailWord_2275381, baseEnd_2275381] using wordTrace_append hprefix tailTrace_2275381
  have hstable : (prefixWord ++ tailWord_2275381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275381).length < 2 ^ (prefixWord ++ tailWord_2275381).sum := by decide
  have hdescent : baseEnd_2275381 < baseStart_2275381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275388 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_2275388 : Nat := 118140960795 + 2275388 * 2 ^ 59
def prefixEnd_2275388 : Nat := 4983230072969 + 3 ^ 40 * 2275388 * 2
def baseEnd_2275388 : Nat := 1168367719472648767685687

theorem tailTrace_2275388 : CollatzResearch.WordTrace tailWord_2275388 prefixEnd_2275388 1168367719472648767685687 := by
  unfold tailWord_2275388
  simp only [CollatzResearch.WordTrace]
  refine ⟨41495109140332678088529409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55326812187110237451372545 41495109140332678088529409)
  ·
    refine ⟨31121331855249508566397057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41495109140332678088529409 31121331855249508566397057)
    ·
      refine ⟨23340998891437131424797793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31121331855249508566397057 23340998891437131424797793)
      ·
        refine ⟨17505749168577848568598345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23340998891437131424797793 17505749168577848568598345)
        ·
          refine ⟨13129311876433386426448759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17505749168577848568598345 13129311876433386426448759)
          ·
            refine ⟨19693967814650079639673139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13129311876433386426448759 19693967814650079639673139)
            ·
              refine ⟨29540951721975119459509709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19693967814650079639673139 29540951721975119459509709)
              ·
                refine ⟨11077856895740669797316141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29540951721975119459509709 11077856895740669797316141)
                ·
                  refine ⟨4154196335902751173993553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11077856895740669797316141 4154196335902751173993553)
                  ·
                    refine ⟨3115647251927063380495165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4154196335902751173993553 3115647251927063380495165)
                    ·
                      refine ⟨1168367719472648767685687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3115647251927063380495165 1168367719472648767685687)
                      ·
                        rfl

theorem cell23_2275388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_2275388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275388 prefixEnd_2275388 := by exact prefixLift 2275388
  have htrace : WordTrace (prefixWord ++ tailWord_2275388) baseStart_2275388 baseEnd_2275388 := by
    simpa [prefixWord, tailWord_2275388, baseEnd_2275388] using wordTrace_append hprefix tailTrace_2275388
  have hstable : (prefixWord ++ tailWord_2275388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275388).length < 2 ^ (prefixWord ++ tailWord_2275388).sum := by decide
  have hdescent : baseEnd_2275388 < baseStart_2275388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275509 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_2275509 : Nat := 118140960795 + 2275509 * 2 ^ 59
def prefixEnd_2275509 : Nat := 4983230072969 + 3 ^ 40 * 2275509 * 2
def baseEnd_2275509 : Nat := 1168429850631842794272631

theorem tailTrace_2275509 : CollatzResearch.WordTrace tailWord_2275509 prefixEnd_2275509 1168429850631842794272631 := by
  unfold tailWord_2275509
  simp only [CollatzResearch.WordTrace]
  refine ⟨82994631513226993842213581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55329754342151329228142387 82994631513226993842213581)
  ·
    refine ⟨31122986817460122690830093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82994631513226993842213581 31122986817460122690830093)
    ·
      refine ⟨11671120056547546009061285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31122986817460122690830093 11671120056547546009061285)
      ·
        refine ⟨2188335010602664876698991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11671120056547546009061285 2188335010602664876698991)
        ·
          refine ⟨3282502515903997315048487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188335010602664876698991 3282502515903997315048487)
          ·
            refine ⟨4923753773855995972572731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3282502515903997315048487 4923753773855995972572731)
            ·
              refine ⟨7385630660783993958859097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923753773855995972572731 7385630660783993958859097)
              ·
                refine ⟨5539222995587995469144323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7385630660783993958859097 5539222995587995469144323)
                ·
                  refine ⟨8308834493381993203716485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5539222995587995469144323 8308834493381993203716485)
                  ·
                    refine ⟨1557906467509123725696841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8308834493381993203716485 1557906467509123725696841)
                    ·
                      refine ⟨1168429850631842794272631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1557906467509123725696841 1168429850631842794272631)
                      ·
                        rfl

theorem cell23_2275509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_2275509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275509 prefixEnd_2275509 := by exact prefixLift 2275509
  have htrace : WordTrace (prefixWord ++ tailWord_2275509) baseStart_2275509 baseEnd_2275509 := by
    simpa [prefixWord, tailWord_2275509, baseEnd_2275509] using wordTrace_append hprefix tailTrace_2275509
  have hstable : (prefixWord ++ tailWord_2275509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275509).length < 2 ^ (prefixWord ++ tailWord_2275509).sum := by decide
  have hdescent : baseEnd_2275509 < baseStart_2275509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275542 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2275542 : Nat := 118140960795 + 2275542 * 2 ^ 59
def prefixEnd_2275542 : Nat := 4983230072969 + 3 ^ 40 * 2275542 * 2
def baseEnd_2275542 : Nat := 1168446795493441165159979

theorem tailTrace_2275542 : CollatzResearch.WordTrace tailWord_2275542 prefixEnd_2275542 1168446795493441165159979 := by
  unfold tailWord_2275542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5187239695131715029885305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55330556748071626985443253 5187239695131715029885305)
  ·
    refine ⟨3890429771348786272413979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5187239695131715029885305 3890429771348786272413979)
    ·
      refine ⟨5835644657023179408620969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3890429771348786272413979 5835644657023179408620969)
      ·
        refine ⟨4376733492767384556465727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5835644657023179408620969 4376733492767384556465727)
        ·
          refine ⟨6565100239151076834698591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4376733492767384556465727 6565100239151076834698591)
          ·
            refine ⟨9847650358726615252047887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6565100239151076834698591 9847650358726615252047887)
            ·
              refine ⟨14771475538089922878071831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9847650358726615252047887 14771475538089922878071831)
              ·
                refine ⟨22157213307134884317107747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14771475538089922878071831 22157213307134884317107747)
                ·
                  refine ⟨33235819960702326475661621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22157213307134884317107747 33235819960702326475661621)
                  ·
                    refine ⟨3115858121315843107093277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33235819960702326475661621 3115858121315843107093277)
                    ·
                      refine ⟨1168446795493441165159979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3115858121315843107093277 1168446795493441165159979)
                      ·
                        rfl

theorem cell23_2275542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2275542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275542 prefixEnd_2275542 := by exact prefixLift 2275542
  have htrace : WordTrace (prefixWord ++ tailWord_2275542) baseStart_2275542 baseEnd_2275542 := by
    simpa [prefixWord, tailWord_2275542, baseEnd_2275542] using wordTrace_append hprefix tailTrace_2275542
  have hstable : (prefixWord ++ tailWord_2275542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275542).length < 2 ^ (prefixWord ++ tailWord_2275542).sum := by decide
  have hdescent : baseEnd_2275542 < baseStart_2275542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275578 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_2275578 : Nat := 118140960795 + 2275578 * 2 ^ 59
def prefixEnd_2275578 : Nat := 4983230072969 + 3 ^ 40 * 2275578 * 2
def baseEnd_2275578 : Nat := 1168465280797003024309813

theorem tailTrace_2275578 : CollatzResearch.WordTrace tailWord_2275578 prefixEnd_2275578 1168465280797003024309813 := by
  unfold tailWord_2275578
  simp only [CollatzResearch.WordTrace]
  refine ⟨20749287037494254656618847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55331432099984679084316925 20749287037494254656618847)
  ·
    refine ⟨31123930556241381984928271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20749287037494254656618847 31123930556241381984928271)
    ·
      refine ⟨46685895834362072977392407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31123930556241381984928271 46685895834362072977392407)
      ·
        refine ⟨70028843751543109466088611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46685895834362072977392407 70028843751543109466088611)
        ·
          refine ⟨105043265627314664199132917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70028843751543109466088611 105043265627314664199132917)
          ·
            refine ⟨9847806152560749768668711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105043265627314664199132917 9847806152560749768668711)
            ·
              refine ⟨14771709228841124653003067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9847806152560749768668711 14771709228841124653003067)
              ·
                refine ⟨22157563843261686979504601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14771709228841124653003067 22157563843261686979504601)
                ·
                  refine ⟨16618172882446265234628451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22157563843261686979504601 16618172882446265234628451)
                  ·
                    refine ⟨24927259323669397851942677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16618172882446265234628451 24927259323669397851942677)
                    ·
                      refine ⟨1168465280797003024309813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24927259323669397851942677 1168465280797003024309813)
                      ·
                        rfl

theorem cell23_2275578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_2275578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275578 prefixEnd_2275578 := by exact prefixLift 2275578
  have htrace : WordTrace (prefixWord ++ tailWord_2275578) baseStart_2275578 baseEnd_2275578 := by
    simpa [prefixWord, tailWord_2275578, baseEnd_2275578] using wordTrace_append hprefix tailTrace_2275578
  have hstable : (prefixWord ++ tailWord_2275578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275578).length < 2 ^ (prefixWord ++ tailWord_2275578).sum := by decide
  have hdescent : baseEnd_2275578 < baseStart_2275578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275582 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_2275582 : Nat := 118140960795 + 2275582 * 2 ^ 59
def prefixEnd_2275582 : Nat := 4983230072969 + 3 ^ 40 * 2275582 * 2
def baseEnd_2275582 : Nat := 1168467334719621008659795

theorem tailTrace_2275582 : CollatzResearch.WordTrace tailWord_2275582 prefixEnd_2275582 1168467334719621008659795 := by
  unfold tailWord_2275582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10374661755245315913702625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55331529361308351539747333 10374661755245315913702625)
  ·
    refine ⟨7780996316433986935276969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10374661755245315913702625 7780996316433986935276969)
    ·
      refine ⟨5835747237325490201457727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7780996316433986935276969 5835747237325490201457727)
      ·
        refine ⟨8753620855988235302186591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5835747237325490201457727 8753620855988235302186591)
        ·
          refine ⟨13130431283982352953279887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8753620855988235302186591 13130431283982352953279887)
          ·
            refine ⟨19695646925973529429919831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13130431283982352953279887 19695646925973529429919831)
            ·
              refine ⟨29543470388960294144879747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19695646925973529429919831 29543470388960294144879747)
              ·
                refine ⟨44315205583440441217319621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29543470388960294144879747 44315205583440441217319621)
                ·
                  refine ⟨8309101046895082728247429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44315205583440441217319621 8309101046895082728247429)
                  ·
                    refine ⟨1557956446292828011546393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8309101046895082728247429 1557956446292828011546393)
                    ·
                      refine ⟨1168467334719621008659795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1557956446292828011546393 1168467334719621008659795)
                      ·
                        rfl

theorem cell23_2275582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_2275582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275582 prefixEnd_2275582 := by exact prefixLift 2275582
  have htrace : WordTrace (prefixWord ++ tailWord_2275582) baseStart_2275582 baseEnd_2275582 := by
    simpa [prefixWord, tailWord_2275582, baseEnd_2275582] using wordTrace_append hprefix tailTrace_2275582
  have hstable : (prefixWord ++ tailWord_2275582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275582).length < 2 ^ (prefixWord ++ tailWord_2275582).sum := by decide
  have hdescent : baseEnd_2275582 < baseStart_2275582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275585 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_2275585 : Nat := 118140960795 + 2275585 * 2 ^ 59
def prefixEnd_2275585 : Nat := 4983230072969 + 3 ^ 40 * 2275585 * 2
def baseEnd_2275585 : Nat := 1168468875161584496922281

theorem tailTrace_2275585 : CollatzResearch.WordTrace tailWord_2275585 prefixEnd_2275585 1168468875161584496922281 := by
  unfold tailWord_2275585
  simp only [CollatzResearch.WordTrace]
  refine ⟨82997403460951658821980209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55331602307301105881320139 82997403460951658821980209)
  ·
    refine ⟨62248052595713744116485157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82997403460951658821980209 62248052595713744116485157)
    ·
      refine ⟨11671509861696327021840967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62248052595713744116485157 11671509861696327021840967)
      ·
        refine ⟨17507264792544490532761451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11671509861696327021840967 17507264792544490532761451)
        ·
          refine ⟨26260897188816735799142177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17507264792544490532761451 26260897188816735799142177)
          ·
            refine ⟨19695672891612551849356633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26260897188816735799142177 19695672891612551849356633)
            ·
              refine ⟨14771754668709413887017475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19695672891612551849356633 14771754668709413887017475)
              ·
                refine ⟨22157632003064120830526213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14771754668709413887017475 22157632003064120830526213)
                ·
                  refine ⟨4154556000574522655723665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22157632003064120830526213 4154556000574522655723665)
                  ·
                    refine ⟨3115917000430891991792749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4154556000574522655723665 3115917000430891991792749)
                    ·
                      refine ⟨1168468875161584496922281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3115917000430891991792749 1168468875161584496922281)
                      ·
                        rfl

theorem cell23_2275585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_2275585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275585 prefixEnd_2275585 := by exact prefixLift 2275585
  have htrace : WordTrace (prefixWord ++ tailWord_2275585) baseStart_2275585 baseEnd_2275585 := by
    simpa [prefixWord, tailWord_2275585, baseEnd_2275585] using wordTrace_append hprefix tailTrace_2275585
  have hstable : (prefixWord ++ tailWord_2275585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275585).length < 2 ^ (prefixWord ++ tailWord_2275585).sum := by decide
  have hdescent : baseEnd_2275585 < baseStart_2275585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275592 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 3, 4]
def baseStart_2275592 : Nat := 118140960795 + 2275592 * 2 ^ 59
def prefixEnd_2275592 : Nat := 4983230072969 + 3 ^ 40 * 2275592 * 2
def baseEnd_2275592 : Nat := 389490823175388656511583

theorem tailTrace_2275592 : CollatzResearch.WordTrace tailWord_2275592 prefixEnd_2275592 389490823175388656511583 := by
  unfold tailWord_2275592
  simp only [CollatzResearch.WordTrace]
  refine ⟨41498829385963149508742515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55331772514617532678323353 41498829385963149508742515)
  ·
    refine ⟨62248244078944724263113773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41498829385963149508742515 62248244078944724263113773)
    ·
      refine ⟨23343091529604271598667665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62248244078944724263113773 23343091529604271598667665)
      ·
        refine ⟨17507318647203203699000749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23343091529604271598667665 17507318647203203699000749)
        ·
          refine ⟨6565244492701201387125281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17507318647203203699000749 6565244492701201387125281)
          ·
            refine ⟨4923933369525901040343961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6565244492701201387125281 4923933369525901040343961)
            ·
              refine ⟨3692950027144425780257971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4923933369525901040343961 3692950027144425780257971)
              ·
                refine ⟨5539425040716638670386957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3692950027144425780257971 5539425040716638670386957)
                ·
                  refine ⟨2077284390268739501395109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5539425040716638670386957 2077284390268739501395109)
                  ·
                    refine ⟨389490823175388656511583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2077284390268739501395109 389490823175388656511583)
                    ·
                      rfl

theorem cell23_2275592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_2275592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275592 prefixEnd_2275592 := by exact prefixLift 2275592
  have htrace : WordTrace (prefixWord ++ tailWord_2275592) baseStart_2275592 baseEnd_2275592 := by
    simpa [prefixWord, tailWord_2275592, baseEnd_2275592] using wordTrace_append hprefix tailTrace_2275592
  have hstable : (prefixWord ++ tailWord_2275592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275592).length < 2 ^ (prefixWord ++ tailWord_2275592).sum := by decide
  have hdescent : baseEnd_2275592 < baseStart_2275592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275608 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2275608 : Nat := 118140960795 + 2275608 * 2 ^ 59
def prefixEnd_2275608 : Nat := 4983230072969 + 3 ^ 40 * 2275608 * 2
def baseEnd_2275608 : Nat := 1168480685216637906934675

theorem tailTrace_2275608 : CollatzResearch.WordTrace tailWord_2275608 prefixEnd_2275608 1168480685216637906934675 := by
  unfold tailWord_2275608
  simp only [CollatzResearch.WordTrace]
  refine ⟨41499121169934166875033739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55332161559912222500044985 41499121169934166875033739)
  ·
    refine ⟨62248681754901250312550609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41499121169934166875033739 62248681754901250312550609)
    ·
      refine ⟨46686511316175937734412957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62248681754901250312550609 46686511316175937734412957)
      ·
        refine ⟨17507441743565976650404859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46686511316175937734412957 17507441743565976650404859)
        ·
          refine ⟨26261162615348964975607289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17507441743565976650404859 26261162615348964975607289)
          ·
            refine ⟨19695871961511723731705467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26261162615348964975607289 19695871961511723731705467)
            ·
              refine ⟨29543807942267585597558201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19695871961511723731705467 29543807942267585597558201)
              ·
                refine ⟨22157855956700689198168651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29543807942267585597558201 22157855956700689198168651)
                ·
                  refine ⟨33236783935051033797252977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22157855956700689198168651 33236783935051033797252977)
                  ·
                    refine ⟨24927587951288275347939733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33236783935051033797252977 24927587951288275347939733)
                    ·
                      refine ⟨1168480685216637906934675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24927587951288275347939733 1168480685216637906934675)
                      ·
                        rfl

theorem cell23_2275608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2275608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275608 prefixEnd_2275608 := by exact prefixLift 2275608
  have htrace : WordTrace (prefixWord ++ tailWord_2275608) baseStart_2275608 baseEnd_2275608 := by
    simpa [prefixWord, tailWord_2275608, baseEnd_2275608] using wordTrace_append hprefix tailTrace_2275608
  have hstable : (prefixWord ++ tailWord_2275608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275608).length < 2 ^ (prefixWord ++ tailWord_2275608).sum := by decide
  have hdescent : baseEnd_2275608 < baseStart_2275608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275635 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 1, 5]
def baseStart_2275635 : Nat := 118140960795 + 2275635 * 2 ^ 59
def prefixEnd_2275635 : Nat := 4983230072969 + 3 ^ 40 * 2275635 * 2
def baseEnd_2275635 : Nat := 389498183064769767099017

theorem tailTrace_2275635 : CollatzResearch.WordTrace tailWord_2275635 prefixEnd_2275635 389498183064769767099017 := by
  unfold tailWord_2275635
  simp only [CollatzResearch.WordTrace]
  refine ⟨82999227110770517361300359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55332818073847011574200239 82999227110770517361300359)
  ·
    refine ⟨124498840666155776041950539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82999227110770517361300359 124498840666155776041950539)
    ·
      refine ⟨186748260999233664062925809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124498840666155776041950539 186748260999233664062925809)
      ·
        refine ⟨140061195749425248047194357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186748260999233664062925809 140061195749425248047194357)
        ·
          refine ⟨13130737101508617004424471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140061195749425248047194357 13130737101508617004424471)
          ·
            refine ⟨19696105652262925506636707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13130737101508617004424471 19696105652262925506636707)
            ·
              refine ⟨29544158478394388259955061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19696105652262925506636707 29544158478394388259955061)
              ·
                refine ⟨2769764857349473899370787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29544158478394388259955061 2769764857349473899370787)
                ·
                  refine ⟨4154647286024210849056181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769764857349473899370787 4154647286024210849056181)
                  ·
                    refine ⟨389498183064769767099017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4154647286024210849056181 389498183064769767099017)
                    ·
                      rfl

theorem cell23_2275635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 5].length) (baseStart_2275635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275635 prefixEnd_2275635 := by exact prefixLift 2275635
  have htrace : WordTrace (prefixWord ++ tailWord_2275635) baseStart_2275635 baseEnd_2275635 := by
    simpa [prefixWord, tailWord_2275635, baseEnd_2275635] using wordTrace_append hprefix tailTrace_2275635
  have hstable : (prefixWord ++ tailWord_2275635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275635).length < 2 ^ (prefixWord ++ tailWord_2275635).sum := by decide
  have hdescent : baseEnd_2275635 < baseStart_2275635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275642 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2]
def baseStart_2275642 : Nat := 118140960795 + 2275642 * 2 ^ 59
def prefixEnd_2275642 : Nat := 4983230072969 + 3 ^ 40 * 2275642 * 2
def baseEnd_2275642 : Nat := 1168498143558890773909519

theorem tailTrace_2275642 : CollatzResearch.WordTrace tailWord_2275642 prefixEnd_2275642 1168498143558890773909519 := by
  unfold tailWord_2275642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20749870605436289389201295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55332988281163438371203453 20749870605436289389201295)
  ·
    refine ⟨31124805908154434083801943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20749870605436289389201295 31124805908154434083801943)
    ·
      refine ⟨46687208862231651125702915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31124805908154434083801943 46687208862231651125702915)
      ·
        refine ⟨70030813293347476688554373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46687208862231651125702915 70030813293347476688554373)
        ·
          refine ⟨13130777492502651879103945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70030813293347476688554373 13130777492502651879103945)
          ·
            refine ⟨9848083119376988909327959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13130777492502651879103945 9848083119376988909327959)
            ·
              refine ⟨14772124679065483363991939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9848083119376988909327959 14772124679065483363991939)
              ·
                refine ⟨22158187018598225045987909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14772124679065483363991939 22158187018598225045987909)
                ·
                  refine ⟨4154660065987167196122733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22158187018598225045987909 4154660065987167196122733)
                  ·
                    refine ⟨1557997524745187698546025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4154660065987167196122733 1557997524745187698546025)
                    ·
                      refine ⟨1168498143558890773909519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1557997524745187698546025 1168498143558890773909519)
                      ·
                        rfl

theorem cell23_2275642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2].length) (baseStart_2275642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275642 prefixEnd_2275642 := by exact prefixLift 2275642
  have htrace : WordTrace (prefixWord ++ tailWord_2275642) baseStart_2275642 baseEnd_2275642 := by
    simpa [prefixWord, tailWord_2275642, baseEnd_2275642] using wordTrace_append hprefix tailTrace_2275642
  have hstable : (prefixWord ++ tailWord_2275642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275642).length < 2 ^ (prefixWord ++ tailWord_2275642).sum := by decide
  have hdescent : baseEnd_2275642 < baseStart_2275642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275648 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 5, 6]
def baseStart_2275648 : Nat := 118140960795 + 2275648 * 2 ^ 59
def prefixEnd_2275648 : Nat := 4983230072969 + 3 ^ 40 * 2275648 * 2
def baseEnd_2275648 : Nat := 389500408147605916811497

theorem tailTrace_2275648 : CollatzResearch.WordTrace tailWord_2275648 prefixEnd_2275648 389500408147605916811497 := by
  unfold tailWord_2275648
  simp only [CollatzResearch.WordTrace]
  refine ⟨41499850629861710290761799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55333134173148947054349065 41499850629861710290761799)
  ·
    refine ⟨62249775944792565436142699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41499850629861710290761799 62249775944792565436142699)
    ·
      refine ⟨93374663917188848154214049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62249775944792565436142699 93374663917188848154214049)
      ·
        refine ⟨70030997937891636115660537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93374663917188848154214049 70030997937891636115660537)
        ·
          refine ⟨52523248453418727086745403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70030997937891636115660537 52523248453418727086745403)
          ·
            refine ⟨78784872680128090630118105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52523248453418727086745403 78784872680128090630118105)
            ·
              refine ⟨59088654510096067972588579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78784872680128090630118105 59088654510096067972588579)
              ·
                refine ⟨88632981765144101958882869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59088654510096067972588579 88632981765144101958882869)
                ·
                  refine ⟨8309342040482259558645269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88632981765144101958882869 8309342040482259558645269)
                  ·
                    refine ⟨389500408147605916811497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8309342040482259558645269 389500408147605916811497)
                    ·
                      rfl

theorem cell23_2275648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_2275648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275648 prefixEnd_2275648 := by exact prefixLift 2275648
  have htrace : WordTrace (prefixWord ++ tailWord_2275648) baseStart_2275648 baseEnd_2275648 := by
    simpa [prefixWord, tailWord_2275648, baseEnd_2275648] using wordTrace_append hprefix tailTrace_2275648
  have hstable : (prefixWord ++ tailWord_2275648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275648).length < 2 ^ (prefixWord ++ tailWord_2275648).sum := by decide
  have hdescent : baseEnd_2275648 < baseStart_2275648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275655 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_2275655 : Nat := 118140960795 + 2275655 * 2 ^ 59
def prefixEnd_2275655 : Nat := 4983230072969 + 3 ^ 40 * 2275655 * 2
def baseEnd_2275655 : Nat := 1168504818807399223046959

theorem tailTrace_2275655 : CollatzResearch.WordTrace tailWord_2275655 prefixEnd_2275655 1168504818807399223046959 := by
  unfold tailWord_2275655
  simp only [CollatzResearch.WordTrace]
  refine ⟨82999956570698060777028419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55333304380465373851352279 82999956570698060777028419)
  ·
    refine ⟨124499934856047091165542629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82999956570698060777028419 124499934856047091165542629)
    ·
      refine ⟨23343737785508829593539243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124499934856047091165542629 23343737785508829593539243)
      ·
        refine ⟨35015606678263244390308865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23343737785508829593539243 35015606678263244390308865)
        ·
          refine ⟨26261705008697433292731649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35015606678263244390308865 26261705008697433292731649)
          ·
            refine ⟨19696278756523074969548737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26261705008697433292731649 19696278756523074969548737)
            ·
              refine ⟨14772209067392306227161553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19696278756523074969548737 14772209067392306227161553)
              ·
                refine ⟨11079156800544229670371165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14772209067392306227161553 11079156800544229670371165)
                ·
                  refine ⟨4154683800204086126389187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11079156800544229670371165 4154683800204086126389187)
                  ·
                    refine ⟨6232025700306129189583781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4154683800204086126389187 6232025700306129189583781)
                    ·
                      refine ⟨1168504818807399223046959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6232025700306129189583781 1168504818807399223046959)
                      ·
                        rfl

theorem cell23_2275655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_2275655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275655 prefixEnd_2275655 := by exact prefixLift 2275655
  have htrace : WordTrace (prefixWord ++ tailWord_2275655) baseStart_2275655 baseEnd_2275655 := by
    simpa [prefixWord, tailWord_2275655, baseEnd_2275655] using wordTrace_append hprefix tailTrace_2275655
  have hstable : (prefixWord ++ tailWord_2275655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275655).length < 2 ^ (prefixWord ++ tailWord_2275655).sum := by decide
  have hdescent : baseEnd_2275655 < baseStart_2275655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275669 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 1, 5]
def baseStart_2275669 : Nat := 118140960795 + 2275669 * 2 ^ 59
def prefixEnd_2275669 : Nat := 4983230072969 + 3 ^ 40 * 2275669 * 2
def baseEnd_2275669 : Nat := 389504002512187389423965

theorem tailTrace_2275669 : CollatzResearch.WordTrace tailWord_2275669 prefixEnd_2275669 389504002512187389423965 := by
  unfold tailWord_2275669
  simp only [CollatzResearch.WordTrace]
  refine ⟨83000467192647341168038061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55333644795098227445358707 83000467192647341168038061)
  ·
    refine ⟨31125175197242752938014273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83000467192647341168038061 31125175197242752938014273)
    ·
      refine ⟨23343881397932064703510705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31125175197242752938014273 23343881397932064703510705)
      ·
        refine ⟨17507911048449048527633029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23343881397932064703510705 17507911048449048527633029)
        ·
          refine ⟨3282733321584196598931193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17507911048449048527633029 3282733321584196598931193)
          ·
            refine ⟨2462049991188147449198395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3282733321584196598931193 2462049991188147449198395)
            ·
              refine ⟨3693074986782221173797593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462049991188147449198395 3693074986782221173797593)
              ·
                refine ⟨2769806240086665880348195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3693074986782221173797593 2769806240086665880348195)
                ·
                  refine ⟨4154709360129998820522293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769806240086665880348195 4154709360129998820522293)
                  ·
                    refine ⟨389504002512187389423965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4154709360129998820522293 389504002512187389423965)
                    ·
                      rfl

theorem cell23_2275669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_2275669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275669 prefixEnd_2275669 := by exact prefixLift 2275669
  have htrace : WordTrace (prefixWord ++ tailWord_2275669) baseStart_2275669 baseEnd_2275669 := by
    simpa [prefixWord, tailWord_2275669, baseEnd_2275669] using wordTrace_append hprefix tailTrace_2275669
  have hstable : (prefixWord ++ tailWord_2275669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275669).length < 2 ^ (prefixWord ++ tailWord_2275669).sum := by decide
  have hdescent : baseEnd_2275669 < baseStart_2275669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275682 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2275682 : Nat := 118140960795 + 2275682 * 2 ^ 59
def prefixEnd_2275682 : Nat := 4983230072969 + 3 ^ 40 * 2275682 * 2
def baseEnd_2275682 : Nat := 389506227595023539136445

theorem tailTrace_2275682 : CollatzResearch.WordTrace tailWord_2275682 prefixEnd_2275682 389506227595023539136445 := by
  unfold tailWord_2275682
  simp only [CollatzResearch.WordTrace]
  refine ⟨20750235335400061097065325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55333960894400162925507533 20750235335400061097065325)
  ·
    refine ⟨7781338250775022911399497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20750235335400061097065325 7781338250775022911399497)
    ·
      refine ⟨5836003688081267183549623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7781338250775022911399497 5836003688081267183549623)
      ·
        refine ⟨8754005532121900775324435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5836003688081267183549623 8754005532121900775324435)
        ·
          refine ⟨13131008298182851162986653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8754005532121900775324435 13131008298182851162986653)
          ·
            refine ⟨4924128111818569186119995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13131008298182851162986653 4924128111818569186119995)
            ·
              refine ⟨7386192167727853779179993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4924128111818569186119995 7386192167727853779179993)
              ·
                refine ⟨5539644125795890334384995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7386192167727853779179993 5539644125795890334384995)
                ·
                  refine ⟨8309466188693835501577493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5539644125795890334384995 8309466188693835501577493)
                  ·
                    refine ⟨389506227595023539136445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8309466188693835501577493 389506227595023539136445)
                    ·
                      rfl

theorem cell23_2275682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2275682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275682 prefixEnd_2275682 := by exact prefixLift 2275682
  have htrace : WordTrace (prefixWord ++ tailWord_2275682) baseStart_2275682 baseEnd_2275682 := by
    simpa [prefixWord, tailWord_2275682, baseEnd_2275682] using wordTrace_append hprefix tailTrace_2275682
  have hstable : (prefixWord ++ tailWord_2275682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275682).length < 2 ^ (prefixWord ++ tailWord_2275682).sum := by decide
  have hdescent : baseEnd_2275682 < baseStart_2275682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275685 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_2275685 : Nat := 118140960795 + 2275685 * 2 ^ 59
def prefixEnd_2275685 : Nat := 4983230072969 + 3 ^ 40 * 2275685 * 2
def baseEnd_2275685 : Nat := 1168520223227034105671821

theorem tailTrace_2275685 : CollatzResearch.WordTrace tailWord_2275685 prefixEnd_2275685 1168520223227034105671821 := by
  unfold tailWord_2275685
  simp only [CollatzResearch.WordTrace]
  refine ⟨83001050760589375900620509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55334033840392917267080339 83001050760589375900620509)
  ·
    refine ⟨31125394035221015962732691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83001050760589375900620509 31125394035221015962732691)
    ·
      refine ⟨46688091052831523944099037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31125394035221015962732691 46688091052831523944099037)
      ·
        refine ⟨17508034144811821479037139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46688091052831523944099037 17508034144811821479037139)
        ·
          refine ⟨26262051217217732218555709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17508034144811821479037139 26262051217217732218555709)
          ·
            refine ⟨9848269206456649581958391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26262051217217732218555709 9848269206456649581958391)
            ·
              refine ⟨14772403809684974372937587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9848269206456649581958391 14772403809684974372937587)
              ·
                refine ⟨22158605714527461559406381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14772403809684974372937587 22158605714527461559406381)
                ·
                  refine ⟨8309477142947798084777393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22158605714527461559406381 8309477142947798084777393)
                  ·
                    refine ⟨6232107857210848563583045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8309477142947798084777393 6232107857210848563583045)
                    ·
                      refine ⟨1168520223227034105671821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6232107857210848563583045 1168520223227034105671821)
                      ·
                        rfl

theorem cell23_2275685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_2275685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275685 prefixEnd_2275685 := by exact prefixLift 2275685
  have htrace : WordTrace (prefixWord ++ tailWord_2275685) baseStart_2275685 baseEnd_2275685 := by
    simpa [prefixWord, tailWord_2275685, baseEnd_2275685] using wordTrace_append hprefix tailTrace_2275685
  have hstable : (prefixWord ++ tailWord_2275685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275685).length < 2 ^ (prefixWord ++ tailWord_2275685).sum := by decide
  have hdescent : baseEnd_2275685 < baseStart_2275685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275705 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 5, 3, 3]
def baseStart_2275705 : Nat := 118140960795 + 2275705 * 2 ^ 59
def prefixEnd_2275705 : Nat := 4983230072969 + 3 ^ 40 * 2275705 * 2
def baseEnd_2275705 : Nat := 1168530492840124027421729

theorem tailTrace_2275705 : CollatzResearch.WordTrace tailWord_2275705 prefixEnd_2275705 1168530492840124027421729 := by
  unfold tailWord_2275705
  simp only [CollatzResearch.WordTrace]
  refine ⟨83001780220516919316348569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55334520147011279544232379 83001780220516919316348569)
  ·
    refine ⟨62251335165387689487261427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83001780220516919316348569 62251335165387689487261427)
    ·
      refine ⟨93377002748081534230892141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62251335165387689487261427 93377002748081534230892141)
      ·
        refine ⟨35016376030530575336584553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93377002748081534230892141 35016376030530575336584553)
        ·
          refine ⟨26262282022897931502438415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35016376030530575336584553 26262282022897931502438415)
          ·
            refine ⟨39393423034346897253657623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26262282022897931502438415 39393423034346897253657623)
            ·
              refine ⟨59090134551520345880486435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39393423034346897253657623 59090134551520345880486435)
              ·
                refine ⟨88635201827280518820729653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59090134551520345880486435 88635201827280518820729653)
                ·
                  refine ⟨8309550171307548639443405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88635201827280518820729653 8309550171307548639443405)
                  ·
                    refine ⟨3116081314240330739791277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8309550171307548639443405 3116081314240330739791277)
                    ·
                      refine ⟨1168530492840124027421729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3116081314240330739791277 1168530492840124027421729)
                      ·
                        rfl

theorem cell23_2275705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_2275705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275705 prefixEnd_2275705 := by exact prefixLift 2275705
  have htrace : WordTrace (prefixWord ++ tailWord_2275705) baseStart_2275705 baseEnd_2275705 := by
    simpa [prefixWord, tailWord_2275705, baseEnd_2275705] using wordTrace_append hprefix tailTrace_2275705
  have hstable : (prefixWord ++ tailWord_2275705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275705).length < 2 ^ (prefixWord ++ tailWord_2275705).sum := by decide
  have hdescent : baseEnd_2275705 < baseStart_2275705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275749 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 1, 3, 2]
def baseStart_2275749 : Nat := 118140960795 + 2275749 * 2 ^ 59
def prefixEnd_2275749 : Nat := 4983230072969 + 3 ^ 40 * 2275749 * 2
def baseEnd_2275749 : Nat := 1168553085988921855271527

theorem tailTrace_2275749 : CollatzResearch.WordTrace tailWord_2275749 prefixEnd_2275749 1168553085988921855271527 := by
  unfold tailWord_2275749
  simp only [CollatzResearch.WordTrace]
  refine ⟨83003385032357514830950301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55335590021571676553966867 83003385032357514830950301)
  ·
    refine ⟨31126269387134068061606363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83003385032357514830950301 31126269387134068061606363)
    ·
      refine ⟨46689404080701102092409545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31126269387134068061606363 46689404080701102092409545)
      ·
        refine ⟨35017053060525826569307159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46689404080701102092409545 35017053060525826569307159)
        ·
          refine ⟨52525579590788739853960739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35017053060525826569307159 52525579590788739853960739)
          ·
            refine ⟨78788369386183109780941109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52525579590788739853960739 78788369386183109780941109)
            ·
              refine ⟨7386409629954666541963229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78788369386183109780941109 7386409629954666541963229)
              ·
                refine ⟨2769903611232999953236211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7386409629954666541963229 2769903611232999953236211)
                ·
                  refine ⟨4154855416849499929854317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769903611232999953236211 4154855416849499929854317)
                  ·
                    refine ⟨1558070781318562473695369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4154855416849499929854317 1558070781318562473695369)
                    ·
                      refine ⟨1168553085988921855271527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558070781318562473695369 1168553085988921855271527)
                      ·
                        rfl

theorem cell23_2275749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_2275749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275749 prefixEnd_2275749 := by exact prefixLift 2275749
  have htrace : WordTrace (prefixWord ++ tailWord_2275749) baseStart_2275749 baseEnd_2275749 := by
    simpa [prefixWord, tailWord_2275749, baseEnd_2275749] using wordTrace_append hprefix tailTrace_2275749
  have hstable : (prefixWord ++ tailWord_2275749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275749).length < 2 ^ (prefixWord ++ tailWord_2275749).sum := by decide
  have hdescent : baseEnd_2275749 < baseStart_2275749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275772 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_2275772 : Nat := 118140960795 + 2275772 * 2 ^ 59
def prefixEnd_2275772 : Nat := 4983230072969 + 3 ^ 40 * 2275772 * 2
def baseEnd_2275772 : Nat := 389521632014658421761307

theorem tailTrace_2275772 : CollatzResearch.WordTrace tailWord_2275772 prefixEnd_2275772 389521632014658421761307 := by
  unfold tailWord_2275772
  simp only [CollatzResearch.WordTrace]
  refine ⟨41502111955637094879518785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55336149274182793172691713 41502111955637094879518785)
  ·
    refine ⟨31126583966727821159639089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41502111955637094879518785 31126583966727821159639089)
    ·
      refine ⟨23344937975045865869729317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31126583966727821159639089 23344937975045865869729317)
      ·
        refine ⟨4377175870321099850574247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23344937975045865869729317 4377175870321099850574247)
        ·
          refine ⟨6565763805481649775861371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4377175870321099850574247 6565763805481649775861371)
          ·
            refine ⟨9848645708222474663792057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6565763805481649775861371 9848645708222474663792057)
            ·
              refine ⟨7386484281166855997844043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9848645708222474663792057 7386484281166855997844043)
              ·
                refine ⟨11079726421750283996766065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7386484281166855997844043 11079726421750283996766065)
                ·
                  refine ⟨8309794816312712997574549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11079726421750283996766065 8309794816312712997574549)
                  ·
                    refine ⟨389521632014658421761307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8309794816312712997574549 389521632014658421761307)
                    ·
                      rfl

theorem cell23_2275772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_2275772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275772 prefixEnd_2275772 := by exact prefixLift 2275772
  have htrace : WordTrace (prefixWord ++ tailWord_2275772) baseStart_2275772 baseEnd_2275772 := by
    simpa [prefixWord, tailWord_2275772, baseEnd_2275772] using wordTrace_append hprefix tailTrace_2275772
  have hstable : (prefixWord ++ tailWord_2275772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275772).length < 2 ^ (prefixWord ++ tailWord_2275772).sum := by decide
  have hdescent : baseEnd_2275772 < baseStart_2275772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275785 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 7]
def baseStart_2275785 : Nat := 118140960795 + 2275785 * 2 ^ 59
def prefixEnd_2275785 : Nat := 4983230072969 + 3 ^ 40 * 2275785 * 2
def baseEnd_2275785 : Nat := 129841285699164857157929

theorem tailTrace_2275785 : CollatzResearch.WordTrace tailWord_2275785 prefixEnd_2275785 129841285699164857157929 := by
  unfold tailWord_2275785
  simp only [CollatzResearch.WordTrace]
  refine ⟨83004698060227092979260809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55336465373484728652840539 83004698060227092979260809)
  ·
    refine ⟨62253523545170319734445607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83004698060227092979260809 62253523545170319734445607)
    ·
      refine ⟨93380285317755479601668411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62253523545170319734445607 93380285317755479601668411)
      ·
        refine ⟨140070427976633219402502617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93380285317755479601668411 140070427976633219402502617)
        ·
          refine ⟨105052820982474914551876963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140070427976633219402502617 105052820982474914551876963)
          ·
            refine ⟨157579231473712371827815445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105052820982474914551876963 157579231473712371827815445)
            ·
              refine ⟨7386526475330267429428849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157579231473712371827815445 7386526475330267429428849)
              ·
                refine ⟨5539894856497700572071637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7386526475330267429428849 5539894856497700572071637)
                ·
                  refine ⟨129841285699164857157929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5539894856497700572071637 129841285699164857157929)
                  ·
                    rfl

theorem cell23_2275785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 7].length) (baseStart_2275785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275785 prefixEnd_2275785 := by exact prefixLift 2275785
  have htrace : WordTrace (prefixWord ++ tailWord_2275785) baseStart_2275785 baseEnd_2275785 := by
    simpa [prefixWord, tailWord_2275785, baseEnd_2275785] using wordTrace_append hprefix tailTrace_2275785
  have hstable : (prefixWord ++ tailWord_2275785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275785).length < 2 ^ (prefixWord ++ tailWord_2275785).sum := by decide
  have hdescent : baseEnd_2275785 < baseStart_2275785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275796 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_2275796 : Nat := 118140960795 + 2275796 * 2 ^ 59
def prefixEnd_2275796 : Nat := 4983230072969 + 3 ^ 40 * 2275796 * 2
def baseEnd_2275796 : Nat := 1168577219579683171383811

theorem tailTrace_2275796 : CollatzResearch.WordTrace tailWord_2275796 prefixEnd_2275796 1168577219579683171383811 := by
  unfold tailWord_2275796
  simp only [CollatzResearch.WordTrace]
  refine ⟨41502549631593620928955621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55336732842124827905274161 41502549631593620928955621)
  ·
    refine ⟨7781728055923803924179179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41502549631593620928955621 7781728055923803924179179)
    ·
      refine ⟨11672592083885705886268769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7781728055923803924179179 11672592083885705886268769)
      ·
        refine ⟨8754444062914279414701577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11672592083885705886268769 8754444062914279414701577)
        ·
          refine ⟨6565833047185709561026183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8754444062914279414701577 6565833047185709561026183)
          ·
            refine ⟨9848749570778564341539275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6565833047185709561026183 9848749570778564341539275)
            ·
              refine ⟨14773124356167846512308913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9848749570778564341539275 14773124356167846512308913)
              ·
                refine ⟨11079843267125884884231685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14773124356167846512308913 11079843267125884884231685)
                ·
                  refine ⟨2077470612586103415793441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11079843267125884884231685 2077470612586103415793441)
                  ·
                    refine ⟨1558102959439577561845081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2077470612586103415793441 1558102959439577561845081)
                    ·
                      refine ⟨1168577219579683171383811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558102959439577561845081 1168577219579683171383811)
                      ·
                        rfl

theorem cell23_2275796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_2275796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275796 prefixEnd_2275796 := by exact prefixLift 2275796
  have htrace : WordTrace (prefixWord ++ tailWord_2275796) baseStart_2275796 baseEnd_2275796 := by
    simpa [prefixWord, tailWord_2275796, baseEnd_2275796] using wordTrace_append hprefix tailTrace_2275796
  have hstable : (prefixWord ++ tailWord_2275796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275796).length < 2 ^ (prefixWord ++ tailWord_2275796).sum := by decide
  have hdescent : baseEnd_2275796 < baseStart_2275796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275819 : List Nat := [1, 1, 1, 1, 2, 3, 7, 2, 5]
def baseStart_2275819 : Nat := 118140960795 + 2275819 * 2 ^ 59
def prefixEnd_2275819 : Nat := 4983230072969 + 3 ^ 40 * 2275819 * 2
def baseEnd_2275819 : Nat := 129843225514970731266245

theorem tailTrace_2275819 : CollatzResearch.WordTrace tailWord_2275819 prefixEnd_2275819 129843225514970731266245 := by
  unfold tailWord_2275819
  simp only [CollatzResearch.WordTrace]
  refine ⟨83005938142103916785998511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55337292094735944523999007 83005938142103916785998511)
  ·
    refine ⟨124508907213155875178997767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83005938142103916785998511 124508907213155875178997767)
    ·
      refine ⟨186763360819733812768496651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124508907213155875178997767 186763360819733812768496651)
      ·
        refine ⟨280145041229600719152744977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186763360819733812768496651 280145041229600719152744977)
        ·
          refine ⟨210108780922200539364558733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280145041229600719152744977 210108780922200539364558733)
          ·
            refine ⟨78790792845825202261709525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210108780922200539364558733 78790792845825202261709525)
            ·
              refine ⟨1846659207324028178008817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 78790792845825202261709525 1846659207324028178008817)
              ·
                refine ⟨1384994405493021133506613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846659207324028178008817 1384994405493021133506613)
                ·
                  refine ⟨129843225514970731266245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1384994405493021133506613 129843225514970731266245)
                  ·
                    rfl

theorem cell23_2275819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 5].length) (baseStart_2275819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275819 prefixEnd_2275819 := by exact prefixLift 2275819
  have htrace : WordTrace (prefixWord ++ tailWord_2275819) baseStart_2275819 baseEnd_2275819 := by
    simpa [prefixWord, tailWord_2275819, baseEnd_2275819] using wordTrace_append hprefix tailTrace_2275819
  have hstable : (prefixWord ++ tailWord_2275819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275819).length < 2 ^ (prefixWord ++ tailWord_2275819).sum := by decide
  have hdescent : baseEnd_2275819 < baseStart_2275819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275845 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_2275845 : Nat := 118140960795 + 2275845 * 2 ^ 59
def prefixEnd_2275845 : Nat := 4983230072969 + 3 ^ 40 * 2275845 * 2
def baseEnd_2275845 : Nat := 389534126710584493223695

theorem tailTrace_2275845 : CollatzResearch.WordTrace tailWord_2275845 prefixEnd_2275845 389534126710584493223695 := by
  unfold tailWord_2275845
  simp only [CollatzResearch.WordTrace]
  refine ⟨83006886440009723226444989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55337924293339815484296659 83006886440009723226444989)
  ·
    refine ⟨31127582415003646209916871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83006886440009723226444989 31127582415003646209916871)
    ·
      refine ⟨46691373622505469314875307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31127582415003646209916871 46691373622505469314875307)
      ·
        refine ⟨70037060433758203972312961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46691373622505469314875307 70037060433758203972312961)
        ·
          refine ⟨52527795325318652979234721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70037060433758203972312961 52527795325318652979234721)
          ·
            refine ⟨39395846493988989734426041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52527795325318652979234721 39395846493988989734426041)
            ·
              refine ⟨29546884870491742300819531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39395846493988989734426041 29546884870491742300819531)
              ·
                refine ⟨44320327305737613451229297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29546884870491742300819531 44320327305737613451229297)
                ·
                  refine ⟨33240245479303210088421973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44320327305737613451229297 33240245479303210088421973)
                  ·
                    refine ⟨389534126710584493223695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33240245479303210088421973 389534126710584493223695)
                    ·
                      rfl

theorem cell23_2275845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_2275845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275845 prefixEnd_2275845 := by exact prefixLift 2275845
  have htrace : WordTrace (prefixWord ++ tailWord_2275845) baseStart_2275845 baseEnd_2275845 := by
    simpa [prefixWord, tailWord_2275845, baseEnd_2275845] using wordTrace_append hprefix tailTrace_2275845
  have hstable : (prefixWord ++ tailWord_2275845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275845).length < 2 ^ (prefixWord ++ tailWord_2275845).sum := by decide
  have hdescent : baseEnd_2275845 < baseStart_2275845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275855 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_2275855 : Nat := 118140960795 + 2275855 * 2 ^ 59
def prefixEnd_2275855 : Nat := 4983230072969 + 3 ^ 40 * 2275855 * 2
def baseEnd_2275855 : Nat := 1168607514938298440546039

theorem tailTrace_2275855 : CollatzResearch.WordTrace tailWord_2275855 prefixEnd_2275855 1168607514938298440546039 := by
  unfold tailWord_2275855
  simp only [CollatzResearch.WordTrace]
  refine ⟨83007251169973494934309019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55338167446648996622872679 83007251169973494934309019)
  ·
    refine ⟨124510876754960242401463529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83007251169973494934309019 124510876754960242401463529)
    ·
      refine ⟨93383157566220181801097647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124510876754960242401463529 93383157566220181801097647)
      ·
        refine ⟨140074736349330272701646471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93383157566220181801097647 140074736349330272701646471)
        ·
          refine ⟨210112104523995409052469707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140074736349330272701646471 210112104523995409052469707)
          ·
            refine ⟨315168156785993113578704561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210112104523995409052469707 315168156785993113578704561)
            ·
              refine ⟨236376117589494835184028421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315168156785993113578704561 236376117589494835184028421)
              ·
                refine ⟨44320522048030281597005329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236376117589494835184028421 44320522048030281597005329)
                ·
                  refine ⟨33240391536022711197753997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44320522048030281597005329 33240391536022711197753997)
                  ·
                    refine ⟨12465146826008516699157749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33240391536022711197753997 12465146826008516699157749)
                    ·
                      refine ⟨1168607514938298440546039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12465146826008516699157749 1168607514938298440546039)
                      ·
                        rfl

theorem cell23_2275855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_2275855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275855 prefixEnd_2275855 := by exact prefixLift 2275855
  have htrace : WordTrace (prefixWord ++ tailWord_2275855) baseStart_2275855 baseEnd_2275855 := by
    simpa [prefixWord, tailWord_2275855, baseEnd_2275855] using wordTrace_append hprefix tailTrace_2275855
  have hstable : (prefixWord ++ tailWord_2275855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275855).length < 2 ^ (prefixWord ++ tailWord_2275855).sum := by decide
  have hdescent : baseEnd_2275855 < baseStart_2275855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275865 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_2275865 : Nat := 118140960795 + 2275865 * 2 ^ 59
def prefixEnd_2275865 : Nat := 4983230072969 + 3 ^ 40 * 2275865 * 2
def baseEnd_2275865 : Nat := 1168612649744843401420993

theorem tailTrace_2275865 : CollatzResearch.WordTrace tailWord_2275865 prefixEnd_2275865 1168612649744843401420993 := by
  unfold tailWord_2275865
  simp only [CollatzResearch.WordTrace]
  refine ⟨83007615899937266642173049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55338410599958177761448699 83007615899937266642173049)
  ·
    refine ⟨62255711924952949981629787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83007615899937266642173049 62255711924952949981629787)
    ·
      refine ⟨93383567887429424972444681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62255711924952949981629787 93383567887429424972444681)
      ·
        refine ⟨70037675915572068729333511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93383567887429424972444681 70037675915572068729333511)
        ·
          refine ⟨105056513873358103094000267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70037675915572068729333511 105056513873358103094000267)
          ·
            refine ⟨157584770810037154641000401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105056513873358103094000267 157584770810037154641000401)
            ·
              refine ⟨118188578107527865980750301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157584770810037154641000401 118188578107527865980750301)
              ·
                refine ⟨44320716790322949742781363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118188578107527865980750301 44320716790322949742781363)
                ·
                  refine ⟨66481075185484424614172045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44320716790322949742781363 66481075185484424614172045)
                  ·
                    refine ⟨24930403194556659230314517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66481075185484424614172045 24930403194556659230314517)
                    ·
                      refine ⟨1168612649744843401420993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24930403194556659230314517 1168612649744843401420993)
                      ·
                        rfl

theorem cell23_2275865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_2275865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275865 prefixEnd_2275865 := by exact prefixLift 2275865
  have htrace : WordTrace (prefixWord ++ tailWord_2275865) baseStart_2275865 baseEnd_2275865 := by
    simpa [prefixWord, tailWord_2275865, baseEnd_2275865] using wordTrace_append hprefix tailTrace_2275865
  have hstable : (prefixWord ++ tailWord_2275865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275865).length < 2 ^ (prefixWord ++ tailWord_2275865).sum := by decide
  have hdescent : baseEnd_2275865 < baseStart_2275865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275869 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2275869 : Nat := 118140960795 + 2275869 * 2 ^ 59
def prefixEnd_2275869 : Nat := 4983230072969 + 3 ^ 40 * 2275869 * 2
def baseEnd_2275869 : Nat := 1168614703667461385770975

theorem tailTrace_2275869 : CollatzResearch.WordTrace tailWord_2275869 prefixEnd_2275869 1168614703667461385770975 := by
  unfold tailWord_2275869
  simp only [CollatzResearch.WordTrace]
  refine ⟨83007761791922775325318661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55338507861281850216879107 83007761791922775325318661)
  ·
    refine ⟨15563955335985520373497249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83007761791922775325318661 15563955335985520373497249)
    ·
      refine ⟨11672966501989140280122937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15563955335985520373497249 11672966501989140280122937)
      ·
        refine ⟨8754724876491855210092203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11672966501989140280122937 8754724876491855210092203)
        ·
          refine ⟨13132087314737782815138305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8754724876491855210092203 13132087314737782815138305)
          ·
            refine ⟨9849065486053337111353729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13132087314737782815138305 9849065486053337111353729)
            ·
              refine ⟨7386799114540002833515297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9849065486053337111353729 7386799114540002833515297)
              ·
                refine ⟨5540099335905002125136473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7386799114540002833515297 5540099335905002125136473)
                ·
                  refine ⟨4155074501928751593852355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5540099335905002125136473 4155074501928751593852355)
                  ·
                    refine ⟨6232611752893127390778533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4155074501928751593852355 6232611752893127390778533)
                    ·
                      refine ⟨1168614703667461385770975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6232611752893127390778533 1168614703667461385770975)
                      ·
                        rfl

theorem cell23_2275869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2275869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275869 prefixEnd_2275869 := by exact prefixLift 2275869
  have htrace : WordTrace (prefixWord ++ tailWord_2275869) baseStart_2275869 baseEnd_2275869 := by
    simpa [prefixWord, tailWord_2275869, baseEnd_2275869] using wordTrace_append hprefix tailTrace_2275869
  have hstable : (prefixWord ++ tailWord_2275869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275869).length < 2 ^ (prefixWord ++ tailWord_2275869).sum := by decide
  have hdescent : baseEnd_2275869 < baseStart_2275869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275959 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 4]
def baseStart_2275959 : Nat := 118140960795 + 2275959 * 2 ^ 59
def prefixEnd_2275959 : Nat := 4983230072969 + 3 ^ 40 * 2275959 * 2
def baseEnd_2275959 : Nat := 1168660916926366033645561

theorem tailTrace_2275959 : CollatzResearch.WordTrace tailWord_2275959 prefixEnd_2275959 1168660916926366033645561 := by
  unfold tailWord_2275959
  simp only [CollatzResearch.WordTrace]
  refine ⟨83011044361596720696094931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55340696241064480464063287 83011044361596720696094931)
  ·
    refine ⟨124516566542395081044142397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83011044361596720696094931 124516566542395081044142397)
    ·
      refine ⟨46693712453398155391553399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124516566542395081044142397 46693712453398155391553399)
      ·
        refine ⟨70040568680097233087330099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46693712453398155391553399 70040568680097233087330099)
        ·
          refine ⟨105060853020145849630995149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70040568680097233087330099 105060853020145849630995149)
          ·
            refine ⟨39397819882554693611623181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105060853020145849630995149 39397819882554693611623181)
            ·
              refine ⟨14774182455958010104358693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39397819882554693611623181 14774182455958010104358693)
              ·
                refine ⟨2770159210492126894567255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14774182455958010104358693 2770159210492126894567255)
                ·
                  refine ⟨4155238815738190341850883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770159210492126894567255 4155238815738190341850883)
                  ·
                    refine ⟨6232858223607285512776325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4155238815738190341850883 6232858223607285512776325)
                    ·
                      refine ⟨1168660916926366033645561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6232858223607285512776325 1168660916926366033645561)
                      ·
                        rfl

theorem cell23_2275959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_2275959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275959 prefixEnd_2275959 := by exact prefixLift 2275959
  have htrace : WordTrace (prefixWord ++ tailWord_2275959) baseStart_2275959 baseEnd_2275959 := by
    simpa [prefixWord, tailWord_2275959, baseEnd_2275959] using wordTrace_append hprefix tailTrace_2275959
  have hstable : (prefixWord ++ tailWord_2275959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275959).length < 2 ^ (prefixWord ++ tailWord_2275959).sum := by decide
  have hdescent : baseEnd_2275959 < baseStart_2275959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275969 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2275969 : Nat := 118140960795 + 2275969 * 2 ^ 59
def prefixEnd_2275969 : Nat := 4983230072969 + 3 ^ 40 * 2275969 * 2
def baseEnd_2275969 : Nat := 389555350577636998173505

theorem tailTrace_2275969 : CollatzResearch.WordTrace tailWord_2275969 prefixEnd_2275969 389555350577636998173505 := by
  unfold tailWord_2275969
  simp only [CollatzResearch.WordTrace]
  refine ⟨83011409091560492403958961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55340939394373661602639307 83011409091560492403958961)
  ·
    refine ⟨62258556818670369302969221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83011409091560492403958961 62258556818670369302969221)
    ·
      refine ⟨11673479403500694244306729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62258556818670369302969221 11673479403500694244306729)
      ·
        refine ⟨8755109552625520683230047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11673479403500694244306729 8755109552625520683230047)
        ·
          refine ⟨13132664328938281024845071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8755109552625520683230047 13132664328938281024845071)
          ·
            refine ⟨19698996493407421537267607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13132664328938281024845071 19698996493407421537267607)
            ·
              refine ⟨29548494740111132305901411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19698996493407421537267607 29548494740111132305901411)
              ·
                refine ⟨44322742110166698458852117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29548494740111132305901411 44322742110166698458852117)
                ·
                  refine ⟨2077628536414063990258693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44322742110166698458852117 2077628536414063990258693)
                  ·
                    refine ⟨389555350577636998173505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2077628536414063990258693 389555350577636998173505)
                    ·
                      rfl

theorem cell23_2275969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2275969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275969 prefixEnd_2275969 := by exact prefixLift 2275969
  have htrace : WordTrace (prefixWord ++ tailWord_2275969) baseStart_2275969 baseEnd_2275969 := by
    simpa [prefixWord, tailWord_2275969, baseEnd_2275969] using wordTrace_append hprefix tailTrace_2275969
  have hstable : (prefixWord ++ tailWord_2275969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275969).length < 2 ^ (prefixWord ++ tailWord_2275969).sum := by decide
  have hdescent : baseEnd_2275969 < baseStart_2275969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2275986 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2275986 : Nat := 118140960795 + 2275986 * 2 ^ 59
def prefixEnd_2275986 : Nat := 4983230072969 + 3 ^ 40 * 2275986 * 2
def baseEnd_2275986 : Nat := 389558260301345809335979

theorem tailTrace_2275986 : CollatzResearch.WordTrace tailWord_2275986 prefixEnd_2275986 389558260301345809335979 := by
  unfold tailWord_2275986
  simp only [CollatzResearch.WordTrace]
  refine ⟨20753007283124726076831953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55341352754999269538218541 20753007283124726076831953)
  ·
    refine ⟨15564755462343544557623965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20753007283124726076831953 15564755462343544557623965)
    ·
      refine ⟨5836783298378829209108987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15564755462343544557623965 5836783298378829209108987)
      ·
        refine ⟨8755174947568243813663481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5836783298378829209108987 8755174947568243813663481)
        ·
          refine ⟨6566381210676182860247611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8755174947568243813663481 6566381210676182860247611)
          ·
            refine ⟨9849571816014274290371417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6566381210676182860247611 9849571816014274290371417)
            ·
              refine ⟨7387178862010705717778563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9849571816014274290371417 7387178862010705717778563)
              ·
                refine ⟨11080768293016058576667845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7387178862010705717778563 11080768293016058576667845)
                ·
                  refine ⟨2077644054940510983125221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11080768293016058576667845 2077644054940510983125221)
                  ·
                    refine ⟨389558260301345809335979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2077644054940510983125221 389558260301345809335979)
                    ·
                      rfl

theorem cell23_2275986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2275986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2275986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2275986 prefixEnd_2275986 := by exact prefixLift 2275986
  have htrace : WordTrace (prefixWord ++ tailWord_2275986) baseStart_2275986 baseEnd_2275986 := by
    simpa [prefixWord, tailWord_2275986, baseEnd_2275986] using wordTrace_append hprefix tailTrace_2275986
  have hstable : (prefixWord ++ tailWord_2275986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2275986).length < 2 ^ (prefixWord ++ tailWord_2275986).sum := by decide
  have hdescent : baseEnd_2275986 < baseStart_2275986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2275986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276013 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_2276013 : Nat := 118140960795 + 2276013 * 2 ^ 59
def prefixEnd_2276013 : Nat := 4983230072969 + 3 ^ 40 * 2276013 * 2
def baseEnd_2276013 : Nat := 1168688644881708822370313

theorem tailTrace_2276013 : CollatzResearch.WordTrace tailWord_2276013 prefixEnd_2276013 1168688644881708822370313 := by
  unfold tailWord_2276013
  simp only [CollatzResearch.WordTrace]
  refine ⟨83013013903401087918560693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55342009268934058612373795 83013013903401087918560693)
  ·
    refine ⟨7782470053443851992365065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83013013903401087918560693 7782470053443851992365065)
    ·
      refine ⟨5836852540082888994273799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7782470053443851992365065 5836852540082888994273799)
      ·
        refine ⟨8755278810124333491410699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5836852540082888994273799 8755278810124333491410699)
        ·
          refine ⟨13132918215186500237116049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8755278810124333491410699 13132918215186500237116049)
          ·
            refine ⟨9849688661389875177837037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13132918215186500237116049 9849688661389875177837037)
            ·
              refine ⟨3693633248021203191688889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9849688661389875177837037 3693633248021203191688889)
              ·
                refine ⟨2770224936015902393766667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3693633248021203191688889 2770224936015902393766667)
                ·
                  refine ⟨4155337404023853590650001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770224936015902393766667 4155337404023853590650001)
                  ·
                    refine ⟨3116503053017890192987501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4155337404023853590650001 3116503053017890192987501)
                    ·
                      refine ⟨1168688644881708822370313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3116503053017890192987501 1168688644881708822370313)
                      ·
                        rfl

theorem cell23_2276013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_2276013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276013 prefixEnd_2276013 := by exact prefixLift 2276013
  have htrace : WordTrace (prefixWord ++ tailWord_2276013) baseStart_2276013 baseEnd_2276013 := by
    simpa [prefixWord, tailWord_2276013, baseEnd_2276013] using wordTrace_append hprefix tailTrace_2276013
  have hstable : (prefixWord ++ tailWord_2276013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276013).length < 2 ^ (prefixWord ++ tailWord_2276013).sum := by decide
  have hdescent : baseEnd_2276013 < baseStart_2276013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276038 : List Nat := [6, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_2276038 : Nat := 118140960795 + 2276038 * 2 ^ 59
def prefixEnd_2276038 : Nat := 4983230072969 + 3 ^ 40 * 2276038 * 2
def baseEnd_2276038 : Nat := 1168701481898071224557699

theorem tailTrace_2276038 : CollatzResearch.WordTrace tailWord_2276038 prefixEnd_2276038 1168701481898071224557699 := by
  unfold tailWord_2276038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2594185179009703662131899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55342617152207011458813845 2594185179009703662131899)
  ·
    refine ⟨3891277768514555493197849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2594185179009703662131899 3891277768514555493197849)
    ·
      refine ⟨2918458326385916619898387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3891277768514555493197849 2918458326385916619898387)
      ·
        refine ⟨4377687489578874929847581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2918458326385916619898387 4377687489578874929847581)
        ·
          refine ⟨1641632808592078098692843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4377687489578874929847581 1641632808592078098692843)
          ·
            refine ⟨2462449212888117148039265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641632808592078098692843 2462449212888117148039265)
            ·
              refine ⟨1846836909666087861029449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462449212888117148039265 1846836909666087861029449)
              ·
                refine ⟨1385127682249565895772087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846836909666087861029449 1385127682249565895772087)
                ·
                  refine ⟨2077691523374348843658131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385127682249565895772087 2077691523374348843658131)
                  ·
                    refine ⟨3116537285061523265487197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2077691523374348843658131 3116537285061523265487197)
                    ·
                      refine ⟨1168701481898071224557699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3116537285061523265487197 1168701481898071224557699)
                      ·
                        rfl

theorem cell23_2276038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_2276038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276038 prefixEnd_2276038 := by exact prefixLift 2276038
  have htrace : WordTrace (prefixWord ++ tailWord_2276038) baseStart_2276038 baseEnd_2276038 := by
    simpa [prefixWord, tailWord_2276038, baseEnd_2276038] using wordTrace_append hprefix tailTrace_2276038
  have hstable : (prefixWord ++ tailWord_2276038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276038).length < 2 ^ (prefixWord ++ tailWord_2276038).sum := by decide
  have hdescent : baseEnd_2276038 < baseStart_2276038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
