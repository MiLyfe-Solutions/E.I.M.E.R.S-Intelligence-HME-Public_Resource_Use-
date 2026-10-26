import V185TrunkScan23Chunk0559

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3310648 : List Nat := [2, 1, 2, 1, 5, 3, 2, 7]
def baseStart_3310648 : Nat := 118140960795 + 3310648 * 2 ^ 59
def prefixEnd_3310648 : Nat := 4983230072969 + 3 ^ 40 * 3310648 * 2
def baseEnd_3310648 : Nat := 62961248216528455858319

theorem tailTrace_3310648 : CollatzResearch.WordTrace tailWord_3310648 prefixEnd_3310648 62961248216528455858319 := by
  unfold tailWord_3310648
  simp only [CollatzResearch.WordTrace]
  refine ⟨60374626255047592254314299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80499501673396789672419065 60374626255047592254314299)
  ·
    refine ⟨90561939382571388381471449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60374626255047592254314299 90561939382571388381471449)
    ·
      refine ⟨67921454536928541286103587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90561939382571388381471449 67921454536928541286103587)
      ·
        refine ⟨101882181805392811929155381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67921454536928541286103587 101882181805392811929155381)
        ·
          refine ⟨9551454544255576118358317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101882181805392811929155381 9551454544255576118358317)
          ·
            refine ⟨3581795454095841044384369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9551454544255576118358317 3581795454095841044384369)
            ·
              refine ⟨2686346590571880783288277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3581795454095841044384369 2686346590571880783288277)
              ·
                refine ⟨62961248216528455858319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2686346590571880783288277 62961248216528455858319)
                ·
                  rfl

theorem cell23_3310648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 7].length) (baseStart_3310648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310648 prefixEnd_3310648 := by exact prefixLift 3310648
  have htrace : WordTrace (prefixWord ++ tailWord_3310648) baseStart_3310648 baseEnd_3310648 := by
    simpa [prefixWord, tailWord_3310648, baseEnd_3310648] using wordTrace_append hprefix tailTrace_3310648
  have hstable : (prefixWord ++ tailWord_3310648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310648).length < 2 ^ (prefixWord ++ tailWord_3310648).sum := by decide
  have hdescent : baseEnd_3310648 < baseStart_3310648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310662 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3310662 : Nat := 118140960795 + 3310662 * 2 ^ 59
def prefixEnd_3310662 : Nat := 4983230072969 + 3 ^ 40 * 3310662 * 2
def baseEnd_3310662 : Nat := 1699960890575431253399549

theorem tailTrace_3310662 : CollatzResearch.WordTrace tailWord_3310662 prefixEnd_3310662 1699960890575431253399549 := by
  unfold tailWord_3310662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3773430097876389528113695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80499842088029643266425493 3773430097876389528113695)
  ·
    refine ⟨5660145146814584292170543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3773430097876389528113695 5660145146814584292170543)
    ·
      refine ⟨8490217720221876438255815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5660145146814584292170543 8490217720221876438255815)
      ·
        refine ⟨12735326580332814657383723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8490217720221876438255815 12735326580332814657383723)
        ·
          refine ⟨19102989870499221986075585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12735326580332814657383723 19102989870499221986075585)
          ·
            refine ⟨14327242402874416489556689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19102989870499221986075585 14327242402874416489556689)
            ·
              refine ⟨10745431802155812367167517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14327242402874416489556689 10745431802155812367167517)
              ·
                refine ⟨4029536925808429637687819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10745431802155812367167517 4029536925808429637687819)
                ·
                  refine ⟨6044305388712644456531729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4029536925808429637687819 6044305388712644456531729)
                  ·
                    refine ⟨4533229041534483342398797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6044305388712644456531729 4533229041534483342398797)
                    ·
                      refine ⟨1699960890575431253399549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4533229041534483342398797 1699960890575431253399549)
                      ·
                        rfl

theorem cell23_3310662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3310662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310662 prefixEnd_3310662 := by exact prefixLift 3310662
  have htrace : WordTrace (prefixWord ++ tailWord_3310662) baseStart_3310662 baseEnd_3310662 := by
    simpa [prefixWord, tailWord_3310662, baseEnd_3310662] using wordTrace_append hprefix tailTrace_3310662
  have hstable : (prefixWord ++ tailWord_3310662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310662).length < 2 ^ (prefixWord ++ tailWord_3310662).sum := by decide
  have hdescent : baseEnd_3310662 < baseStart_3310662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310668 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 5, 3, 2]
def baseStart_3310668 : Nat := 118140960795 + 3310668 * 2 ^ 59
def prefixEnd_3310668 : Nat := 4983230072969 + 3 ^ 40 * 3310668 * 2
def baseEnd_3310668 : Nat := 1699963971459358229924521

theorem tailTrace_3310668 : CollatzResearch.WordTrace tailWord_3310668 prefixEnd_3310668 1699963971459358229924521 := by
  unfold tailWord_3310668
  simp only [CollatzResearch.WordTrace]
  refine ⟨60374990985011363962178329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80499987980015151949571105 60374990985011363962178329)
  ·
    refine ⟨45281243238758522971633747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60374990985011363962178329 45281243238758522971633747)
    ·
      refine ⟨67921864858137784457450621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45281243238758522971633747 67921864858137784457450621)
      ·
        refine ⟨25470699321801669171543983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67921864858137784457450621 25470699321801669171543983)
        ·
          refine ⟨38206048982702503757315975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25470699321801669171543983 38206048982702503757315975)
          ·
            refine ⟨57309073474053755635973963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38206048982702503757315975 57309073474053755635973963)
            ·
              refine ⟨85963610211080633453960945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57309073474053755635973963 85963610211080633453960945)
              ·
                refine ⟨64472707658310475090470709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85963610211080633453960945 64472707658310475090470709)
                ·
                  refine ⟨6044316342966607039731629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64472707658310475090470709 6044316342966607039731629)
                  ·
                    refine ⟨2266618628612477639899361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6044316342966607039731629 2266618628612477639899361)
                    ·
                      refine ⟨1699963971459358229924521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266618628612477639899361 1699963971459358229924521)
                      ·
                        rfl

theorem cell23_3310668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_3310668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310668 prefixEnd_3310668 := by exact prefixLift 3310668
  have htrace : WordTrace (prefixWord ++ tailWord_3310668) baseStart_3310668 baseEnd_3310668 := by
    simpa [prefixWord, tailWord_3310668, baseEnd_3310668] using wordTrace_append hprefix tailTrace_3310668
  have hstable : (prefixWord ++ tailWord_3310668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310668).length < 2 ^ (prefixWord ++ tailWord_3310668).sum := by decide
  have hdescent : baseEnd_3310668 < baseStart_3310668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310686 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_3310686 : Nat := 118140960795 + 3310686 * 2 ^ 59
def prefixEnd_3310686 : Nat := 4983230072969 + 3 ^ 40 * 3310686 * 2
def baseEnd_3310686 : Nat := 566657738037046386499813

theorem tailTrace_3310686 : CollatzResearch.WordTrace tailWord_3310686 prefixEnd_3310686 566657738037046386499813 := by
  unfold tailWord_3310686
  simp only [CollatzResearch.WordTrace]
  refine ⟨15093829810494689624813989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80500425655971677999007941 15093829810494689624813989)
  ·
    refine ⟨2830093089467754304652623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15093829810494689624813989 2830093089467754304652623)
    ·
      refine ⟨4245139634201631456978935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2830093089467754304652623 4245139634201631456978935)
      ·
        refine ⟨6367709451302447185468403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4245139634201631456978935 6367709451302447185468403)
        ·
          refine ⟨9551564176953670778202605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6367709451302447185468403 9551564176953670778202605)
          ·
            refine ⟨3581836566357626541825977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9551564176953670778202605 3581836566357626541825977)
            ·
              refine ⟨2686377424768219906369483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3581836566357626541825977 2686377424768219906369483)
              ·
                refine ⟨4029566137152329859554225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2686377424768219906369483 4029566137152329859554225)
                ·
                  refine ⟨3022174602864247394665669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4029566137152329859554225 3022174602864247394665669)
                  ·
                    refine ⟨566657738037046386499813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3022174602864247394665669 566657738037046386499813)
                    ·
                      rfl

theorem cell23_3310686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_3310686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310686 prefixEnd_3310686 := by exact prefixLift 3310686
  have htrace : WordTrace (prefixWord ++ tailWord_3310686) baseStart_3310686 baseEnd_3310686 := by
    simpa [prefixWord, tailWord_3310686, baseEnd_3310686] using wordTrace_append hprefix tailTrace_3310686
  have hstable : (prefixWord ++ tailWord_3310686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310686).length < 2 ^ (prefixWord ++ tailWord_3310686).sum := by decide
  have hdescent : baseEnd_3310686 < baseStart_3310686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310702 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_3310702 : Nat := 118140960795 + 3310702 * 2 ^ 59
def prefixEnd_3310702 : Nat := 4983230072969 + 3 ^ 40 * 3310702 * 2
def baseEnd_3310702 : Nat := 1699981429801611096899365

theorem tailTrace_3310702 : CollatzResearch.WordTrace tailWord_3310702 prefixEnd_3310702 1699981429801611096899365 := by
  unfold tailWord_3310702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15093902756487443966386795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80500814701266367820729573 15093902756487443966386795)
  ·
    refine ⟨22640854134731165949580193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15093902756487443966386795 22640854134731165949580193)
    ·
      refine ⟨16980640601048374462185145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22640854134731165949580193 16980640601048374462185145)
      ·
        refine ⟨12735480450786280846638859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16980640601048374462185145 12735480450786280846638859)
        ·
          refine ⟨19103220676179421269958289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12735480450786280846638859 19103220676179421269958289)
          ·
            refine ⟨14327415507134565952468717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19103220676179421269958289 14327415507134565952468717)
            ·
              refine ⟨5372780815175462232175769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14327415507134565952468717 5372780815175462232175769)
              ·
                refine ⟨4029585611381596674131827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5372780815175462232175769 4029585611381596674131827)
                ·
                  refine ⟨6044378417072395011197741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4029585611381596674131827 6044378417072395011197741)
                  ·
                    refine ⟨2266641906402148129199153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6044378417072395011197741 2266641906402148129199153)
                    ·
                      refine ⟨1699981429801611096899365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266641906402148129199153 1699981429801611096899365)
                      ·
                        rfl

theorem cell23_3310702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_3310702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310702 prefixEnd_3310702 := by exact prefixLift 3310702
  have htrace : WordTrace (prefixWord ++ tailWord_3310702) baseStart_3310702 baseEnd_3310702 := by
    simpa [prefixWord, tailWord_3310702, baseEnd_3310702] using wordTrace_append hprefix tailTrace_3310702
  have hstable : (prefixWord ++ tailWord_3310702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310702).length < 2 ^ (prefixWord ++ tailWord_3310702).sum := by decide
  have hdescent : baseEnd_3310702 < baseStart_3310702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310731 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 3]
def baseStart_3310731 : Nat := 118140960795 + 3310731 * 2 ^ 59
def prefixEnd_3310731 : Nat := 4983230072969 + 3 ^ 40 * 3310731 * 2
def baseEnd_3310731 : Nat := 1699996320740591483436731

theorem tailTrace_3310731 : CollatzResearch.WordTrace tailWord_3310731 prefixEnd_3310731 1699996320740591483436731 := by
  unfold tailWord_3310731
  simp only [CollatzResearch.WordTrace]
  refine ⟨120752279768794489683900047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80501519845862993122600031 120752279768794489683900047)
  ·
    refine ⟨181128419653191734525850071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120752279768794489683900047 181128419653191734525850071)
    ·
      refine ⟨271692629479787601788775107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181128419653191734525850071 271692629479787601788775107)
      ·
        refine ⟨407538944219681402683162661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271692629479787601788775107 407538944219681402683162661)
        ·
          refine ⟨76413552041190263003092999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407538944219681402683162661 76413552041190263003092999)
          ·
            refine ⟨114620328061785394504639499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76413552041190263003092999 114620328061785394504639499)
            ·
              refine ⟨171930492092678091756959249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114620328061785394504639499 171930492092678091756959249)
              ·
                refine ⟨128947869069508568817719437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171930492092678091756959249 128947869069508568817719437)
                ·
                  refine ⟨48355450901065713306644789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128947869069508568817719437 48355450901065713306644789)
                  ·
                    refine ⟨4533323521974910622497949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48355450901065713306644789 4533323521974910622497949)
                    ·
                      refine ⟨1699996320740591483436731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4533323521974910622497949 1699996320740591483436731)
                      ·
                        rfl

theorem cell23_3310731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 3].length) (baseStart_3310731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310731 prefixEnd_3310731 := by exact prefixLift 3310731
  have htrace : WordTrace (prefixWord ++ tailWord_3310731) baseStart_3310731 baseEnd_3310731 := by
    simpa [prefixWord, tailWord_3310731, baseEnd_3310731] using wordTrace_append hprefix tailTrace_3310731
  have hstable : (prefixWord ++ tailWord_3310731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310731).length < 2 ^ (prefixWord ++ tailWord_3310731).sum := by decide
  have hdescent : baseEnd_3310731 < baseStart_3310731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310748 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_3310748 : Nat := 118140960795 + 3310748 * 2 ^ 59
def prefixEnd_3310748 : Nat := 4983230072969 + 3 ^ 40 * 3310748 * 2
def baseEnd_3310748 : Nat := 1700005049911717916924153

theorem tailTrace_3310748 : CollatzResearch.WordTrace tailWord_3310748 prefixEnd_3310748 1700005049911717916924153 := by
  unfold tailWord_3310748
  simp only [CollatzResearch.WordTrace]
  refine ⟨60376449904866450793634449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80501933206488601058179265 60376449904866450793634449)
  ·
    refine ⟨45282337428649838095225837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60376449904866450793634449 45282337428649838095225837)
    ·
      refine ⟨16980876535743689285709689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45282337428649838095225837 16980876535743689285709689)
      ·
        refine ⟨12735657401807766964282267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16980876535743689285709689 12735657401807766964282267)
        ·
          refine ⟨19103486102711650446423401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12735657401807766964282267 19103486102711650446423401)
          ·
            refine ⟨14327614577033737834817551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19103486102711650446423401 14327614577033737834817551)
            ·
              refine ⟨21491421865550606752226327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14327614577033737834817551 21491421865550606752226327)
              ·
                refine ⟨32237132798325910128339491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21491421865550606752226327 32237132798325910128339491)
                ·
                  refine ⟨48355699197488865192509237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32237132798325910128339491 48355699197488865192509237)
                  ·
                    refine ⟨4533346799764581111797741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48355699197488865192509237 4533346799764581111797741)
                    ·
                      refine ⟨1700005049911717916924153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4533346799764581111797741 1700005049911717916924153)
                      ·
                        rfl

theorem cell23_3310748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_3310748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310748 prefixEnd_3310748 := by exact prefixLift 3310748
  have htrace : WordTrace (prefixWord ++ tailWord_3310748) baseStart_3310748 baseEnd_3310748 := by
    simpa [prefixWord, tailWord_3310748, baseEnd_3310748] using wordTrace_append hprefix tailTrace_3310748
  have hstable : (prefixWord ++ tailWord_3310748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310748).length < 2 ^ (prefixWord ++ tailWord_3310748).sum := by decide
  have hdescent : baseEnd_3310748 < baseStart_3310748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310791 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_3310791 : Nat := 118140960795 + 3310791 * 2 ^ 59
def prefixEnd_3310791 : Nat := 4983230072969 + 3 ^ 40 * 3310791 * 2
def baseEnd_3310791 : Nat := 1700027129579861248686455

theorem tailTrace_3310791 : CollatzResearch.WordTrace tailWord_3310791 prefixEnd_3310791 1700027129579861248686455 := by
  unfold tailWord_3310791
  simp only [CollatzResearch.WordTrace]
  refine ⟨120754468148577119931084227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80502978765718079954056151 120754468148577119931084227)
  ·
    refine ⟨181131702222865679896626341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120754468148577119931084227 181131702222865679896626341)
    ·
      refine ⟨33962194166787314980617439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181131702222865679896626341 33962194166787314980617439)
      ·
        refine ⟨50943291250180972470926159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33962194166787314980617439 50943291250180972470926159)
        ·
          refine ⟨76414936875271458706389239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50943291250180972470926159 76414936875271458706389239)
          ·
            refine ⟨114622405312907188059583859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76414936875271458706389239 114622405312907188059583859)
            ·
              refine ⟨171933607969360782089375789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114622405312907188059583859 171933607969360782089375789)
              ·
                refine ⟨64475102988510293283515921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171933607969360782089375789 64475102988510293283515921)
                ·
                  refine ⟨48356327241382719962636941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64475102988510293283515921 48356327241382719962636941)
                  ·
                    refine ⟨18133622715518519985988853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48356327241382719962636941 18133622715518519985988853)
                    ·
                      refine ⟨1700027129579861248686455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18133622715518519985988853 1700027129579861248686455)
                      ·
                        rfl

theorem cell23_3310791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_3310791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310791 prefixEnd_3310791 := by exact prefixLift 3310791
  have htrace : WordTrace (prefixWord ++ tailWord_3310791) baseStart_3310791 baseEnd_3310791 := by
    simpa [prefixWord, tailWord_3310791, baseEnd_3310791] using wordTrace_append hprefix tailTrace_3310791
  have hstable : (prefixWord ++ tailWord_3310791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310791).length < 2 ^ (prefixWord ++ tailWord_3310791).sum := by decide
  have hdescent : baseEnd_3310791 < baseStart_3310791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310801 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_3310801 : Nat := 118140960795 + 3310801 * 2 ^ 59
def prefixEnd_3310801 : Nat := 4983230072969 + 3 ^ 40 * 3310801 * 2
def baseEnd_3310801 : Nat := 1700032264386406209561409

theorem tailTrace_3310801 : CollatzResearch.WordTrace tailWord_3310801 prefixEnd_3310801 1700032264386406209561409 := by
  unfold tailWord_3310801
  simp only [CollatzResearch.WordTrace]
  refine ⟨120754832878540891638948257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80503221919027261092632171 120754832878540891638948257)
  ·
    refine ⟨90566124658905668729211193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120754832878540891638948257 90566124658905668729211193)
    ·
      refine ⟨67924593494179251546908395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90566124658905668729211193 67924593494179251546908395)
      ·
        refine ⟨101886890241268877320362593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67924593494179251546908395 101886890241268877320362593)
        ·
          refine ⟨76415167680951657990271945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101886890241268877320362593 76415167680951657990271945)
          ·
            refine ⟨57311375760713743492703959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76415167680951657990271945 57311375760713743492703959)
            ·
              refine ⟨85967063641070615239055939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57311375760713743492703959 85967063641070615239055939)
              ·
                refine ⟨128950595461605922858583909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85967063641070615239055939 128950595461605922858583909)
                ·
                  refine ⟨24178236649051110535984483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128950595461605922858583909 24178236649051110535984483)
                  ·
                    refine ⟨36267354973576665803976725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24178236649051110535984483 36267354973576665803976725)
                    ·
                      refine ⟨1700032264386406209561409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36267354973576665803976725 1700032264386406209561409)
                      ·
                        rfl

theorem cell23_3310801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_3310801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310801 prefixEnd_3310801 := by exact prefixLift 3310801
  have htrace : WordTrace (prefixWord ++ tailWord_3310801) baseStart_3310801 baseEnd_3310801 := by
    simpa [prefixWord, tailWord_3310801, baseEnd_3310801] using wordTrace_append hprefix tailTrace_3310801
  have hstable : (prefixWord ++ tailWord_3310801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310801).length < 2 ^ (prefixWord ++ tailWord_3310801).sum := by decide
  have hdescent : baseEnd_3310801 < baseStart_3310801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310849 : List Nat := [1, 2, 4, 1, 1, 4, 3, 2, 1, 4]
def baseStart_3310849 : Nat := 118140960795 + 3310849 * 2 ^ 59
def prefixEnd_3310849 : Nat := 4983230072969 + 3 ^ 40 * 3310849 * 2
def baseEnd_3310849 : Nat := 566685637152607340587063

theorem tailTrace_3310849 : CollatzResearch.WordTrace tailWord_3310849 prefixEnd_3310849 566685637152607340587063 := by
  unfold tailWord_3310849
  simp only [CollatzResearch.WordTrace]
  refine ⟨120756583582366995836695601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80504389054911330557797067 120756583582366995836695601)
  ·
    refine ⟨90567437686775246877521701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120756583582366995836695601 90567437686775246877521701)
    ·
      refine ⟨16981394566270358789535319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90567437686775246877521701 16981394566270358789535319)
      ·
        refine ⟨25472091849405538184302979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16981394566270358789535319 25472091849405538184302979)
        ·
          refine ⟨38208137774108307276454469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25472091849405538184302979 38208137774108307276454469)
          ·
            refine ⟨7164025832645307614335213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38208137774108307276454469 7164025832645307614335213)
            ·
              refine ⟨2686509687241990355375705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7164025832645307614335213 2686509687241990355375705)
              ·
                refine ⟨2014882265431492766531779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2686509687241990355375705 2014882265431492766531779)
                ·
                  refine ⟨3022323398147239149797669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014882265431492766531779 3022323398147239149797669)
                  ·
                    refine ⟨566685637152607340587063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3022323398147239149797669 566685637152607340587063)
                    ·
                      rfl

theorem cell23_3310849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_3310849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310849 prefixEnd_3310849 := by exact prefixLift 3310849
  have htrace : WordTrace (prefixWord ++ tailWord_3310849) baseStart_3310849 baseEnd_3310849 := by
    simpa [prefixWord, tailWord_3310849, baseEnd_3310849] using wordTrace_append hprefix tailTrace_3310849
  have hstable : (prefixWord ++ tailWord_3310849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310849).length < 2 ^ (prefixWord ++ tailWord_3310849).sum := by decide
  have hdescent : baseEnd_3310849 < baseStart_3310849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310858 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_3310858 : Nat := 118140960795 + 3310858 * 2 ^ 59
def prefixEnd_3310858 : Nat := 4983230072969 + 3 ^ 40 * 3310858 * 2
def baseEnd_3310858 : Nat := 566687177594570828849549

theorem tailTrace_3310858 : CollatzResearch.WordTrace tailWord_3310858 prefixEnd_3310858 566687177594570828849549 := by
  unfold tailWord_3310858
  simp only [CollatzResearch.WordTrace]
  refine ⟨30189227959833597593443307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80504607892889593582515485 30189227959833597593443307)
  ·
    refine ⟨45283841939750396390164961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30189227959833597593443307 45283841939750396390164961)
    ·
      refine ⟨33962881454812797292623721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45283841939750396390164961 33962881454812797292623721)
      ·
        refine ⟨25472161091109597969467791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33962881454812797292623721 25472161091109597969467791)
        ·
          refine ⟨38208241636664396954201687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25472161091109597969467791 38208241636664396954201687)
          ·
            refine ⟨57312362454996595431302531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38208241636664396954201687 57312362454996595431302531)
            ·
              refine ⟨85968543682494893146953797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57312362454996595431302531 85968543682494893146953797)
              ·
                refine ⟨16119101940467792465053837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85968543682494893146953797 16119101940467792465053837)
                ·
                  refine ⟨6044663227675422174395189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16119101940467792465053837 6044663227675422174395189)
                  ·
                    refine ⟨566687177594570828849549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6044663227675422174395189 566687177594570828849549)
                    ·
                      rfl

theorem cell23_3310858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_3310858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310858 prefixEnd_3310858 := by exact prefixLift 3310858
  have htrace : WordTrace (prefixWord ++ tailWord_3310858) baseStart_3310858 baseEnd_3310858 := by
    simpa [prefixWord, tailWord_3310858, baseEnd_3310858] using wordTrace_append hprefix tailTrace_3310858
  have hstable : (prefixWord ++ tailWord_3310858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310858).length < 2 ^ (prefixWord ++ tailWord_3310858).sum := by decide
  have hdescent : baseEnd_3310858 < baseStart_3310858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310862 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_3310862 : Nat := 118140960795 + 3310862 * 2 ^ 59
def prefixEnd_3310862 : Nat := 4983230072969 + 3 ^ 40 * 3310862 * 2
def baseEnd_3310862 : Nat := 188895954078481163433181

theorem tailTrace_3310862 : CollatzResearch.WordTrace tailWord_3310862 prefixEnd_3310862 188895954078481163433181 := by
  unfold tailWord_3310862
  simp only [CollatzResearch.WordTrace]
  refine ⟨15094632216414987382114855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80504705154213266037945893 15094632216414987382114855)
  ·
    refine ⟨22641948324622481073172283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15094632216414987382114855 22641948324622481073172283)
    ·
      refine ⟨33962922486933721609758425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22641948324622481073172283 33962922486933721609758425)
      ·
        refine ⟨25472191865200291207318819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33962922486933721609758425 25472191865200291207318819)
        ·
          refine ⟨38208287797800436810978229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25472191865200291207318819 38208287797800436810978229)
          ·
            refine ⟨3582026981043790951029209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38208287797800436810978229 3582026981043790951029209)
            ·
              refine ⟨2686520235782843213271907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3582026981043790951029209 2686520235782843213271907)
              ·
                refine ⟨4029780353674264819907861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2686520235782843213271907 4029780353674264819907861)
                ·
                  refine ⟨188895954078481163433181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4029780353674264819907861 188895954078481163433181)
                  ·
                    rfl

theorem cell23_3310862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_3310862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310862 prefixEnd_3310862 := by exact prefixLift 3310862
  have htrace : WordTrace (prefixWord ++ tailWord_3310862) baseStart_3310862 baseEnd_3310862 := by
    simpa [prefixWord, tailWord_3310862, baseEnd_3310862] using wordTrace_append hprefix tailTrace_3310862
  have hstable : (prefixWord ++ tailWord_3310862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310862).length < 2 ^ (prefixWord ++ tailWord_3310862).sum := by decide
  have hdescent : baseEnd_3310862 < baseStart_3310862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310865 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 4, 3, 2]
def baseStart_3310865 : Nat := 118140960795 + 3310865 * 2 ^ 59
def prefixEnd_3310865 : Nat := 4983230072969 + 3 ^ 40 * 3310865 * 2
def baseEnd_3310865 : Nat := 1700065127148293959161115

theorem tailTrace_3310865 : CollatzResearch.WordTrace tailWord_3310865 prefixEnd_3310865 1700065127148293959161115 := by
  unfold tailWord_3310865
  simp only [CollatzResearch.WordTrace]
  refine ⟨120757167150309030569278049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80504778100206020379518699 120757167150309030569278049)
  ·
    refine ⟨90567875362731772926958537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120757167150309030569278049 90567875362731772926958537)
    ·
      refine ⟨67925906522048829695218903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90567875362731772926958537 67925906522048829695218903)
      ·
        refine ⟨101888859783073244542828355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67925906522048829695218903 101888859783073244542828355)
        ·
          refine ⟨152833289674609866814242533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101888859783073244542828355 152833289674609866814242533)
          ·
            refine ⟨28656241813989350027670475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152833289674609866814242533 28656241813989350027670475)
            ·
              refine ⟨42984362720984025041505713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28656241813989350027670475 42984362720984025041505713)
              ·
                refine ⟨32238272040738018781129285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42984362720984025041505713 32238272040738018781129285)
                ·
                  refine ⟨6044676007638378521461741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32238272040738018781129285 6044676007638378521461741)
                  ·
                    refine ⟨2266753502864391945548153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6044676007638378521461741 2266753502864391945548153)
                    ·
                      refine ⟨1700065127148293959161115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266753502864391945548153 1700065127148293959161115)
                      ·
                        rfl

theorem cell23_3310865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 3, 2].length) (baseStart_3310865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310865 prefixEnd_3310865 := by exact prefixLift 3310865
  have htrace : WordTrace (prefixWord ++ tailWord_3310865) baseStart_3310865 baseEnd_3310865 := by
    simpa [prefixWord, tailWord_3310865, baseEnd_3310865] using wordTrace_append hprefix tailTrace_3310865
  have hstable : (prefixWord ++ tailWord_3310865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310865).length < 2 ^ (prefixWord ++ tailWord_3310865).sum := by decide
  have hdescent : baseEnd_3310865 < baseStart_3310865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310912 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 3, 2, 2]
def baseStart_3310912 : Nat := 118140960795 + 3310912 * 2 ^ 59
def prefixEnd_3310912 : Nat := 4983230072969 + 3 ^ 40 * 3310912 * 2
def baseEnd_3310912 : Nat := 1700089260739055275273399

theorem tailTrace_3310912 : CollatzResearch.WordTrace tailWord_3310912 prefixEnd_3310912 1700089260739055275273399 := by
  unfold tailWord_3310912
  simp only [CollatzResearch.WordTrace]
  refine ⟨60379440690569378798119495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80505920920759171730825993 60379440690569378798119495)
  ·
    refine ⟨90569161035854068197179243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60379440690569378798119495 90569161035854068197179243)
    ·
      refine ⟨135853741553781102295768865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90569161035854068197179243 135853741553781102295768865)
      ·
        refine ⟨101890306165335826721826649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135853741553781102295768865 101890306165335826721826649)
        ·
          refine ⟨76417729624001870041369987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101890306165335826721826649 76417729624001870041369987)
          ·
            refine ⟨114626594436002805062054981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76417729624001870041369987 114626594436002805062054981)
            ·
              refine ⟨21492486456750525949135309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114626594436002805062054981 21492486456750525949135309)
              ·
                refine ⟨8059682421281447230925741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21492486456750525949135309 8059682421281447230925741)
                ·
                  refine ⟨3022380907980542711597153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8059682421281447230925741 3022380907980542711597153)
                  ·
                    refine ⟨2266785680985407033697865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3022380907980542711597153 2266785680985407033697865)
                    ·
                      refine ⟨1700089260739055275273399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266785680985407033697865 1700089260739055275273399)
                      ·
                        rfl

theorem cell23_3310912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3, 2, 2].length) (baseStart_3310912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310912 prefixEnd_3310912 := by exact prefixLift 3310912
  have htrace : WordTrace (prefixWord ++ tailWord_3310912) baseStart_3310912 baseEnd_3310912 := by
    simpa [prefixWord, tailWord_3310912, baseEnd_3310912] using wordTrace_append hprefix tailTrace_3310912
  have hstable : (prefixWord ++ tailWord_3310912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310912).length < 2 ^ (prefixWord ++ tailWord_3310912).sum := by decide
  have hdescent : baseEnd_3310912 < baseStart_3310912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310932 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_3310932 : Nat := 118140960795 + 3310932 * 2 ^ 59
def prefixEnd_3310932 : Nat := 4983230072969 + 3 ^ 40 * 3310932 * 2
def baseEnd_3310932 : Nat := 1700099530352145197023307

theorem tailTrace_3310932 : CollatzResearch.WordTrace tailWord_3310932 prefixEnd_3310932 1700099530352145197023307 := by
  unfold tailWord_3310932
  simp only [CollatzResearch.WordTrace]
  refine ⟨60379805420533150505983525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80506407227377534007978033 60379805420533150505983525)
  ·
    refine ⟨11321213516349965719871911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60379805420533150505983525 11321213516349965719871911)
    ·
      refine ⟨16981820274524948579807867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11321213516349965719871911 16981820274524948579807867)
      ·
        refine ⟨25472730411787422869711801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16981820274524948579807867 25472730411787422869711801)
        ·
          refine ⟨19104547808840567152283851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25472730411787422869711801 19104547808840567152283851)
          ·
            refine ⟨28656821713260850728425777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19104547808840567152283851 28656821713260850728425777)
            ·
              refine ⟨21492616284945638046319333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28656821713260850728425777 21492616284945638046319333)
              ·
                refine ⟨4029865553427307133684875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21492616284945638046319333 4029865553427307133684875)
                ·
                  refine ⟨6044798330140960700527313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4029865553427307133684875 6044798330140960700527313)
                  ·
                    refine ⟨4533598747605720525395485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6044798330140960700527313 4533598747605720525395485)
                    ·
                      refine ⟨1700099530352145197023307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4533598747605720525395485 1700099530352145197023307)
                      ·
                        rfl

theorem cell23_3310932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_3310932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310932 prefixEnd_3310932 := by exact prefixLift 3310932
  have htrace : WordTrace (prefixWord ++ tailWord_3310932) baseStart_3310932 baseEnd_3310932 := by
    simpa [prefixWord, tailWord_3310932, baseEnd_3310932] using wordTrace_append hprefix tailTrace_3310932
  have hstable : (prefixWord ++ tailWord_3310932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310932).length < 2 ^ (prefixWord ++ tailWord_3310932).sum := by decide
  have hdescent : baseEnd_3310932 < baseStart_3310932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310935 : List Nat := [1, 1, 3, 2, 3, 3, 3, 7]
def baseStart_3310935 : Nat := 118140960795 + 3310935 * 2 ^ 59
def prefixEnd_3310935 : Nat := 4983230072969 + 3 ^ 40 * 3310935 * 2
def baseEnd_3310935 : Nat := 62966706325707729084659

theorem tailTrace_3310935 : CollatzResearch.WordTrace tailWord_3310935 prefixEnd_3310935 62966706325707729084659 := by
  unfold tailWord_3310935
  simp only [CollatzResearch.WordTrace]
  refine ⟨120759720260055432524326259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80506480173370288349550839 120759720260055432524326259)
  ·
    refine ⟨181139580390083148786489389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120759720260055432524326259 181139580390083148786489389)
    ·
      refine ⟨67927342646281180794933521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181139580390083148786489389 67927342646281180794933521)
      ·
        refine ⟨50945506984710885596200141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67927342646281180794933521 50945506984710885596200141)
        ·
          refine ⟨19104565119266582098575053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50945506984710885596200141 19104565119266582098575053)
          ·
            refine ⟨7164211919724968286965645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19104565119266582098575053 7164211919724968286965645)
            ·
              refine ⟨2686579469896863107612117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7164211919724968286965645 2686579469896863107612117)
              ·
                refine ⟨62966706325707729084659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2686579469896863107612117 62966706325707729084659)
                ·
                  rfl

theorem cell23_3310935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 7].length) (baseStart_3310935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310935 prefixEnd_3310935 := by exact prefixLift 3310935
  have htrace : WordTrace (prefixWord ++ tailWord_3310935) baseStart_3310935 baseEnd_3310935 := by
    simpa [prefixWord, tailWord_3310935, baseEnd_3310935] using wordTrace_append hprefix tailTrace_3310935
  have hstable : (prefixWord ++ tailWord_3310935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310935).length < 2 ^ (prefixWord ++ tailWord_3310935).sum := by decide
  have hdescent : baseEnd_3310935 < baseStart_3310935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310962 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_3310962 : Nat := 118140960795 + 3310962 * 2 ^ 59
def prefixEnd_3310962 : Nat := 4983230072969 + 3 ^ 40 * 3310962 * 2
def baseEnd_3310962 : Nat := 1700114934771780079648169

theorem tailTrace_3310962 : CollatzResearch.WordTrace tailWord_3310962 prefixEnd_3310962 1700114934771780079648169 := by
  unfold tailWord_3310962
  simp only [CollatzResearch.WordTrace]
  refine ⟨30190176257739404033889785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80507136687305077423706093 30190176257739404033889785)
  ·
    refine ⟨22642632193304553025417339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30190176257739404033889785 22642632193304553025417339)
    ·
      refine ⟨33963948289956829538126009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22642632193304553025417339 33963948289956829538126009)
      ·
        refine ⟨25472961217467622153594507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33963948289956829538126009 25472961217467622153594507)
        ·
          refine ⟨38209441826201433230391761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25472961217467622153594507 38209441826201433230391761)
          ·
            refine ⟨28657081369651074922793821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38209441826201433230391761 28657081369651074922793821)
            ·
              refine ⟨10746405513619153096047683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28657081369651074922793821 10746405513619153096047683)
              ·
                refine ⟨16119608270428729644071525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746405513619153096047683 16119608270428729644071525)
                ·
                  refine ⟨3022426550705386808263411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16119608270428729644071525 3022426550705386808263411)
                  ·
                    refine ⟨4533639826058080212395117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3022426550705386808263411 4533639826058080212395117)
                    ·
                      refine ⟨1700114934771780079648169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4533639826058080212395117 1700114934771780079648169)
                      ·
                        rfl

theorem cell23_3310962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_3310962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310962 prefixEnd_3310962 := by exact prefixLift 3310962
  have htrace : WordTrace (prefixWord ++ tailWord_3310962) baseStart_3310962 baseEnd_3310962 := by
    simpa [prefixWord, tailWord_3310962, baseEnd_3310962] using wordTrace_append hprefix tailTrace_3310962
  have hstable : (prefixWord ++ tailWord_3310962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310962).length < 2 ^ (prefixWord ++ tailWord_3310962).sum := by decide
  have hdescent : baseEnd_3310962 < baseStart_3310962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311002 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2]
def baseStart_3311002 : Nat := 118140960795 + 3311002 * 2 ^ 59
def prefixEnd_3311002 : Nat := 4983230072969 + 3 ^ 40 * 3311002 * 2
def baseEnd_3311002 : Nat := 1700135473997959923147985

theorem tailTrace_3311002 : CollatzResearch.WordTrace tailWord_3311002 prefixEnd_3311002 1700135473997959923147985 := by
  unfold tailWord_3311002
  simp only [CollatzResearch.WordTrace]
  refine ⟨30190540987703175741753815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80508109300541801978010173 30190540987703175741753815)
  ·
    refine ⟨45285811481554763612630723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30190540987703175741753815 45285811481554763612630723)
    ·
      refine ⟨67928717222332145418946085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45285811481554763612630723 67928717222332145418946085)
      ·
        refine ⟨12736634479187277266052391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67928717222332145418946085 12736634479187277266052391)
        ·
          refine ⟨19104951718780915899078587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12736634479187277266052391 19104951718780915899078587)
          ·
            refine ⟨28657427578171373848617881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19104951718780915899078587 28657427578171373848617881)
            ·
              refine ⟨21493070683628530386463411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28657427578171373848617881 21493070683628530386463411)
              ·
                refine ⟨32239606025442795579695117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21493070683628530386463411 32239606025442795579695117)
                ·
                  refine ⟨12089852259541048342385669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32239606025442795579695117 12089852259541048342385669)
                  ·
                    refine ⟨2266847298663946564197313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12089852259541048342385669 2266847298663946564197313)
                    ·
                      refine ⟨1700135473997959923147985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266847298663946564197313 1700135473997959923147985)
                      ·
                        rfl

theorem cell23_3311002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_3311002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311002 prefixEnd_3311002 := by exact prefixLift 3311002
  have htrace : WordTrace (prefixWord ++ tailWord_3311002) baseStart_3311002 baseEnd_3311002 := by
    simpa [prefixWord, tailWord_3311002, baseEnd_3311002] using wordTrace_append hprefix tailTrace_3311002
  have hstable : (prefixWord ++ tailWord_3311002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311002).length < 2 ^ (prefixWord ++ tailWord_3311002).sum := by decide
  have hdescent : baseEnd_3311002 < baseStart_3311002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311005 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_3311005 : Nat := 118140960795 + 3311005 * 2 ^ 59
def prefixEnd_3311005 : Nat := 4983230072969 + 3 ^ 40 * 3311005 * 2
def baseEnd_3311005 : Nat := 1700137014439923411410471

theorem tailTrace_3311005 : CollatzResearch.WordTrace tailWord_3311005 prefixEnd_3311005 1700137014439923411410471 := by
  unfold tailWord_3311005
  simp only [CollatzResearch.WordTrace]
  refine ⟨120762273369801834479374469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80508182246534556319582979 120762273369801834479374469)
  ·
    refine ⟨22642926256837843964882713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120762273369801834479374469 22642926256837843964882713)
    ·
      refine ⟨16982194692628382973662035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22642926256837843964882713 16982194692628382973662035)
      ·
        refine ⟨25473292038942574460493053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16982194692628382973662035 25473292038942574460493053)
        ·
          refine ⟨9552484514603465422684895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25473292038942574460493053 9552484514603465422684895)
          ·
            refine ⟨14328726771905198134027343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9552484514603465422684895 14328726771905198134027343)
            ·
              refine ⟨21493090157857797201041015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14328726771905198134027343 21493090157857797201041015)
              ·
                refine ⟨32239635236786695801561523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21493090157857797201041015 32239635236786695801561523)
                ·
                  refine ⟨48359452855180043702342285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32239635236786695801561523 48359452855180043702342285)
                  ·
                    refine ⟨18134794820692516388378357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48359452855180043702342285 18134794820692516388378357)
                    ·
                      refine ⟨1700137014439923411410471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18134794820692516388378357 1700137014439923411410471)
                      ·
                        rfl

theorem cell23_3311005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_3311005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311005 prefixEnd_3311005 := by exact prefixLift 3311005
  have htrace : WordTrace (prefixWord ++ tailWord_3311005) baseStart_3311005 baseEnd_3311005 := by
    simpa [prefixWord, tailWord_3311005, baseEnd_3311005] using wordTrace_append hprefix tailTrace_3311005
  have hstable : (prefixWord ++ tailWord_3311005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311005).length < 2 ^ (prefixWord ++ tailWord_3311005).sum := by decide
  have hdescent : baseEnd_3311005 < baseStart_3311005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311055 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 2, 5]
def baseStart_3311055 : Nat := 118140960795 + 3311055 * 2 ^ 59
def prefixEnd_3311055 : Nat := 4983230072969 + 3 ^ 40 * 3311055 * 2
def baseEnd_3311055 : Nat := 566720896157549405261747

theorem tailTrace_3311055 : CollatzResearch.WordTrace tailWord_3311055 prefixEnd_3311055 566720896157549405261747 := by
  unfold tailWord_3311055
  simp only [CollatzResearch.WordTrace]
  refine ⟨120764097019620693018694619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80509398013080462012463079 120764097019620693018694619)
  ·
    refine ⟨181146145529431039528041929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120764097019620693018694619 181146145529431039528041929)
    ·
      refine ⟨135859609147073279646031447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181146145529431039528041929 135859609147073279646031447)
      ·
        refine ⟨203789413720609919469047171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135859609147073279646031447 203789413720609919469047171)
        ·
          refine ⟨305684120580914879203570757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203789413720609919469047171 305684120580914879203570757)
          ·
            refine ⟨57315772608921539850669517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305684120580914879203570757 57315772608921539850669517)
            ·
              refine ⟨21493414728345577444001069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57315772608921539850669517 21493414728345577444001069)
              ·
                refine ⟨8060030523129591541500401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21493414728345577444001069 8060030523129591541500401)
                ·
                  refine ⟨6045022892347193656125301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8060030523129591541500401 6045022892347193656125301)
                  ·
                    refine ⟨566720896157549405261747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6045022892347193656125301 566720896157549405261747)
                    ·
                      rfl

theorem cell23_3311055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_3311055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311055 prefixEnd_3311055 := by exact prefixLift 3311055
  have htrace : WordTrace (prefixWord ++ tailWord_3311055) baseStart_3311055 baseEnd_3311055 := by
    simpa [prefixWord, tailWord_3311055, baseEnd_3311055] using wordTrace_append hprefix tailTrace_3311055
  have hstable : (prefixWord ++ tailWord_3311055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311055).length < 2 ^ (prefixWord ++ tailWord_3311055).sum := by decide
  have hdescent : baseEnd_3311055 < baseStart_3311055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311065 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 5]
def baseStart_3311065 : Nat := 118140960795 + 3311065 * 2 ^ 59
def prefixEnd_3311065 : Nat := 4983230072969 + 3 ^ 40 * 3311065 * 2
def baseEnd_3311065 : Nat := 1700167823279193176660195

theorem tailTrace_3311065 : CollatzResearch.WordTrace tailWord_3311065 prefixEnd_3311065 1700167823279193176660195 := by
  unfold tailWord_3311065
  simp only [CollatzResearch.WordTrace]
  refine ⟨120764461749584464726558649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80509641166389643151039099 120764461749584464726558649)
  ·
    refine ⟨90573346312188348544918987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120764461749584464726558649 90573346312188348544918987)
    ·
      refine ⟨135860019468282522817378481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90573346312188348544918987 135860019468282522817378481)
      ·
        refine ⟨101895014601211892113033861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135860019468282522817378481 101895014601211892113033861)
        ·
          refine ⟨19105315237727229771193849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101895014601211892113033861 19105315237727229771193849)
          ·
            refine ⟨14328986428295422328395387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19105315237727229771193849 14328986428295422328395387)
            ·
              refine ⟨21493479642443133492593081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14328986428295422328395387 21493479642443133492593081)
              ·
                refine ⟨16120109731832350119444811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21493479642443133492593081 16120109731832350119444811)
                ·
                  refine ⟨24180164597748525179167217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16120109731832350119444811 24180164597748525179167217)
                  ·
                    refine ⟨18135123448311393884375413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24180164597748525179167217 18135123448311393884375413)
                    ·
                      refine ⟨1700167823279193176660195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18135123448311393884375413 1700167823279193176660195)
                      ·
                        rfl

theorem cell23_3311065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_3311065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311065 prefixEnd_3311065 := by exact prefixLift 3311065
  have htrace : WordTrace (prefixWord ++ tailWord_3311065) baseStart_3311065 baseEnd_3311065 := by
    simpa [prefixWord, tailWord_3311065, baseEnd_3311065] using wordTrace_append hprefix tailTrace_3311065
  have hstable : (prefixWord ++ tailWord_3311065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311065).length < 2 ^ (prefixWord ++ tailWord_3311065).sum := by decide
  have hdescent : baseEnd_3311065 < baseStart_3311065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311106 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3311106 : Nat := 118140960795 + 3311106 * 2 ^ 59
def prefixEnd_3311106 : Nat := 4983230072969 + 3 ^ 40 * 3311106 * 2
def baseEnd_3311106 : Nat := 566729625328675838749169

theorem tailTrace_3311106 : CollatzResearch.WordTrace tailWord_3311106 prefixEnd_3311106 566729625328675838749169 := by
  unfold tailWord_3311106
  simp only [CollatzResearch.WordTrace]
  refine ⟨30191489285608982182200293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80510638094957285819200781 30191489285608982182200293)
  ·
    refine ⟨5660904241051684159162555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30191489285608982182200293 5660904241051684159162555)
    ·
      refine ⟨8491356361577526238743833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5660904241051684159162555 8491356361577526238743833)
      ·
        refine ⟨6368517271183144679057875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8491356361577526238743833 6368517271183144679057875)
        ·
          refine ⟨9552775906774717018586813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6368517271183144679057875 9552775906774717018586813)
          ·
            refine ⟨3582290965040518881970055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9552775906774717018586813 3582290965040518881970055)
            ·
              refine ⟨5373436447560778322955083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582290965040518881970055 5373436447560778322955083)
              ·
                refine ⟨8060154671341167484432625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5373436447560778322955083 8060154671341167484432625)
                ·
                  refine ⟨6045116003505875613324469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8060154671341167484432625 6045116003505875613324469)
                  ·
                    refine ⟨566729625328675838749169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6045116003505875613324469 566729625328675838749169)
                    ·
                      rfl

theorem cell23_3311106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3311106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311106 prefixEnd_3311106 := by exact prefixLift 3311106
  have htrace : WordTrace (prefixWord ++ tailWord_3311106) baseStart_3311106 baseEnd_3311106 := by
    simpa [prefixWord, tailWord_3311106, baseEnd_3311106] using wordTrace_append hprefix tailTrace_3311106
  have hstable : (prefixWord ++ tailWord_3311106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311106).length < 2 ^ (prefixWord ++ tailWord_3311106).sum := by decide
  have hdescent : baseEnd_3311106 < baseStart_3311106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311110 : List Nat := [6, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3311110 : Nat := 118140960795 + 3311110 * 2 ^ 59
def prefixEnd_3311110 : Nat := 4983230072969 + 3 ^ 40 * 3311110 * 2
def baseEnd_3311110 : Nat := 188910103323182833399721

theorem tailTrace_3311110 : CollatzResearch.WordTrace tailWord_3311110 prefixEnd_3311110 188910103323182833399721 := by
  unfold tailWord_3311110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3773940719825669919123337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80510735356280958274631189 3773940719825669919123337)
  ·
    refine ⟨2830455539869252439342503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3773940719825669919123337 2830455539869252439342503)
    ·
      refine ⟨4245683309803878659013755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2830455539869252439342503 4245683309803878659013755)
      ·
        refine ⟨6368524964705817988520633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4245683309803878659013755 6368524964705817988520633)
        ·
          refine ⟨4776393723529363491390475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6368524964705817988520633 4776393723529363491390475)
          ·
            refine ⟨7164590585294045237085713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776393723529363491390475 7164590585294045237085713)
            ·
              refine ⟨5373442938970533927814285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7164590585294045237085713 5373442938970533927814285)
              ·
                refine ⟨2015041102113950222930357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5373442938970533927814285 2015041102113950222930357)
                ·
                  refine ⟨188910103323182833399721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2015041102113950222930357 188910103323182833399721)
                  ·
                    rfl

theorem cell23_3311110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3311110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311110 prefixEnd_3311110 := by exact prefixLift 3311110
  have htrace : WordTrace (prefixWord ++ tailWord_3311110) baseStart_3311110 baseEnd_3311110 := by
    simpa [prefixWord, tailWord_3311110, baseEnd_3311110] using wordTrace_append hprefix tailTrace_3311110
  have hstable : (prefixWord ++ tailWord_3311110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311110).length < 2 ^ (prefixWord ++ tailWord_3311110).sum := by decide
  have hdescent : baseEnd_3311110 < baseStart_3311110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311135 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_3311135 : Nat := 118140960795 + 3311135 * 2 ^ 59
def prefixEnd_3311135 : Nat := 4983230072969 + 3 ^ 40 * 3311135 * 2
def baseEnd_3311135 : Nat := 1700203766925007902784873

theorem tailTrace_3311135 : CollatzResearch.WordTrace tailWord_3311135 prefixEnd_3311135 1700203766925007902784873 := by
  unfold tailWord_3311135
  simp only [CollatzResearch.WordTrace]
  refine ⟨120767014859330866681606859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80511343239553911121071239 120767014859330866681606859)
  ·
    refine ⟨181150522288996300022410289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120767014859330866681606859 181150522288996300022410289)
    ·
      refine ⟨135862891716747225016807717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181150522288996300022410289 135862891716747225016807717)
      ·
        refine ⟨25474292196890104690651447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135862891716747225016807717 25474292196890104690651447)
        ·
          refine ⟨38211438295335157035977171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25474292196890104690651447 38211438295335157035977171)
          ·
            refine ⟨57317157443002735553965757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38211438295335157035977171 57317157443002735553965757)
            ·
              refine ⟨21493934041126025832737159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57317157443002735553965757 21493934041126025832737159)
              ·
                refine ⟨32240901061689038749105739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21493934041126025832737159 32240901061689038749105739)
                ·
                  refine ⟨48361351592533558123658609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32240901061689038749105739 48361351592533558123658609)
                  ·
                    refine ⟨36271013694400168592743957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48361351592533558123658609 36271013694400168592743957)
                    ·
                      refine ⟨1700203766925007902784873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36271013694400168592743957 1700203766925007902784873)
                      ·
                        rfl

theorem cell23_3311135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_3311135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311135 prefixEnd_3311135 := by exact prefixLift 3311135
  have htrace : WordTrace (prefixWord ++ tailWord_3311135) baseStart_3311135 baseEnd_3311135 := by
    simpa [prefixWord, tailWord_3311135, baseEnd_3311135] using wordTrace_append hprefix tailTrace_3311135
  have hstable : (prefixWord ++ tailWord_3311135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311135).length < 2 ^ (prefixWord ++ tailWord_3311135).sum := by decide
  have hdescent : baseEnd_3311135 < baseStart_3311135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311136 : List Nat := [2, 1, 1, 6, 1, 1, 2, 4, 1, 4]
def baseStart_3311136 : Nat := 118140960795 + 3311136 * 2 ^ 59
def prefixEnd_3311136 : Nat := 4983230072969 + 3 ^ 40 * 3311136 * 2
def baseEnd_3311136 : Nat := 566734760135220799624123

theorem tailTrace_3311136 : CollatzResearch.WordTrace tailWord_3311136 prefixEnd_3311136 566734760135220799624123 := by
  unfold tailWord_3311136
  simp only [CollatzResearch.WordTrace]
  refine ⟨60383525666163621926196631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80511367554884829234928841 60383525666163621926196631)
  ·
    refine ⟨90575288499245432889294947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60383525666163621926196631 90575288499245432889294947)
    ·
      refine ⟨135862932748868149333942421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90575288499245432889294947 135862932748868149333942421)
      ·
        refine ⟨6368574972603194500028551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135862932748868149333942421 6368574972603194500028551)
        ·
          refine ⟨9552862458904791750042827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6368574972603194500028551 9552862458904791750042827)
          ·
            refine ⟨14329293688357187625064241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9552862458904791750042827 14329293688357187625064241)
            ·
              refine ⟨10746970266267890718798181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14329293688357187625064241 10746970266267890718798181)
              ·
                refine ⟨2015056924925229509774659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10746970266267890718798181 2015056924925229509774659)
                ·
                  refine ⟨3022585387387844264661989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015056924925229509774659 3022585387387844264661989)
                  ·
                    refine ⟨566734760135220799624123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3022585387387844264661989 566734760135220799624123)
                    ·
                      rfl

theorem cell23_3311136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 1, 4].length) (baseStart_3311136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311136 prefixEnd_3311136 := by exact prefixLift 3311136
  have htrace : WordTrace (prefixWord ++ tailWord_3311136) baseStart_3311136 baseEnd_3311136 := by
    simpa [prefixWord, tailWord_3311136, baseEnd_3311136] using wordTrace_append hprefix tailTrace_3311136
  have hstable : (prefixWord ++ tailWord_3311136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311136).length < 2 ^ (prefixWord ++ tailWord_3311136).sum := by decide
  have hdescent : baseEnd_3311136 < baseStart_3311136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311159 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 3, 1, 3]
def baseStart_3311159 : Nat := 118140960795 + 3311159 * 2 ^ 59
def prefixEnd_3311159 : Nat := 4983230072969 + 3 ^ 40 * 3311159 * 2
def baseEnd_3311159 : Nat := 1700216090460715808884763

theorem tailTrace_3311159 : CollatzResearch.WordTrace tailWord_3311159 prefixEnd_3311159 1700216090460715808884763 := by
  unfold tailWord_3311159
  simp only [CollatzResearch.WordTrace]
  refine ⟨120767890211243918780480531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80511926807495945853653687 120767890211243918780480531)
  ·
    refine ⟨181151835316865878170720797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120767890211243918780480531 181151835316865878170720797)
    ·
      refine ⟨67931938243824704314020299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181151835316865878170720797 67931938243824704314020299)
      ·
        refine ⟨101897907365737056471030449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67931938243824704314020299 101897907365737056471030449)
        ·
          refine ⟨76423430524302792353272837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101897907365737056471030449 76423430524302792353272837)
          ·
            refine ⟨14329393223306773566238657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76423430524302792353272837 14329393223306773566238657)
            ·
              refine ⟨10747044917480080174678993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14329393223306773566238657 10747044917480080174678993)
              ·
                refine ⟨8060283688110060131009245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10747044917480080174678993 8060283688110060131009245)
                ·
                  refine ⟨3022606383041272549128467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8060283688110060131009245 3022606383041272549128467)
                  ·
                    refine ⟨4533909574561908823692701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3022606383041272549128467 4533909574561908823692701)
                    ·
                      refine ⟨1700216090460715808884763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4533909574561908823692701 1700216090460715808884763)
                      ·
                        rfl

theorem cell23_3311159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_3311159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311159 prefixEnd_3311159 := by exact prefixLift 3311159
  have htrace : WordTrace (prefixWord ++ tailWord_3311159) baseStart_3311159 baseEnd_3311159 := by
    simpa [prefixWord, tailWord_3311159, baseEnd_3311159] using wordTrace_append hprefix tailTrace_3311159
  have hstable : (prefixWord ++ tailWord_3311159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311159).length < 2 ^ (prefixWord ++ tailWord_3311159).sum := by decide
  have hdescent : baseEnd_3311159 < baseStart_3311159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311169 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_3311169 : Nat := 118140960795 + 3311169 * 2 ^ 59
def prefixEnd_3311169 : Nat := 4983230072969 + 3 ^ 40 * 3311169 * 2
def baseEnd_3311169 : Nat := 1700221225267260769759717

theorem tailTrace_3311169 : CollatzResearch.WordTrace tailWord_3311169 prefixEnd_3311169 1700221225267260769759717 := by
  unfold tailWord_3311169
  simp only [CollatzResearch.WordTrace]
  refine ⟨120768254941207690488344561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80512169960805126992229707 120768254941207690488344561)
  ·
    refine ⟨90576191205905767866258421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120768254941207690488344561 90576191205905767866258421)
    ·
      refine ⟨8491517925553665737461727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90576191205905767866258421 8491517925553665737461727)
      ·
        refine ⟨12737276888330498606192591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8491517925553665737461727 12737276888330498606192591)
        ·
          refine ⟨19105915332495747909288887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12737276888330498606192591 19105915332495747909288887)
          ·
            refine ⟨28658872998743621863933331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19105915332495747909288887 28658872998743621863933331)
            ·
              refine ⟨42988309498115432795899997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28658872998743621863933331 42988309498115432795899997)
              ·
                refine ⟨16120616061793287298462499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42988309498115432795899997 16120616061793287298462499)
                ·
                  refine ⟨24180924092689930947693749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16120616061793287298462499 24180924092689930947693749)
                  ·
                    refine ⟨2266961633689681026346289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24180924092689930947693749 2266961633689681026346289)
                    ·
                      refine ⟨1700221225267260769759717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266961633689681026346289 1700221225267260769759717)
                      ·
                        rfl

theorem cell23_3311169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_3311169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311169 prefixEnd_3311169 := by exact prefixLift 3311169
  have htrace : WordTrace (prefixWord ++ tailWord_3311169) baseStart_3311169 baseEnd_3311169 := by
    simpa [prefixWord, tailWord_3311169, baseEnd_3311169] using wordTrace_append hprefix tailTrace_3311169
  have hstable : (prefixWord ++ tailWord_3311169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311169).length < 2 ^ (prefixWord ++ tailWord_3311169).sum := by decide
  have hdescent : baseEnd_3311169 < baseStart_3311169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311182 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3311182 : Nat := 118140960795 + 3311182 * 2 ^ 59
def prefixEnd_3311182 : Nat := 4983230072969 + 3 ^ 40 * 3311182 * 2
def baseEnd_3311182 : Nat := 1700227900515769218897157

theorem tailTrace_3311182 : CollatzResearch.WordTrace tailWord_3311182 prefixEnd_3311182 1700227900515769218897157 := by
  unfold tailWord_3311182
  simp only [CollatzResearch.WordTrace]
  refine ⟨15096091136270074213570975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80512486060107062472378533 15096091136270074213570975)
  ·
    refine ⟨22644136704405111320356463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15096091136270074213570975 22644136704405111320356463)
    ·
      refine ⟨33966205056607666980534695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22644136704405111320356463 33966205056607666980534695)
      ·
        refine ⟨50949307584911500470802043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33966205056607666980534695 50949307584911500470802043)
        ·
          refine ⟨76423961377367250706203065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50949307584911500470802043 76423961377367250706203065)
          ·
            refine ⟨57317971033025438029652299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76423961377367250706203065 57317971033025438029652299)
            ·
              refine ⟨85976956549538157044478449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57317971033025438029652299 85976956549538157044478449)
              ·
                refine ⟨64482717412153617783358837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85976956549538157044478449 64482717412153617783358837)
                ·
                  refine ⟨6045254757389401667189891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64482717412153617783358837 6045254757389401667189891)
                  ·
                    refine ⟨9067882136084102500784837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6045254757389401667189891 9067882136084102500784837)
                    ·
                      refine ⟨1700227900515769218897157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9067882136084102500784837 1700227900515769218897157)
                      ·
                        rfl

theorem cell23_3311182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3311182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311182 prefixEnd_3311182 := by exact prefixLift 3311182
  have htrace : WordTrace (prefixWord ++ tailWord_3311182) baseStart_3311182 baseEnd_3311182 := by
    simpa [prefixWord, tailWord_3311182, baseEnd_3311182] using wordTrace_append hprefix tailTrace_3311182
  have hstable : (prefixWord ++ tailWord_3311182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311182).length < 2 ^ (prefixWord ++ tailWord_3311182).sum := by decide
  have hdescent : baseEnd_3311182 < baseStart_3311182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311186 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_3311186 : Nat := 118140960795 + 3311186 * 2 ^ 59
def prefixEnd_3311186 : Nat := 4983230072969 + 3 ^ 40 * 3311186 * 2
def baseEnd_3311186 : Nat := 1700229954438387203247139

theorem tailTrace_3311186 : CollatzResearch.WordTrace tailWord_3311186 prefixEnd_3311186 1700229954438387203247139 := by
  unfold tailWord_3311186
  simp only [CollatzResearch.WordTrace]
  refine ⟨30192218745536525597928353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80512583321430734927808941 30192218745536525597928353)
  ·
    refine ⟨22644164059152394198446265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30192218745536525597928353 22644164059152394198446265)
    ·
      refine ⟨16983123044364295648834699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22644164059152394198446265 16983123044364295648834699)
      ·
        refine ⟨25474684566546443473252049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16983123044364295648834699 25474684566546443473252049)
        ·
          refine ⟨19106013424909832604939037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25474684566546443473252049 19106013424909832604939037)
          ·
            refine ⟨7164755034341187226852139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19106013424909832604939037 7164755034341187226852139)
            ·
              refine ⟨10747132551511780840278209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164755034341187226852139 10747132551511780840278209)
              ·
                refine ⟨8060349413633835630208657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10747132551511780840278209 8060349413633835630208657)
                ·
                  refine ⟨6045262060225376722656493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8060349413633835630208657 6045262060225376722656493)
                  ·
                    refine ⟨2266973272584516270996185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6045262060225376722656493 2266973272584516270996185)
                    ·
                      refine ⟨1700229954438387203247139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266973272584516270996185 1700229954438387203247139)
                      ·
                        rfl

theorem cell23_3311186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_3311186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311186 prefixEnd_3311186 := by exact prefixLift 3311186
  have htrace : WordTrace (prefixWord ++ tailWord_3311186) baseStart_3311186 baseEnd_3311186 := by
    simpa [prefixWord, tailWord_3311186, baseEnd_3311186] using wordTrace_append hprefix tailTrace_3311186
  have hstable : (prefixWord ++ tailWord_3311186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311186).length < 2 ^ (prefixWord ++ tailWord_3311186).sum := by decide
  have hdescent : baseEnd_3311186 < baseStart_3311186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311212 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_3311212 : Nat := 118140960795 + 3311212 * 2 ^ 59
def prefixEnd_3311212 : Nat := 4983230072969 + 3 ^ 40 * 3311212 * 2
def baseEnd_3311212 : Nat := 1700243304935404101522019

theorem tailTrace_3311212 : CollatzResearch.WordTrace tailWord_3311212 prefixEnd_3311212 1700243304935404101522019 := by
  unfold tailWord_3311212
  simp only [CollatzResearch.WordTrace]
  refine ⟨60384911640025954416079945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80513215520034605888106593 60384911640025954416079945)
  ·
    refine ⟨45288683730019465812059959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60384911640025954416079945 45288683730019465812059959)
    ·
      refine ⟨67933025595029198718089939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45288683730019465812059959 67933025595029198718089939)
      ·
        refine ⟨101899538392543798077134909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67933025595029198718089939 101899538392543798077134909)
        ·
          refine ⟨38212326897203924278925591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101899538392543798077134909 38212326897203924278925591)
          ·
            refine ⟨57318490345805886418388387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38212326897203924278925591 57318490345805886418388387)
            ·
              refine ⟨85977735518708829627582581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57318490345805886418388387 85977735518708829627582581)
              ·
                refine ⟨8060412704878952777585867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85977735518708829627582581 8060412704878952777585867)
                ·
                  refine ⟨12090619057318429166378801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060412704878952777585867 12090619057318429166378801)
                  ·
                    refine ⟨9067964292988821874784101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12090619057318429166378801 9067964292988821874784101)
                    ·
                      refine ⟨1700243304935404101522019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9067964292988821874784101 1700243304935404101522019)
                      ·
                        rfl

theorem cell23_3311212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_3311212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311212 prefixEnd_3311212 := by exact prefixLift 3311212
  have htrace : WordTrace (prefixWord ++ tailWord_3311212) baseStart_3311212 baseEnd_3311212 := by
    simpa [prefixWord, tailWord_3311212, baseEnd_3311212] using wordTrace_append hprefix tailTrace_3311212
  have hstable : (prefixWord ++ tailWord_3311212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311212).length < 2 ^ (prefixWord ++ tailWord_3311212).sum := by decide
  have hdescent : baseEnd_3311212 < baseStart_3311212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311213 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_3311213 : Nat := 118140960795 + 3311213 * 2 ^ 59
def prefixEnd_3311213 : Nat := 4983230072969 + 3 ^ 40 * 3311213 * 2
def baseEnd_3311213 : Nat := 566747939472019532536505

theorem tailTrace_3311213 : CollatzResearch.WordTrace tailWord_3311213 prefixEnd_3311213 566747939472019532536505 := by
  unfold tailWord_3311213
  simp only [CollatzResearch.WordTrace]
  refine ⟨120769859753048286002946293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80513239835365524001964195 120769859753048286002946293)
  ·
    refine ⟨11322174351848276812776215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120769859753048286002946293 11322174351848276812776215)
    ·
      refine ⟨16983261527772415219164323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11322174351848276812776215 16983261527772415219164323)
      ·
        refine ⟨25474892291658622828746485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16983261527772415219164323 25474892291658622828746485)
        ·
          refine ⟨2388271152342995890194983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25474892291658622828746485 2388271152342995890194983)
          ·
            refine ⟨3582406728514493835292475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388271152342995890194983 3582406728514493835292475)
            ·
              refine ⟨5373610092771740752938713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582406728514493835292475 5373610092771740752938713)
              ·
                refine ⟨4030207569578805564704035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5373610092771740752938713 4030207569578805564704035)
                ·
                  refine ⟨6045311354368208347056053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030207569578805564704035 6045311354368208347056053)
                  ·
                    refine ⟨566747939472019532536505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6045311354368208347056053 566747939472019532536505)
                    ·
                      rfl

theorem cell23_3311213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_3311213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311213 prefixEnd_3311213 := by exact prefixLift 3311213
  have htrace : WordTrace (prefixWord ++ tailWord_3311213) baseStart_3311213 baseEnd_3311213 := by
    simpa [prefixWord, tailWord_3311213, baseEnd_3311213] using wordTrace_append hprefix tailTrace_3311213
  have hstable : (prefixWord ++ tailWord_3311213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311213).length < 2 ^ (prefixWord ++ tailWord_3311213).sum := by decide
  have hdescent : baseEnd_3311213 < baseStart_3311213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311216 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 4]
def baseStart_3311216 : Nat := 118140960795 + 3311216 * 2 ^ 59
def prefixEnd_3311216 : Nat := 4983230072969 + 3 ^ 40 * 3311216 * 2
def baseEnd_3311216 : Nat := 1700245358858022085872001

theorem tailTrace_3311216 : CollatzResearch.WordTrace tailWord_3311216 prefixEnd_3311216 1700245358858022085872001 := by
  unfold tailWord_3311216
  simp only [CollatzResearch.WordTrace]
  refine ⟨60384984586018708757652751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80513312781358278343537001 60384984586018708757652751)
  ·
    refine ⟨90577476879028063136479127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60384984586018708757652751 90577476879028063136479127)
    ·
      refine ⟨135866215318542094704718691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90577476879028063136479127 135866215318542094704718691)
      ·
        refine ⟨203799322977813142057078037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135866215318542094704718691 203799322977813142057078037)
        ·
          refine ⟨9553093264584991033925533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 203799322977813142057078037 9553093264584991033925533)
          ·
            refine ⟨3582409974219371637722075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9553093264584991033925533 3582409974219371637722075)
            ·
              refine ⟨5373614961329057456583113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582409974219371637722075 5373614961329057456583113)
              ·
                refine ⟨4030211220996793092437335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5373614961329057456583113 4030211220996793092437335)
                ·
                  refine ⟨6045316831495189638656003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030211220996793092437335 6045316831495189638656003)
                  ·
                    refine ⟨9067975247242784457984005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6045316831495189638656003 9067975247242784457984005)
                    ·
                      refine ⟨1700245358858022085872001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9067975247242784457984005 1700245358858022085872001)
                      ·
                        rfl

theorem cell23_3311216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 4].length) (baseStart_3311216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311216 prefixEnd_3311216 := by exact prefixLift 3311216
  have htrace : WordTrace (prefixWord ++ tailWord_3311216) baseStart_3311216 baseEnd_3311216 := by
    simpa [prefixWord, tailWord_3311216, baseEnd_3311216] using wordTrace_append hprefix tailTrace_3311216
  have hstable : (prefixWord ++ tailWord_3311216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311216).length < 2 ^ (prefixWord ++ tailWord_3311216).sum := by decide
  have hdescent : baseEnd_3311216 < baseStart_3311216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311229 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_3311229 : Nat := 118140960795 + 3311229 * 2 ^ 59
def prefixEnd_3311229 : Nat := 4983230072969 + 3 ^ 40 * 3311229 * 2
def baseEnd_3311229 : Nat := 1700252034106530535009441

theorem tailTrace_3311229 : CollatzResearch.WordTrace tailWord_3311229 prefixEnd_3311229 1700252034106530535009441 := by
  unfold tailWord_3311229
  simp only [CollatzResearch.WordTrace]
  refine ⟨120770443320990320735528741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80513628880660213823685827 120770443320990320735528741)
  ·
    refine ⟨22644458122685685137911639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120770443320990320735528741 22644458122685685137911639)
    ·
      refine ⟨33966687184028527706867459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22644458122685685137911639 33966687184028527706867459)
      ·
        refine ⟨50950030776042791560301189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33966687184028527706867459 50950030776042791560301189)
        ·
          refine ⟨9553130770508023417556473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50950030776042791560301189 9553130770508023417556473)
          ·
            refine ⟨7164848077881017563167355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9553130770508023417556473 7164848077881017563167355)
            ·
              refine ⟨10747272116821526344751033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164848077881017563167355 10747272116821526344751033)
              ·
                refine ⟨8060454087616144758563275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10747272116821526344751033 8060454087616144758563275)
                ·
                  refine ⟨12090681131424217137844913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060454087616144758563275 12090681131424217137844913)
                  ·
                    refine ⟨9068010848568162853383685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12090681131424217137844913 9068010848568162853383685)
                    ·
                      refine ⟨1700252034106530535009441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9068010848568162853383685 1700252034106530535009441)
                      ·
                        rfl

theorem cell23_3311229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_3311229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311229 prefixEnd_3311229 := by exact prefixLift 3311229
  have htrace : WordTrace (prefixWord ++ tailWord_3311229) baseStart_3311229 baseEnd_3311229 := by
    simpa [prefixWord, tailWord_3311229, baseEnd_3311229] using wordTrace_append hprefix tailTrace_3311229
  have hstable : (prefixWord ++ tailWord_3311229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311229).length < 2 ^ (prefixWord ++ tailWord_3311229).sum := by decide
  have hdescent : baseEnd_3311229 < baseStart_3311229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311236 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_3311236 : Nat := 118140960795 + 3311236 * 2 ^ 59
def prefixEnd_3311236 : Nat := 4983230072969 + 3 ^ 40 * 3311236 * 2
def baseEnd_3311236 : Nat := 1700255628471112007621909

theorem tailTrace_3311236 : CollatzResearch.WordTrace tailWord_3311236 prefixEnd_3311236 1700255628471112007621909 := by
  unfold tailWord_3311236
  simp only [CollatzResearch.WordTrace]
  refine ⟨60385349315982480465516781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80513799087976640620689041 60385349315982480465516781)
  ·
    refine ⟨22644505993493430174568793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60385349315982480465516781 22644505993493430174568793)
    ·
      refine ⟨16983379495120072630926595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22644505993493430174568793 16983379495120072630926595)
      ·
        refine ⟨25475069242680108946389893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16983379495120072630926595 25475069242680108946389893)
        ·
          refine ⟨4776575483002520427448105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25475069242680108946389893 4776575483002520427448105)
          ·
            refine ⟨3582431612251890320586079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4776575483002520427448105 3582431612251890320586079)
            ·
              refine ⟨5373647418377835480879119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582431612251890320586079 5373647418377835480879119)
              ·
                refine ⟨8060471127566753221318679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5373647418377835480879119 8060471127566753221318679)
                ·
                  refine ⟨12090706691350129831978019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060471127566753221318679 12090706691350129831978019)
                  ·
                    refine ⟨18136060037025194747967029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12090706691350129831978019 18136060037025194747967029)
                    ·
                      refine ⟨1700255628471112007621909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18136060037025194747967029 1700255628471112007621909)
                      ·
                        rfl

theorem cell23_3311236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_3311236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311236 prefixEnd_3311236 := by exact prefixLift 3311236
  have htrace : WordTrace (prefixWord ++ tailWord_3311236) baseStart_3311236 baseEnd_3311236 := by
    simpa [prefixWord, tailWord_3311236, baseEnd_3311236] using wordTrace_append hprefix tailTrace_3311236
  have hstable : (prefixWord ++ tailWord_3311236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311236).length < 2 ^ (prefixWord ++ tailWord_3311236).sum := by decide
  have hdescent : baseEnd_3311236 < baseStart_3311236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311396 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_3311396 : Nat := 118140960795 + 3311396 * 2 ^ 59
def prefixEnd_3311396 : Nat := 4983230072969 + 3 ^ 40 * 3311396 * 2
def baseEnd_3311396 : Nat := 1700337785375831381621173

theorem tailTrace_3311396 : CollatzResearch.WordTrace tailWord_3311396 prefixEnd_3311396 1700337785375831381621173 := by
  unfold tailWord_3311396
  simp only [CollatzResearch.WordTrace]
  refine ⟨60388267155692654128429021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80517689540923538837905361 60388267155692654128429021)
  ·
    refine ⟨22645600183384745298160883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60388267155692654128429021 22645600183384745298160883)
    ·
      refine ⟨33968400275077117947241325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22645600183384745298160883 33968400275077117947241325)
      ·
        refine ⟨12738150103153919230215497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33968400275077117947241325 12738150103153919230215497)
        ·
          refine ⟨9553612577365439422661623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12738150103153919230215497 9553612577365439422661623)
          ·
            refine ⟨14330418866048159133992435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9553612577365439422661623 14330418866048159133992435)
            ·
              refine ⟨21495628299072238700988653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14330418866048159133992435 21495628299072238700988653)
              ·
                refine ⟨8060860612152089512870745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21495628299072238700988653 8060860612152089512870745)
                ·
                  refine ⟨6045645459114067134653059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8060860612152089512870745 6045645459114067134653059)
                  ·
                    refine ⟨9068468188671100701979589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6045645459114067134653059 9068468188671100701979589)
                    ·
                      refine ⟨1700337785375831381621173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9068468188671100701979589 1700337785375831381621173)
                      ·
                        rfl

theorem cell23_3311396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_3311396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311396 prefixEnd_3311396 := by exact prefixLift 3311396
  have htrace : WordTrace (prefixWord ++ tailWord_3311396) baseStart_3311396 baseEnd_3311396 := by
    simpa [prefixWord, tailWord_3311396, baseEnd_3311396] using wordTrace_append hprefix tailTrace_3311396
  have hstable : (prefixWord ++ tailWord_3311396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311396).length < 2 ^ (prefixWord ++ tailWord_3311396).sum := by decide
  have hdescent : baseEnd_3311396 < baseStart_3311396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311416 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 2, 2, 3]
def baseStart_3311416 : Nat := 118140960795 + 3311416 * 2 ^ 59
def prefixEnd_3311416 : Nat := 4983230072969 + 3 ^ 40 * 3311416 * 2
def baseEnd_3311416 : Nat := 1700348054988921303371081

theorem tailTrace_3311416 : CollatzResearch.WordTrace tailWord_3311416 prefixEnd_3311416 1700348054988921303371081 := by
  unfold tailWord_3311416
  simp only [CollatzResearch.WordTrace]
  refine ⟨60388631885656425836293051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80518175847541901115057401 60388631885656425836293051)
  ·
    refine ⟨90582947828484638754439577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60388631885656425836293051 90582947828484638754439577)
    ·
      refine ⟨67937210871363479065829683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90582947828484638754439577 67937210871363479065829683)
      ·
        refine ⟨101905816307045218598744525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67937210871363479065829683 101905816307045218598744525)
        ·
          refine ⟨38214681115141956974529197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101905816307045218598744525 38214681115141956974529197)
          ·
            refine ⟨14330505418178233865448449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38214681115141956974529197 14330505418178233865448449)
            ·
              refine ⟨10747879063633675399086337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14330505418178233865448449 10747879063633675399086337)
              ·
                refine ⟨8060909297725256549314753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10747879063633675399086337 8060909297725256549314753)
                ·
                  refine ⟨6045681973293942411986065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8060909297725256549314753 6045681973293942411986065)
                  ·
                    refine ⟨4534261479970456808989549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6045681973293942411986065 4534261479970456808989549)
                    ·
                      refine ⟨1700348054988921303371081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4534261479970456808989549 1700348054988921303371081)
                      ·
                        rfl

theorem cell23_3311416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_3311416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311416 prefixEnd_3311416 := by exact prefixLift 3311416
  have htrace : WordTrace (prefixWord ++ tailWord_3311416) baseStart_3311416 baseEnd_3311416 := by
    simpa [prefixWord, tailWord_3311416, baseEnd_3311416] using wordTrace_append hprefix tailTrace_3311416
  have hstable : (prefixWord ++ tailWord_3311416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311416).length < 2 ^ (prefixWord ++ tailWord_3311416).sum := by decide
  have hdescent : baseEnd_3311416 < baseStart_3311416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311430 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_3311430 : Nat := 118140960795 + 3311430 * 2 ^ 59
def prefixEnd_3311430 : Nat := 4983230072969 + 3 ^ 40 * 3311430 * 2
def baseEnd_3311430 : Nat := 1700355243718084248596017

theorem tailTrace_3311430 : CollatzResearch.WordTrace tailWord_3311430 prefixEnd_3311430 1700355243718084248596017 := by
  unfold tailWord_3311430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774305449789441626987367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80518516262174754709063829 3774305449789441626987367)
  ·
    refine ⟨5661458174684162440481051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3774305449789441626987367 5661458174684162440481051)
    ·
      refine ⟨8492187262026243660721577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5661458174684162440481051 8492187262026243660721577)
      ·
        refine ⟨6369140446519682745541183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8492187262026243660721577 6369140446519682745541183)
        ·
          refine ⟨9553710669779524118311775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6369140446519682745541183 9553710669779524118311775)
          ·
            refine ⟨14330566004669286177467663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9553710669779524118311775 14330566004669286177467663)
            ·
              refine ⟨21495849007003929266201495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14330566004669286177467663 21495849007003929266201495)
              ·
                refine ⟨32243773510505893899302243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21495849007003929266201495 32243773510505893899302243)
                ·
                  refine ⟨48365660265758840848953365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32243773510505893899302243 48365660265758840848953365)
                  ·
                    refine ⟨2267140324957445664794689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48365660265758840848953365 2267140324957445664794689)
                    ·
                      refine ⟨1700355243718084248596017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267140324957445664794689 1700355243718084248596017)
                      ·
                        rfl

theorem cell23_3311430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_3311430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311430 prefixEnd_3311430 := by exact prefixLift 3311430
  have htrace : WordTrace (prefixWord ++ tailWord_3311430) baseStart_3311430 baseEnd_3311430 := by
    simpa [prefixWord, tailWord_3311430, baseEnd_3311430] using wordTrace_append hprefix tailTrace_3311430
  have hstable : (prefixWord ++ tailWord_3311430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311430).length < 2 ^ (prefixWord ++ tailWord_3311430).sum := by decide
  have hdescent : baseEnd_3311430 < baseStart_3311430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311449 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 3, 5]
def baseStart_3311449 : Nat := 118140960795 + 3311449 * 2 ^ 59
def prefixEnd_3311449 : Nat := 4983230072969 + 3 ^ 40 * 3311449 * 2
def baseEnd_3311449 : Nat := 566788333283506558086143

theorem tailTrace_3311449 : CollatzResearch.WordTrace tailWord_3311449 prefixEnd_3311449 566788333283506558086143 := by
  unfold tailWord_3311449
  simp only [CollatzResearch.WordTrace]
  refine ⟨120778467380193298308537401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80518978253462198872358267 120778467380193298308537401)
  ·
    refine ⟨90583850535144973731403051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120778467380193298308537401 90583850535144973731403051)
    ·
      refine ⟨135875775802717460597104577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90583850535144973731403051 135875775802717460597104577)
      ·
        refine ⟨101906831852038095447828433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135875775802717460597104577 101906831852038095447828433)
        ·
          refine ⟨76430123889028571585871325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101906831852038095447828433 76430123889028571585871325)
          ·
            refine ⟨28661296458385714344701747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76430123889028571585871325 28661296458385714344701747)
            ·
              refine ⟨42991944687578571517052621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28661296458385714344701747 42991944687578571517052621)
              ·
                refine ⟨16121979257841964318894733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42991944687578571517052621 16121979257841964318894733)
                ·
                  refine ⟨6045742221690736619585525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16121979257841964318894733 6045742221690736619585525)
                  ·
                    refine ⟨566788333283506558086143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6045742221690736619585525 566788333283506558086143)
                    ·
                      rfl

theorem cell23_3311449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_3311449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311449 prefixEnd_3311449 := by exact prefixLift 3311449
  have htrace : WordTrace (prefixWord ++ tailWord_3311449) baseStart_3311449 baseEnd_3311449 := by
    simpa [prefixWord, tailWord_3311449, baseEnd_3311449] using wordTrace_append hprefix tailTrace_3311449
  have hstable : (prefixWord ++ tailWord_3311449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311449).length < 2 ^ (prefixWord ++ tailWord_3311449).sum := by decide
  have hdescent : baseEnd_3311449 < baseStart_3311449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311509 : List Nat := [1, 3, 2, 1, 1, 3, 3, 9]
def baseStart_3311509 : Nat := 118140960795 + 3311509 * 2 ^ 59
def prefixEnd_3311509 : Nat := 4983230072969 + 3 ^ 40 * 3311509 * 2
def baseEnd_3311509 : Nat := 62977622544066275537339

theorem tailTrace_3311509 : CollatzResearch.WordTrace tailWord_3311509 prefixEnd_3311509 62977622544066275537339 := by
  unfold tailWord_3311509
  simp only [CollatzResearch.WordTrace]
  refine ⟨120780655759975928555721581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80520437173317285703814387 120780655759975928555721581)
  ·
    refine ⟨45292745909990973208395593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120780655759975928555721581 45292745909990973208395593)
    ·
      refine ⟨33969559432493229906296695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45292745909990973208395593 33969559432493229906296695)
      ·
        refine ⟨50954339148739844859445043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33969559432493229906296695 50954339148739844859445043)
        ·
          refine ⟨76431508723109767289167565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50954339148739844859445043 76431508723109767289167565)
          ·
            refine ⟨28661815771166162733437837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76431508723109767289167565 28661815771166162733437837)
            ·
              refine ⟨10748180914187311025039189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28661815771166162733437837 10748180914187311025039189)
              ·
                refine ⟨62977622544066275537339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10748180914187311025039189 62977622544066275537339)
                ·
                  rfl

theorem cell23_3311509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 9].length) (baseStart_3311509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311509 prefixEnd_3311509 := by exact prefixLift 3311509
  have htrace : WordTrace (prefixWord ++ tailWord_3311509) baseStart_3311509 baseEnd_3311509 := by
    simpa [prefixWord, tailWord_3311509, baseEnd_3311509] using wordTrace_append hprefix tailTrace_3311509
  have hstable : (prefixWord ++ tailWord_3311509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311509).length < 2 ^ (prefixWord ++ tailWord_3311509).sum := by decide
  have hdescent : baseEnd_3311509 < baseStart_3311509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311537 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 3, 2, 2]
def baseStart_3311537 : Nat := 118140960795 + 3311537 * 2 ^ 59
def prefixEnd_3311537 : Nat := 4983230072969 + 3 ^ 40 * 3311537 * 2
def baseEnd_3311537 : Nat := 1700410186148115329958025

theorem tailTrace_3311537 : CollatzResearch.WordTrace tailWord_3311537 prefixEnd_3311537 1700410186148115329958025 := by
  unfold tailWord_3311537
  simp only [CollatzResearch.WordTrace]
  refine ⟨120781677003874489337740865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80521118002582992891827243 120781677003874489337740865)
  ·
    refine ⟨90586257752905867003305649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120781677003874489337740865 90586257752905867003305649)
    ·
      refine ⟨67939693314679400252479237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90586257752905867003305649 67939693314679400252479237)
      ·
        refine ⟨12738692496502387547339857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67939693314679400252479237 12738692496502387547339857)
        ·
          refine ⟨9554019372376790660504893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12738692496502387547339857 9554019372376790660504893)
          ·
            refine ⟨3582757264641296497689335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9554019372376790660504893 3582757264641296497689335)
            ·
              refine ⟨5374135896961944746534003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582757264641296497689335 5374135896961944746534003)
              ·
                refine ⟨8061203845442917119801005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5374135896961944746534003 8061203845442917119801005)
                ·
                  refine ⟨3022951442041093919925377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8061203845442917119801005 3022951442041093919925377)
                  ·
                    refine ⟨2267213581530820439944033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3022951442041093919925377 2267213581530820439944033)
                    ·
                      refine ⟨1700410186148115329958025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267213581530820439944033 1700410186148115329958025)
                      ·
                        rfl

theorem cell23_3311537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_3311537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311537 prefixEnd_3311537 := by exact prefixLift 3311537
  have htrace : WordTrace (prefixWord ++ tailWord_3311537) baseStart_3311537 baseEnd_3311537 := by
    simpa [prefixWord, tailWord_3311537, baseEnd_3311537] using wordTrace_append hprefix tailTrace_3311537
  have hstable : (prefixWord ++ tailWord_3311537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311537).length < 2 ^ (prefixWord ++ tailWord_3311537).sum := by decide
  have hdescent : baseEnd_3311537 < baseStart_3311537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311539 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 2, 7]
def baseStart_3311539 : Nat := 118140960795 + 3311539 * 2 ^ 59
def prefixEnd_3311539 : Nat := 4983230072969 + 3 ^ 40 * 3311539 * 2
def baseEnd_3311539 : Nat := 566803737703141440711005

theorem tailTrace_3311539 : CollatzResearch.WordTrace tailWord_3311539 prefixEnd_3311539 566803737703141440711005 := by
  unfold tailWord_3311539
  simp only [CollatzResearch.WordTrace]
  refine ⟨120781749949867243679313671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80521166633244829119542447 120781749949867243679313671)
  ·
    refine ⟨181172624924800865518970507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120781749949867243679313671 181172624924800865518970507)
    ·
      refine ⟨271758937387201298278455761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181172624924800865518970507 271758937387201298278455761)
      ·
        refine ⟨203819203040400973708841821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271758937387201298278455761 203819203040400973708841821)
        ·
          refine ⟨76432201140150365140815683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203819203040400973708841821 76432201140150365140815683)
          ·
            refine ⟨114648301710225547711223525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76432201140150365140815683 114648301710225547711223525)
            ·
              refine ⟨21496556570667290195854411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114648301710225547711223525 21496556570667290195854411)
              ·
                refine ⟨32244834856000935293781617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21496556570667290195854411 32244834856000935293781617)
                ·
                  refine ⟨24183626142000701470336213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32244834856000935293781617 24183626142000701470336213)
                  ·
                    refine ⟨566803737703141440711005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24183626142000701470336213 566803737703141440711005)
                    ·
                      rfl

theorem cell23_3311539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 7].length) (baseStart_3311539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311539 prefixEnd_3311539 := by exact prefixLift 3311539
  have htrace : WordTrace (prefixWord ++ tailWord_3311539) baseStart_3311539 baseEnd_3311539 := by
    simpa [prefixWord, tailWord_3311539, baseEnd_3311539] using wordTrace_append hprefix tailTrace_3311539
  have hstable : (prefixWord ++ tailWord_3311539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311539).length < 2 ^ (prefixWord ++ tailWord_3311539).sum := by decide
  have hdescent : baseEnd_3311539 < baseStart_3311539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311559 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_3311559 : Nat := 118140960795 + 3311559 * 2 ^ 59
def prefixEnd_3311559 : Nat := 4983230072969 + 3 ^ 40 * 3311559 * 2
def baseEnd_3311559 : Nat := 1700421482722514243882923

theorem tailTrace_3311559 : CollatzResearch.WordTrace tailWord_3311559 prefixEnd_3311559 1700421482722514243882923 := by
  unfold tailWord_3311559
  simp only [CollatzResearch.WordTrace]
  refine ⟨120782479409794787095041731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80521652939863191396694487 120782479409794787095041731)
  ·
    refine ⟨181173719114692180642562597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120782479409794787095041731 181173719114692180642562597)
    ·
      refine ⟨33970072334004783870480487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181173719114692180642562597 33970072334004783870480487)
      ·
        refine ⟨50955108501007175805720731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33970072334004783870480487 50955108501007175805720731)
        ·
          refine ⟨76432662751510763708581097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50955108501007175805720731 76432662751510763708581097)
          ·
            refine ⟨57324497063633072781435823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76432662751510763708581097 57324497063633072781435823)
            ·
              refine ⟨85986745595449609172153735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57324497063633072781435823 85986745595449609172153735)
              ·
                refine ⟨128980118393174413758230603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85986745595449609172153735 128980118393174413758230603)
                ·
                  refine ⟨193470177589761620637345905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128980118393174413758230603 193470177589761620637345905)
                  ·
                    refine ⟨145102633192321215478009429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193470177589761620637345905 145102633192321215478009429)
                    ·
                      refine ⟨1700421482722514243882923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 145102633192321215478009429 1700421482722514243882923)
                      ·
                        rfl

theorem cell23_3311559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_3311559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311559 prefixEnd_3311559 := by exact prefixLift 3311559
  have htrace : WordTrace (prefixWord ++ tailWord_3311559) baseStart_3311559 baseEnd_3311559 := by
    simpa [prefixWord, tailWord_3311559, baseEnd_3311559] using wordTrace_append hprefix tailTrace_3311559
  have hstable : (prefixWord ++ tailWord_3311559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311559).length < 2 ^ (prefixWord ++ tailWord_3311559).sum := by decide
  have hdescent : baseEnd_3311559 < baseStart_3311559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311563 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 3, 3, 2]
def baseStart_3311563 : Nat := 118140960795 + 3311563 * 2 ^ 59
def prefixEnd_3311563 : Nat := 4983230072969 + 3 ^ 40 * 3311563 * 2
def baseEnd_3311563 : Nat := 1700423536645132228232905

theorem tailTrace_3311563 : CollatzResearch.WordTrace tailWord_3311563 prefixEnd_3311563 1700423536645132228232905 := by
  unfold tailWord_3311563
  simp only [CollatzResearch.WordTrace]
  refine ⟨120782625301780295778187343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80521750201186863852124895 120782625301780295778187343)
  ·
    refine ⟨181173937952670443667281015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120782625301780295778187343 181173937952670443667281015)
    ·
      refine ⟨271760906929005665500921523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181173937952670443667281015 271760906929005665500921523)
      ·
        refine ⟨407641360393508498251382285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271760906929005665500921523 407641360393508498251382285)
        ·
          refine ⟨152865510147565686844268357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407641360393508498251382285 152865510147565686844268357)
          ·
            refine ⟨28662283152668566283300317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152865510147565686844268357 28662283152668566283300317)
            ·
              refine ⟨10748356182250712356237619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28662283152668566283300317 10748356182250712356237619)
              ·
                refine ⟨16122534273376068534356429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10748356182250712356237619 16122534273376068534356429)
                ·
                  refine ⟨6045950352516025700383661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16122534273376068534356429 6045950352516025700383661)
                  ·
                    refine ⟨2267231382193509637643873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6045950352516025700383661 2267231382193509637643873)
                    ·
                      refine ⟨1700423536645132228232905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267231382193509637643873 1700423536645132228232905)
                      ·
                        rfl

theorem cell23_3311563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 3, 2].length) (baseStart_3311563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311563 prefixEnd_3311563 := by exact prefixLift 3311563
  have htrace : WordTrace (prefixWord ++ tailWord_3311563) baseStart_3311563 baseEnd_3311563 := by
    simpa [prefixWord, tailWord_3311563, baseEnd_3311563] using wordTrace_append hprefix tailTrace_3311563
  have hstable : (prefixWord ++ tailWord_3311563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311563).length < 2 ^ (prefixWord ++ tailWord_3311563).sum := by decide
  have hdescent : baseEnd_3311563 < baseStart_3311563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311569 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 3, 8]
def baseStart_3311569 : Nat := 118140960795 + 3311569 * 2 ^ 59
def prefixEnd_3311569 : Nat := 4983230072969 + 3 ^ 40 * 3311569 * 2
def baseEnd_3311569 : Nat := 566808872509686401585959

theorem tailTrace_3311569 : CollatzResearch.WordTrace tailWord_3311569 prefixEnd_3311569 566808872509686401585959 := by
  unfold tailWord_3311569
  simp only [CollatzResearch.WordTrace]
  refine ⟨120782844139758558802905761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80521896093172372535270507 120782844139758558802905761)
  ·
    refine ⟨90587133104818919102179321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120782844139758558802905761 90587133104818919102179321)
    ·
      refine ⟨67940349828614189326634491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90587133104818919102179321 67940349828614189326634491)
      ·
        refine ⟨101910524742921283989951737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67940349828614189326634491 101910524742921283989951737)
        ·
          refine ⟨76432893557190962992463803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101910524742921283989951737 76432893557190962992463803)
          ·
            refine ⟨114649340335786444488695705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76432893557190962992463803 114649340335786444488695705)
            ·
              refine ⟨85987005251839833366521779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114649340335786444488695705 85987005251839833366521779)
              ·
                refine ⟨128980507877759750049782669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85987005251839833366521779 128980507877759750049782669)
                ·
                  refine ⟨48367690454159906268668501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128980507877759750049782669 48367690454159906268668501)
                  ·
                    refine ⟨566808872509686401585959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48367690454159906268668501 566808872509686401585959)
                    ·
                      rfl

theorem cell23_3311569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_3311569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311569 prefixEnd_3311569 := by exact prefixLift 3311569
  have htrace : WordTrace (prefixWord ++ tailWord_3311569) baseStart_3311569 baseEnd_3311569 := by
    simpa [prefixWord, tailWord_3311569, baseEnd_3311569] using wordTrace_append hprefix tailTrace_3311569
  have hstable : (prefixWord ++ tailWord_3311569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311569).length < 2 ^ (prefixWord ++ tailWord_3311569).sum := by decide
  have hdescent : baseEnd_3311569 < baseStart_3311569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311570 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3311570 : Nat := 118140960795 + 3311570 * 2 ^ 59
def prefixEnd_3311570 : Nat := 4983230072969 + 3 ^ 40 * 3311570 * 2
def baseEnd_3311570 : Nat := 1700427131009713700845373

theorem tailTrace_3311570 : CollatzResearch.WordTrace tailWord_3311570 prefixEnd_3311570 1700427131009713700845373 := by
  unfold tailWord_3311570
  simp only [CollatzResearch.WordTrace]
  refine ⟨30195720153188733993423041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80521920408503290649128109 30195720153188733993423041)
  ·
    refine ⟨22646790114891550495067281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30195720153188733993423041 22646790114891550495067281)
    ·
      refine ⟨16985092586168662871300461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22646790114891550495067281 16985092586168662871300461)
      ·
        refine ⟨6369409719813248576737673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16985092586168662871300461 6369409719813248576737673)
        ·
          refine ⟨4777057289859936432553255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6369409719813248576737673 4777057289859936432553255)
          ·
            refine ⟨7165585934789904648829883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4777057289859936432553255 7165585934789904648829883)
            ·
              refine ⟨10748378902184856973244825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7165585934789904648829883 10748378902184856973244825)
              ·
                refine ⟨8061284176638642729933619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10748378902184856973244825 8061284176638642729933619)
                ·
                  refine ⟨12091926264957964094900429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8061284176638642729933619 12091926264957964094900429)
                  ·
                    refine ⟨4534472349359236535587661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12091926264957964094900429 4534472349359236535587661)
                    ·
                      refine ⟨1700427131009713700845373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4534472349359236535587661 1700427131009713700845373)
                      ·
                        rfl

theorem cell23_3311570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3311570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311570 prefixEnd_3311570 := by exact prefixLift 3311570
  have htrace : WordTrace (prefixWord ++ tailWord_3311570) baseStart_3311570 baseEnd_3311570 := by
    simpa [prefixWord, tailWord_3311570, baseEnd_3311570] using wordTrace_append hprefix tailTrace_3311570
  have hstable : (prefixWord ++ tailWord_3311570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311570).length < 2 ^ (prefixWord ++ tailWord_3311570).sum := by decide
  have hdescent : baseEnd_3311570 < baseStart_3311570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311574 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_3311574 : Nat := 118140960795 + 3311574 * 2 ^ 59
def prefixEnd_3311574 : Nat := 4983230072969 + 3 ^ 40 * 3311574 * 2
def baseEnd_3311574 : Nat := 1700429184932331685195355

theorem tailTrace_3311574 : CollatzResearch.WordTrace tailWord_3311574 prefixEnd_3311574 1700429184932331685195355 := by
  unfold tailWord_3311574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7548939156546277791052361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80522017669826963104558517 7548939156546277791052361)
  ·
    refine ⟨5661704367409708343289271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7548939156546277791052361 5661704367409708343289271)
    ·
      refine ⟨8492556551114562514933907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5661704367409708343289271 8492556551114562514933907)
      ·
        refine ⟨12738834826671843772400861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8492556551114562514933907 12738834826671843772400861)
        ·
          refine ⟨4777063060001941414650323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12738834826671843772400861 4777063060001941414650323)
          ·
            refine ⟨7165594590002912121975485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4777063060001941414650323 7165594590002912121975485)
            ·
              refine ⟨2687097971251092045740807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7165594590002912121975485 2687097971251092045740807)
              ·
                refine ⟨4030646956876638068611211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687097971251092045740807 4030646956876638068611211)
                ·
                  refine ⟨6045970435314957102916817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030646956876638068611211 6045970435314957102916817)
                  ·
                    refine ⟨4534477826486217827187613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6045970435314957102916817 4534477826486217827187613)
                    ·
                      refine ⟨1700429184932331685195355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4534477826486217827187613 1700429184932331685195355)
                      ·
                        rfl

theorem cell23_3311574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_3311574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311574 prefixEnd_3311574 := by exact prefixLift 3311574
  have htrace : WordTrace (prefixWord ++ tailWord_3311574) baseStart_3311574 baseEnd_3311574 := by
    simpa [prefixWord, tailWord_3311574, baseEnd_3311574] using wordTrace_append hprefix tailTrace_3311574
  have hstable : (prefixWord ++ tailWord_3311574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311574).length < 2 ^ (prefixWord ++ tailWord_3311574).sum := by decide
  have hdescent : baseEnd_3311574 < baseStart_3311574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311644 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_3311644 : Nat := 118140960795 + 3311644 * 2 ^ 59
def prefixEnd_3311644 : Nat := 4983230072969 + 3 ^ 40 * 3311644 * 2
def baseEnd_3311644 : Nat := 1700465128578146411320033

theorem tailTrace_3311644 : CollatzResearch.WordTrace tailWord_3311644 prefixEnd_3311644 1700465128578146411320033 := by
  unfold tailWord_3311644
  simp only [CollatzResearch.WordTrace]
  refine ⟨60392789807243423305942993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80523719742991231074590657 60392789807243423305942993)
  ·
    refine ⟨45294592355432567479457245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60392789807243423305942993 45294592355432567479457245)
    ·
      refine ⟨16985472133287212804796467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45294592355432567479457245 16985472133287212804796467)
      ·
        refine ⟨25478208199930819207194701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16985472133287212804796467 25478208199930819207194701)
        ·
          refine ⟨9554328074974057202698013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25478208199930819207194701 9554328074974057202698013)
          ·
            refine ⟨3582873028115271451011755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9554328074974057202698013 3582873028115271451011755)
            ·
              refine ⟨5374309542172907176517633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582873028115271451011755 5374309542172907176517633)
              ·
                refine ⟨4030732156629680382388225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5374309542172907176517633 4030732156629680382388225)
                ·
                  refine ⟨3023049117472260286791169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4030732156629680382388225 3023049117472260286791169)
                  ·
                    refine ⟨2267286838104195215093377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3023049117472260286791169 2267286838104195215093377)
                    ·
                      refine ⟨1700465128578146411320033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267286838104195215093377 1700465128578146411320033)
                      ·
                        rfl

theorem cell23_3311644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_3311644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311644 prefixEnd_3311644 := by exact prefixLift 3311644
  have htrace : WordTrace (prefixWord ++ tailWord_3311644) baseStart_3311644 baseEnd_3311644 := by
    simpa [prefixWord, tailWord_3311644, baseEnd_3311644] using wordTrace_append hprefix tailTrace_3311644
  have hstable : (prefixWord ++ tailWord_3311644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311644).length < 2 ^ (prefixWord ++ tailWord_3311644).sum := by decide
  have hdescent : baseEnd_3311644 < baseStart_3311644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311676 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_3311676 : Nat := 118140960795 + 3311676 * 2 ^ 59
def prefixEnd_3311676 : Nat := 4983230072969 + 3 ^ 40 * 3311676 * 2
def baseEnd_3311676 : Nat := 566827186653030095373295

theorem tailTrace_3311676 : CollatzResearch.WordTrace tailWord_3311676 prefixEnd_3311676 566827186653030095373295 := by
  unfold tailWord_3311676
  simp only [CollatzResearch.WordTrace]
  refine ⟨60393373375185458038525441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80524497833580610718033921 60393373375185458038525441)
  ·
    refine ⟨45295030031389093528894081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60393373375185458038525441 45295030031389093528894081)
    ·
      refine ⟨33971272523541820146670561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45295030031389093528894081 33971272523541820146670561)
      ·
        refine ⟨25478454392656365110002921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33971272523541820146670561 25478454392656365110002921)
        ·
          refine ⟨19108840794492273832502191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25478454392656365110002921 19108840794492273832502191)
          ·
            refine ⟨28663261191738410748753287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19108840794492273832502191 28663261191738410748753287)
            ·
              refine ⟨42994891787607616123129931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28663261191738410748753287 42994891787607616123129931)
              ·
                refine ⟨64492337681411424184694897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42994891787607616123129931 64492337681411424184694897)
                ·
                  refine ⟨48369253261058568138521173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64492337681411424184694897 48369253261058568138521173)
                  ·
                    refine ⟨566827186653030095373295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48369253261058568138521173 566827186653030095373295)
                    ·
                      rfl

theorem cell23_3311676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_3311676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311676 prefixEnd_3311676 := by exact prefixLift 3311676
  have htrace : WordTrace (prefixWord ++ tailWord_3311676) baseStart_3311676 baseEnd_3311676 := by
    simpa [prefixWord, tailWord_3311676, baseEnd_3311676] using wordTrace_append hprefix tailTrace_3311676
  have hstable : (prefixWord ++ tailWord_3311676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311676).length < 2 ^ (prefixWord ++ tailWord_3311676).sum := by decide
  have hdescent : baseEnd_3311676 < baseStart_3311676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311683 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 4, 4, 2]
def baseStart_3311683 : Nat := 118140960795 + 3311683 * 2 ^ 59
def prefixEnd_3311683 : Nat := 4983230072969 + 3 ^ 40 * 3311683 * 2
def baseEnd_3311683 : Nat := 1700485154323671758732353

theorem tailTrace_3311683 : CollatzResearch.WordTrace tailWord_3311683 prefixEnd_3311683 1700485154323671758732353 := by
  unfold tailWord_3311683
  simp only [CollatzResearch.WordTrace]
  refine ⟨120787002061345556272555703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80524668040897037515037135 120787002061345556272555703)
  ·
    refine ⟨181180503092018334408833555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120787002061345556272555703 181180503092018334408833555)
    ·
      refine ⟨271770754638027501613250333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181180503092018334408833555 271770754638027501613250333)
      ·
        refine ⟨101914032989260313104968875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271770754638027501613250333 101914032989260313104968875)
        ·
          refine ⟨152871049483890469657453313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101914032989260313104968875 152871049483890469657453313)
          ·
            refine ⟨114653287112917852243089985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152871049483890469657453313 114653287112917852243089985)
            ·
              refine ⟨85989965334688389182317489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114653287112917852243089985 85989965334688389182317489)
              ·
                refine ⟨64492474001016291886738117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85989965334688389182317489 64492474001016291886738117)
                ·
                  refine ⟨12092338875190554728763397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64492474001016291886738117 12092338875190554728763397)
                  ·
                    refine ⟨2267313539098229011643137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12092338875190554728763397 2267313539098229011643137)
                    ·
                      refine ⟨1700485154323671758732353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267313539098229011643137 1700485154323671758732353)
                      ·
                        rfl

theorem cell23_3311683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 4, 2].length) (baseStart_3311683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311683 prefixEnd_3311683 := by exact prefixLift 3311683
  have htrace : WordTrace (prefixWord ++ tailWord_3311683) baseStart_3311683 baseEnd_3311683 := by
    simpa [prefixWord, tailWord_3311683, baseEnd_3311683] using wordTrace_append hprefix tailTrace_3311683
  have hstable : (prefixWord ++ tailWord_3311683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311683).length < 2 ^ (prefixWord ++ tailWord_3311683).sum := by decide
  have hdescent : baseEnd_3311683 < baseStart_3311683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311703 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 3]
def baseStart_3311703 : Nat := 118140960795 + 3311703 * 2 ^ 59
def prefixEnd_3311703 : Nat := 4983230072969 + 3 ^ 40 * 3311703 * 2
def baseEnd_3311703 : Nat := 1700495423936761680482261

theorem tailTrace_3311703 : CollatzResearch.WordTrace tailWord_3311703 prefixEnd_3311703 1700495423936761680482261 := by
  unfold tailWord_3311703
  simp only [CollatzResearch.WordTrace]
  refine ⟨120787731521273099688283763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80525154347515399792189175 120787731521273099688283763)
  ·
    refine ⟨181181597281909649532425645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120787731521273099688283763 181181597281909649532425645)
    ·
      refine ⟨67943098980716118574659617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181181597281909649532425645 67943098980716118574659617)
      ·
        refine ⟨50957324235537088930994713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67943098980716118574659617 50957324235537088930994713)
        ·
          refine ⟨38217993176652816698246035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50957324235537088930994713 38217993176652816698246035)
          ·
            refine ⟨57326989764979225047369053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38217993176652816698246035 57326989764979225047369053)
            ·
              refine ⟨21497621161867209392763395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57326989764979225047369053 21497621161867209392763395)
              ·
                refine ⟨32246431742800814089145093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21497621161867209392763395 32246431742800814089145093)
                ·
                  refine ⟨6046205951775152641714705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32246431742800814089145093 6046205951775152641714705)
                  ·
                    refine ⟨4534654463831364481286029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6046205951775152641714705 4534654463831364481286029)
                    ·
                      refine ⟨1700495423936761680482261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4534654463831364481286029 1700495423936761680482261)
                      ·
                        rfl

theorem cell23_3311703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_3311703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311703 prefixEnd_3311703 := by exact prefixLift 3311703
  have htrace : WordTrace (prefixWord ++ tailWord_3311703) baseStart_3311703 baseEnd_3311703 := by
    simpa [prefixWord, tailWord_3311703, baseEnd_3311703] using wordTrace_append hprefix tailTrace_3311703
  have hstable : (prefixWord ++ tailWord_3311703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311703).length < 2 ^ (prefixWord ++ tailWord_3311703).sum := by decide
  have hdescent : baseEnd_3311703 < baseStart_3311703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311706 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 8]
def baseStart_3311706 : Nat := 118140960795 + 3311706 * 2 ^ 59
def prefixEnd_3311706 : Nat := 4983230072969 + 3 ^ 40 * 3311706 * 2
def baseEnd_3311706 : Nat := 188944107153191685416083

theorem tailTrace_3311706 : CollatzResearch.WordTrace tailWord_3311706 prefixEnd_3311706 188944107153191685416083 := by
  unfold tailWord_3311706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30196960235065557800160743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80525227293508154133761981 30196960235065557800160743)
  ·
    refine ⟨45295440352598336700241115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30196960235065557800160743 45295440352598336700241115)
    ·
      refine ⟨67943160528897505050361673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45295440352598336700241115 67943160528897505050361673)
      ·
        refine ⟨50957370396673128787771255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67943160528897505050361673 50957370396673128787771255)
        ·
          refine ⟨76436055595009693181656883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50957370396673128787771255 76436055595009693181656883)
          ·
            refine ⟨114654083392514539772485325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76436055595009693181656883 114654083392514539772485325)
            ·
              refine ⟨42995281272192952414681997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114654083392514539772485325 42995281272192952414681997)
              ·
                refine ⟨16123230477072357155505749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42995281272192952414681997 16123230477072357155505749)
                ·
                  refine ⟨188944107153191685416083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16123230477072357155505749 188944107153191685416083)
                  ·
                    rfl

theorem cell23_3311706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_3311706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311706 prefixEnd_3311706 := by exact prefixLift 3311706
  have htrace : WordTrace (prefixWord ++ tailWord_3311706) baseStart_3311706 baseEnd_3311706 := by
    simpa [prefixWord, tailWord_3311706, baseEnd_3311706] using wordTrace_append hprefix tailTrace_3311706
  have hstable : (prefixWord ++ tailWord_3311706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311706).length < 2 ^ (prefixWord ++ tailWord_3311706).sum := by decide
  have hdescent : baseEnd_3311706 < baseStart_3311706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311760 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 2, 3, 2]
def baseStart_3311760 : Nat := 118140960795 + 3311760 * 2 ^ 59
def prefixEnd_3311760 : Nat := 4983230072969 + 3 ^ 40 * 3311760 * 2
def baseEnd_3311760 : Nat := 1700524692334067957469499

theorem tailTrace_3311760 : CollatzResearch.WordTrace tailWord_3311760 prefixEnd_3311760 1700524692334067957469499 := by
  unfold tailWord_3311760
  simp only [CollatzResearch.WordTrace]
  refine ⟨60394905241033299211554367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80526540321377732282072489 60394905241033299211554367)
  ·
    refine ⟨90592357861549948817331551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60394905241033299211554367 90592357861549948817331551)
    ·
      refine ⟨135888536792324923225997327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90592357861549948817331551 135888536792324923225997327)
      ·
        refine ⟨203832805188487384838995991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135888536792324923225997327 203832805188487384838995991)
        ·
          refine ⟨305749207782731077258493987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203832805188487384838995991 305749207782731077258493987)
          ·
            refine ⟨458623811674096615887740981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305749207782731077258493987 458623811674096615887740981)
            ·
              refine ⟨42995982344446557739475717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 458623811674096615887740981 42995982344446557739475717)
              ·
                refine ⟨8061746689583729576151697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42995982344446557739475717 8061746689583729576151697)
                ·
                  refine ⟨6046310017187797182113773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8061746689583729576151697 6046310017187797182113773)
                  ·
                    refine ⟨2267366256445423943292665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6046310017187797182113773 2267366256445423943292665)
                    ·
                      refine ⟨1700524692334067957469499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267366256445423943292665 1700524692334067957469499)
                      ·
                        rfl

theorem cell23_3311760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 3, 2].length) (baseStart_3311760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311760 prefixEnd_3311760 := by exact prefixLift 3311760
  have htrace : WordTrace (prefixWord ++ tailWord_3311760) baseStart_3311760 baseEnd_3311760 := by
    simpa [prefixWord, tailWord_3311760, baseEnd_3311760] using wordTrace_append hprefix tailTrace_3311760
  have hstable : (prefixWord ++ tailWord_3311760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311760).length < 2 ^ (prefixWord ++ tailWord_3311760).sum := by decide
  have hdescent : baseEnd_3311760 < baseStart_3311760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311803 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 4]
def baseStart_3311803 : Nat := 118140960795 + 3311803 * 2 ^ 59
def prefixEnd_3311803 : Nat := 4983230072969 + 3 ^ 40 * 3311803 * 2
def baseEnd_3311803 : Nat := 1700546772002211289231801

theorem tailTrace_3311803 : CollatzResearch.WordTrace tailWord_3311803 prefixEnd_3311803 1700546772002211289231801 := by
  unfold tailWord_3311803
  simp only [CollatzResearch.WordTrace]
  refine ⟨120791378820910816766924063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80527585880607211177949375 120791378820910816766924063)
  ·
    refine ⟨181187068231366225150386095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120791378820910816766924063 181187068231366225150386095)
    ·
      refine ⟨271780602347049337725579143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181187068231366225150386095 271780602347049337725579143)
      ·
        refine ⟨407670903520574006588368715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271780602347049337725579143 407670903520574006588368715)
        ·
          refine ⟨611506355280861009882553073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407670903520574006588368715 611506355280861009882553073)
          ·
            refine ⟨458629766460645757411914805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611506355280861009882553073 458629766460645757411914805)
            ·
              refine ⟨42996540605685539757367013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 458629766460645757411914805 42996540605685539757367013)
              ·
                refine ⟨8061851363566038704506315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42996540605685539757367013 8061851363566038704506315)
                ·
                  refine ⟨12092777045349058056759473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8061851363566038704506315 12092777045349058056759473)
                  ·
                    refine ⟨9069582784011793542569605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12092777045349058056759473 9069582784011793542569605)
                    ·
                      refine ⟨1700546772002211289231801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9069582784011793542569605 1700546772002211289231801)
                      ·
                        rfl

theorem cell23_3311803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 4].length) (baseStart_3311803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311803 prefixEnd_3311803 := by exact prefixLift 3311803
  have htrace : WordTrace (prefixWord ++ tailWord_3311803) baseStart_3311803 baseEnd_3311803 := by
    simpa [prefixWord, tailWord_3311803, baseEnd_3311803] using wordTrace_append hprefix tailTrace_3311803
  have hstable : (prefixWord ++ tailWord_3311803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311803).length < 2 ^ (prefixWord ++ tailWord_3311803).sum := by decide
  have hdescent : baseEnd_3311803 < baseStart_3311803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311804 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 1, 5]
def baseStart_3311804 : Nat := 118140960795 + 3311804 * 2 ^ 59
def prefixEnd_3311804 : Nat := 4983230072969 + 3 ^ 40 * 3311804 * 2
def baseEnd_3311804 : Nat := 566849095160955261773099

theorem tailTrace_3311804 : CollatzResearch.WordTrace tailWord_3311804 prefixEnd_3311804 566849095160955261773099 := by
  unfold tailWord_3311804
  simp only [CollatzResearch.WordTrace]
  refine ⟨60395707646953596968855233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80527610195938129291806977 60395707646953596968855233)
  ·
    refine ⟨45296780735215197726641425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60395707646953596968855233 45296780735215197726641425)
    ·
      refine ⟨33972585551411398294981069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45296780735215197726641425 33972585551411398294981069)
      ·
        refine ⟨12739719581779274360617901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33972585551411398294981069 12739719581779274360617901)
        ·
          refine ⟨4777394843167227885231713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12739719581779274360617901 4777394843167227885231713)
          ·
            refine ⟨3583046132375420913923785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777394843167227885231713 3583046132375420913923785)
            ·
              refine ⟨2687284599281565685442839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3583046132375420913923785 2687284599281565685442839)
              ·
                refine ⟨4030926898922348528164259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687284599281565685442839 4030926898922348528164259)
                ·
                  refine ⟨6046390348383522792246389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030926898922348528164259 6046390348383522792246389)
                  ·
                    refine ⟨566849095160955261773099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6046390348383522792246389 566849095160955261773099)
                    ·
                      rfl

theorem cell23_3311804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_3311804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311804 prefixEnd_3311804 := by exact prefixLift 3311804
  have htrace : WordTrace (prefixWord ++ tailWord_3311804) baseStart_3311804 baseEnd_3311804 := by
    simpa [prefixWord, tailWord_3311804, baseEnd_3311804] using wordTrace_append hprefix tailTrace_3311804
  have hstable : (prefixWord ++ tailWord_3311804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311804).length < 2 ^ (prefixWord ++ tailWord_3311804).sum := by decide
  have hdescent : baseEnd_3311804 < baseStart_3311804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311837 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3311837 : Nat := 118140960795 + 3311837 * 2 ^ 59
def prefixEnd_3311837 : Nat := 4983230072969 + 3 ^ 40 * 3311837 * 2
def baseEnd_3311837 : Nat := 1700564230344464156206645

theorem tailTrace_3311837 : CollatzResearch.WordTrace tailWord_3311837 prefixEnd_3311837 1700564230344464156206645 := by
  unfold tailWord_3311837
  simp only [CollatzResearch.WordTrace]
  refine ⟨120792618902787640573661765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80528412601858427049107843 120792618902787640573661765)
  ·
    refine ⟨22648616044272682607561581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120792618902787640573661765 22648616044272682607561581)
    ·
      refine ⟨8493231016602255977835593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22648616044272682607561581 8493231016602255977835593)
      ·
        refine ⟨6369923262451691983376695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8493231016602255977835593 6369923262451691983376695)
        ·
          refine ⟨9554884893677537975065043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6369923262451691983376695 9554884893677537975065043)
          ·
            refine ⟨14332327340516306962597565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9554884893677537975065043 14332327340516306962597565)
            ·
              refine ⟨5374622752693615110974087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14332327340516306962597565 5374622752693615110974087)
              ·
                refine ⟨8061934129040422666461131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5374622752693615110974087 8061934129040422666461131)
                ·
                  refine ⟨12092901193560633999691697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8061934129040422666461131 12092901193560633999691697)
                  ·
                    refine ⟨9069675895170475499768773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12092901193560633999691697 9069675895170475499768773)
                    ·
                      refine ⟨1700564230344464156206645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9069675895170475499768773 1700564230344464156206645)
                      ·
                        rfl

theorem cell23_3311837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3311837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311837 prefixEnd_3311837 := by exact prefixLift 3311837
  have htrace : WordTrace (prefixWord ++ tailWord_3311837) baseStart_3311837 baseEnd_3311837 := by
    simpa [prefixWord, tailWord_3311837, baseEnd_3311837] using wordTrace_append hprefix tailTrace_3311837
  have hstable : (prefixWord ++ tailWord_3311837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311837).length < 2 ^ (prefixWord ++ tailWord_3311837).sum := by decide
  have hdescent : baseEnd_3311837 < baseStart_3311837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311847 : List Nat := [1, 1, 5, 3, 1, 3, 2, 7]
def baseStart_3311847 : Nat := 118140960795 + 3311847 * 2 ^ 59
def prefixEnd_3311847 : Nat := 4983230072969 + 3 ^ 40 * 3311847 * 2
def baseEnd_3311847 : Nat := 62984050561148485817837

theorem tailTrace_3311847 : CollatzResearch.WordTrace tailWord_3311847 prefixEnd_3311847 62984050561148485817837 := by
  unfold tailWord_3311847
  simp only [CollatzResearch.WordTrace]
  refine ⟨120792983632751412281525795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80528655755167608187683863 120792983632751412281525795)
  ·
    refine ⟨181189475449127118422288693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120792983632751412281525795 181189475449127118422288693)
    ·
      refine ⟨16986513323355667352089565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181189475449127118422288693 16986513323355667352089565)
      ·
        refine ⟨6369942496258375257033587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16986513323355667352089565 6369942496258375257033587)
        ·
          refine ⟨9554913744387562885550381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6369942496258375257033587 9554913744387562885550381)
          ·
            refine ⟨3583092654145336082081393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9554913744387562885550381 3583092654145336082081393)
            ·
              refine ⟨2687319490609002061561045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3583092654145336082081393 2687319490609002061561045)
              ·
                refine ⟨62984050561148485817837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2687319490609002061561045 62984050561148485817837)
                ·
                  rfl

theorem cell23_3311847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 7].length) (baseStart_3311847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311847 prefixEnd_3311847 := by exact prefixLift 3311847
  have htrace : WordTrace (prefixWord ++ tailWord_3311847) baseStart_3311847 baseEnd_3311847 := by
    simpa [prefixWord, tailWord_3311847, baseEnd_3311847] using wordTrace_append hprefix tailTrace_3311847
  have hstable : (prefixWord ++ tailWord_3311847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311847).length < 2 ^ (prefixWord ++ tailWord_3311847).sum := by decide
  have hdescent : baseEnd_3311847 < baseStart_3311847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311858 : List Nat := [3, 2, 1, 3, 2, 3, 1, 3, 1, 2, 2]
def baseStart_3311858 : Nat := 118140960795 + 3311858 * 2 ^ 59
def prefixEnd_3311858 : Nat := 4983230072969 + 3 ^ 40 * 3311858 * 2
def baseEnd_3311858 : Nat := 1700575013438208574044049

theorem tailTrace_3311858 : CollatzResearch.WordTrace tailWord_3311858 prefixEnd_3311858 1700575013438208574044049 := by
  unfold tailWord_3311858
  simp only [CollatzResearch.WordTrace]
  refine ⟨30198346208927890290044057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80528923223807707440117485 30198346208927890290044057)
  ·
    refine ⟨22648759656695917717533043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30198346208927890290044057 22648759656695917717533043)
    ·
      refine ⟨33973139485043876576299565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22648759656695917717533043 33973139485043876576299565)
      ·
        refine ⟨12739927306891453716112337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33973139485043876576299565 12739927306891453716112337)
        ·
          refine ⟨9554945480168590287084253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12739927306891453716112337 9554945480168590287084253)
          ·
            refine ⟨3583104555063221357656595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9554945480168590287084253 3583104555063221357656595)
            ·
              refine ⟨5374656832594832036484893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583104555063221357656595 5374656832594832036484893)
              ·
                refine ⟨2015496312223062013681835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5374656832594832036484893 2015496312223062013681835)
                ·
                  refine ⟨3023244468334593020522753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015496312223062013681835 3023244468334593020522753)
                  ·
                    refine ⟨2267433351250944765392065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3023244468334593020522753 2267433351250944765392065)
                    ·
                      refine ⟨1700575013438208574044049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267433351250944765392065 1700575013438208574044049)
                      ·
                        rfl

theorem cell23_3311858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_3311858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311858 prefixEnd_3311858 := by exact prefixLift 3311858
  have htrace : WordTrace (prefixWord ++ tailWord_3311858) baseStart_3311858 baseEnd_3311858 := by
    simpa [prefixWord, tailWord_3311858, baseEnd_3311858] using wordTrace_append hprefix tailTrace_3311858
  have hstable : (prefixWord ++ tailWord_3311858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311858).length < 2 ^ (prefixWord ++ tailWord_3311858).sum := by decide
  have hdescent : baseEnd_3311858 < baseStart_3311858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311870 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3311870 : Nat := 118140960795 + 3311870 * 2 ^ 59
def prefixEnd_3311870 : Nat := 4983230072969 + 3 ^ 40 * 3311870 * 2
def baseEnd_3311870 : Nat := 1700581175206062527093993

theorem tailTrace_3311870 : CollatzResearch.WordTrace tailWord_3311870 prefixEnd_3311870 1700581175206062527093993 := by
  unfold tailWord_3311870
  simp only [CollatzResearch.WordTrace]
  refine ⟨15099227813958510901201633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80529215007778724806408709 15099227813958510901201633)
  ·
    refine ⟨11324420860468883175901225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15099227813958510901201633 11324420860468883175901225)
    ·
      refine ⟨8493315645351662381925919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11324420860468883175901225 8493315645351662381925919)
      ·
        refine ⟨12739973468027493572888879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8493315645351662381925919 12739973468027493572888879)
        ·
          refine ⟨19109960202041240359333319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12739973468027493572888879 19109960202041240359333319)
          ·
            refine ⟨28664940303061860538999979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19109960202041240359333319 28664940303061860538999979)
            ·
              refine ⟨42997410454592790808499969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28664940303061860538999979 42997410454592790808499969)
              ·
                refine ⟨32248057840944593106374977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42997410454592790808499969 32248057840944593106374977)
                ·
                  refine ⟨24186043380708444829781233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32248057840944593106374977 24186043380708444829781233)
                  ·
                    refine ⟨18139532535531333622335925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24186043380708444829781233 18139532535531333622335925)
                    ·
                      refine ⟨1700581175206062527093993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18139532535531333622335925 1700581175206062527093993)
                      ·
                        rfl

theorem cell23_3311870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3311870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311870 prefixEnd_3311870 := by exact prefixLift 3311870
  have htrace : WordTrace (prefixWord ++ tailWord_3311870) baseStart_3311870 baseEnd_3311870 := by
    simpa [prefixWord, tailWord_3311870, baseEnd_3311870] using wordTrace_append hprefix tailTrace_3311870
  have hstable : (prefixWord ++ tailWord_3311870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311870).length < 2 ^ (prefixWord ++ tailWord_3311870).sum := by decide
  have hdescent : baseEnd_3311870 < baseStart_3311870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311874 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_3311874 : Nat := 118140960795 + 3311874 * 2 ^ 59
def prefixEnd_3311874 : Nat := 4983230072969 + 3 ^ 40 * 3311874 * 2
def baseEnd_3311874 : Nat := 1700583229128680511443975

theorem tailTrace_3311874 : CollatzResearch.WordTrace tailWord_3311874 prefixEnd_3311874 1700583229128680511443975 := by
  unfold tailWord_3311874
  simp only [CollatzResearch.WordTrace]
  refine ⟨30198492100913398973189669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80529312269102397261839117 30198492100913398973189669)
  ·
    refine ⟨5662217268921262307473063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30198492100913398973189669 5662217268921262307473063)
    ·
      refine ⟨8493325903381893461209595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5662217268921262307473063 8493325903381893461209595)
      ·
        refine ⟨12739988855072840191814393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8493325903381893461209595 12739988855072840191814393)
        ·
          refine ⟨9554991641304630143860795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12739988855072840191814393 9554991641304630143860795)
          ·
            refine ⟨14332487461956945215791193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9554991641304630143860795 14332487461956945215791193)
            ·
              refine ⟨10749365596467708911843395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14332487461956945215791193 10749365596467708911843395)
              ·
                refine ⟨16124048394701563367765093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10749365596467708911843395 16124048394701563367765093)
                ·
                  refine ⟨3023259074006543131455955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16124048394701563367765093 3023259074006543131455955)
                  ·
                    refine ⟨4534888611009814697183933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3023259074006543131455955 4534888611009814697183933)
                    ·
                      refine ⟨1700583229128680511443975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4534888611009814697183933 1700583229128680511443975)
                      ·
                        rfl

theorem cell23_3311874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_3311874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311874 prefixEnd_3311874 := by exact prefixLift 3311874
  have htrace : WordTrace (prefixWord ++ tailWord_3311874) baseStart_3311874 baseEnd_3311874 := by
    simpa [prefixWord, tailWord_3311874, baseEnd_3311874] using wordTrace_append hprefix tailTrace_3311874
  have hstable : (prefixWord ++ tailWord_3311874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311874).length < 2 ^ (prefixWord ++ tailWord_3311874).sum := by decide
  have hdescent : baseEnd_3311874 < baseStart_3311874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311883 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 5]
def baseStart_3311883 : Nat := 118140960795 + 3311883 * 2 ^ 59
def prefixEnd_3311883 : Nat := 4983230072969 + 3 ^ 40 * 3311883 * 2
def baseEnd_3311883 : Nat := 1700587850454570976231433

theorem tailTrace_3311883 : CollatzResearch.WordTrace tailWord_3311883 prefixEnd_3311883 1700587850454570976231433 := by
  unfold tailWord_3311883
  simp only [CollatzResearch.WordTrace]
  refine ⟨120794296660620990429836303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80529531107080660286557535 120794296660620990429836303)
  ·
    refine ⟨181191444990931485644754455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120794296660620990429836303 181191444990931485644754455)
    ·
      refine ⟨271787167486397228467131683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181191444990931485644754455 271787167486397228467131683)
      ·
        refine ⟨407680751229595842700697525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271787167486397228467131683 407680751229595842700697525)
        ·
          refine ⟨38220070427774610253190393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 407680751229595842700697525 38220070427774610253190393)
          ·
            refine ⟨28665052820830957689892795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38220070427774610253190393 28665052820830957689892795)
            ·
              refine ⟨42997579231246436534839193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28665052820830957689892795 42997579231246436534839193)
              ·
                refine ⟨32248184423434827401129395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42997579231246436534839193 32248184423434827401129395)
                ·
                  refine ⟨48372276635152241101694093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32248184423434827401129395 48372276635152241101694093)
                  ·
                    refine ⟨18139603738182090413135285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48372276635152241101694093 18139603738182090413135285)
                    ·
                      refine ⟨1700587850454570976231433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18139603738182090413135285 1700587850454570976231433)
                      ·
                        rfl

theorem cell23_3311883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_3311883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311883 prefixEnd_3311883 := by exact prefixLift 3311883
  have htrace : WordTrace (prefixWord ++ tailWord_3311883) baseStart_3311883 baseEnd_3311883 := by
    simpa [prefixWord, tailWord_3311883, baseEnd_3311883] using wordTrace_append hprefix tailTrace_3311883
  have hstable : (prefixWord ++ tailWord_3311883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311883).length < 2 ^ (prefixWord ++ tailWord_3311883).sum := by decide
  have hdescent : baseEnd_3311883 < baseStart_3311883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311997 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_3311997 : Nat := 118140960795 + 3311997 * 2 ^ 59
def prefixEnd_3311997 : Nat := 4983230072969 + 3 ^ 40 * 3311997 * 2
def baseEnd_3311997 : Nat := 566882129083061176735303

theorem tailTrace_3311997 : CollatzResearch.WordTrace tailWord_3311997 prefixEnd_3311997 566882129083061176735303 := by
  unfold tailWord_3311997
  simp only [CollatzResearch.WordTrace]
  refine ⟨120798454582207987899486245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80532303054805325266324163 120798454582207987899486245)
  ·
    refine ⟨22649710234163997731153671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120798454582207987899486245 22649710234163997731153671)
    ·
      refine ⟨33974565351245996596730507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22649710234163997731153671 33974565351245996596730507)
      ·
        refine ⟨50961848026868994895095761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33974565351245996596730507 50961848026868994895095761)
        ·
          refine ⟨38221386020151746171321821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50961848026868994895095761 38221386020151746171321821)
          ·
            refine ⟨14333019757556904814245683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38221386020151746171321821 14333019757556904814245683)
            ·
              refine ⟨21499529636335357221368525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14333019757556904814245683 21499529636335357221368525)
              ·
                refine ⟨8062323613625758958013197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21499529636335357221368525 8062323613625758958013197)
                ·
                  refine ⟨3023371355109659609254949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8062323613625758958013197 3023371355109659609254949)
                  ·
                    refine ⟨566882129083061176735303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3023371355109659609254949 566882129083061176735303)
                    ·
                      rfl

theorem cell23_3311997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_3311997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311997 prefixEnd_3311997 := by exact prefixLift 3311997
  have htrace : WordTrace (prefixWord ++ tailWord_3311997) baseStart_3311997 baseEnd_3311997 := by
    simpa [prefixWord, tailWord_3311997, baseEnd_3311997] using wordTrace_append hprefix tailTrace_3311997
  have hstable : (prefixWord ++ tailWord_3311997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311997).length < 2 ^ (prefixWord ++ tailWord_3311997).sum := by decide
  have hdescent : baseEnd_3311997 < baseStart_3311997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312014 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_3312014 : Nat := 118140960795 + 3312014 * 2 ^ 59
def prefixEnd_3312014 : Nat := 4983230072969 + 3 ^ 40 * 3312014 * 2
def baseEnd_3312014 : Nat := 566885038806769987897777

theorem tailTrace_3312014 : CollatzResearch.WordTrace tailWord_3312014 prefixEnd_3312014 566885038806769987897777 := by
  unfold tailWord_3312014
  simp only [CollatzResearch.WordTrace]
  refine ⟨15099884327893299975356887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80532716415430933201903397 15099884327893299975356887)
  ·
    refine ⟨22649826491839949963035331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15099884327893299975356887 22649826491839949963035331)
    ·
      refine ⟨33974739737759924944552997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22649826491839949963035331 33974739737759924944552997)
      ·
        refine ⟨6370263700829985927103687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33974739737759924944552997 6370263700829985927103687)
        ·
          refine ⟨9555395551244978890655531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6370263700829985927103687 9555395551244978890655531)
          ·
            refine ⟨14333093326867468335983297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9555395551244978890655531 14333093326867468335983297)
            ·
              refine ⟨10749819995150601251987473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14333093326867468335983297 10749819995150601251987473)
              ·
                refine ⟨8062364996362950938990605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10749819995150601251987473 8062364996362950938990605)
                ·
                  refine ⟨3023386873636106602121477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8062364996362950938990605 3023386873636106602121477)
                  ·
                    refine ⟨566885038806769987897777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3023386873636106602121477 566885038806769987897777)
                    ·
                      rfl

theorem cell23_3312014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_3312014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312014 prefixEnd_3312014 := by exact prefixLift 3312014
  have htrace : WordTrace (prefixWord ++ tailWord_3312014) baseStart_3312014 baseEnd_3312014 := by
    simpa [prefixWord, tailWord_3312014, baseEnd_3312014] using wordTrace_append hprefix tailTrace_3312014
  have hstable : (prefixWord ++ tailWord_3312014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312014).length < 2 ^ (prefixWord ++ tailWord_3312014).sum := by decide
  have hdescent : baseEnd_3312014 < baseStart_3312014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312022 : List Nat := [5, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_3312022 : Nat := 118140960795 + 3312022 * 2 ^ 59
def prefixEnd_3312022 : Nat := 4983230072969 + 3 ^ 40 * 3312022 * 2
def baseEnd_3312022 : Nat := 188962136029505103599255

theorem tailTrace_3312022 : CollatzResearch.WordTrace tailWord_3312022 prefixEnd_3312022 188962136029505103599255 := by
  unfold tailWord_3312022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7549960400444838573071645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80532910938078278112764213 7549960400444838573071645)
  ·
    refine ⟨2831235150166814464901867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7549960400444838573071645 2831235150166814464901867)
    ·
      refine ⟨4246852725250221697352801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2831235150166814464901867 4246852725250221697352801)
      ·
        refine ⟨3185139543937666273014601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4246852725250221697352801 3185139543937666273014601)
        ·
          refine ⟨2388854657953249704760951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3185139543937666273014601 2388854657953249704760951)
          ·
            refine ⟨3583281986929874557141427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388854657953249704760951 3583281986929874557141427)
            ·
              refine ⟨5374922980394811835712141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583281986929874557141427 5374922980394811835712141)
              ·
                refine ⟨2015596117648054438392053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5374922980394811835712141 2015596117648054438392053)
                ·
                  refine ⟨188962136029505103599255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2015596117648054438392053 188962136029505103599255)
                  ·
                    rfl

theorem cell23_3312022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_3312022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312022 prefixEnd_3312022 := by exact prefixLift 3312022
  have htrace : WordTrace (prefixWord ++ tailWord_3312022) baseStart_3312022 baseEnd_3312022 := by
    simpa [prefixWord, tailWord_3312022, baseEnd_3312022] using wordTrace_append hprefix tailTrace_3312022
  have hstable : (prefixWord ++ tailWord_3312022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312022).length < 2 ^ (prefixWord ++ tailWord_3312022).sum := by decide
  have hdescent : baseEnd_3312022 < baseStart_3312022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312104 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 2, 4]
def baseStart_3312104 : Nat := 118140960795 + 3312104 * 2 ^ 59
def prefixEnd_3312104 : Nat := 4983230072969 + 3 ^ 40 * 3312104 * 2
def baseEnd_3312104 : Nat := 566900443226404870522639

theorem tailTrace_3312104 : CollatzResearch.WordTrace tailWord_3312104 prefixEnd_3312104 566900443226404870522639 := by
  unfold tailWord_3312104
  simp only [CollatzResearch.WordTrace]
  refine ⟨60401178596410172586815683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80534904795213563449087577 60401178596410172586815683)
  ·
    refine ⟨90601767894615258880223525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60401178596410172586815683 90601767894615258880223525)
    ·
      refine ⟨16987831480240361040041911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90601767894615258880223525 16987831480240361040041911)
      ·
        refine ⟨25481747220360541560062867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16987831480240361040041911 25481747220360541560062867)
        ·
          refine ⟨38222620830540812340094301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25481747220360541560062867 38222620830540812340094301)
          ·
            refine ⟨14333482811452804627535363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38222620830540812340094301 14333482811452804627535363)
            ·
              refine ⟨21500224217179206941303045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14333482811452804627535363 21500224217179206941303045)
              ·
                refine ⟨4031292040721101301494321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21500224217179206941303045 4031292040721101301494321)
                ·
                  refine ⟨3023469030540825976120741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4031292040721101301494321 3023469030540825976120741)
                  ·
                    refine ⟨566900443226404870522639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3023469030540825976120741 566900443226404870522639)
                    ·
                      rfl

theorem cell23_3312104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_3312104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312104 prefixEnd_3312104 := by exact prefixLift 3312104
  have htrace : WordTrace (prefixWord ++ tailWord_3312104) baseStart_3312104 baseEnd_3312104 := by
    simpa [prefixWord, tailWord_3312104, baseEnd_3312104] using wordTrace_append hprefix tailTrace_3312104
  have hstable : (prefixWord ++ tailWord_3312104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312104).length < 2 ^ (prefixWord ++ tailWord_3312104).sum := by decide
  have hdescent : baseEnd_3312104 < baseStart_3312104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312148 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3312148 : Nat := 118140960795 + 3312148 * 2 ^ 59
def prefixEnd_3312148 : Nat := 4983230072969 + 3 ^ 40 * 3312148 * 2
def baseEnd_3312148 : Nat := 1700723922828012439417715

theorem tailTrace_3312148 : CollatzResearch.WordTrace tailWord_3312148 prefixEnd_3312148 1700723922828012439417715 := by
  unfold tailWord_3312148
  simp only [CollatzResearch.WordTrace]
  refine ⟨60401981002330470344116549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80535974669773960458822065 60401981002330470344116549)
  ·
    refine ⟨11325371437936963189521853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60401981002330470344116549 11325371437936963189521853)
    ·
      refine ⟨4247014289226361196070695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11325371437936963189521853 4247014289226361196070695)
      ·
        refine ⟨6370521433839541794106043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4247014289226361196070695 6370521433839541794106043)
        ·
          refine ⟨9555782150759312691159065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6370521433839541794106043 9555782150759312691159065)
          ·
            refine ⟨7166836613069484518369299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9555782150759312691159065 7166836613069484518369299)
            ·
              refine ⟨10750254919604226777553949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7166836613069484518369299 10750254919604226777553949)
              ·
                refine ⟨4031345594851585041582731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10750254919604226777553949 4031345594851585041582731)
                ·
                  refine ⟨6047018392277377562374097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031345594851585041582731 6047018392277377562374097)
                  ·
                    refine ⟨4535263794208033171780573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6047018392277377562374097 4535263794208033171780573)
                    ·
                      refine ⟨1700723922828012439417715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4535263794208033171780573 1700723922828012439417715)
                      ·
                        rfl

theorem cell23_3312148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3312148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312148 prefixEnd_3312148 := by exact prefixLift 3312148
  have htrace : WordTrace (prefixWord ++ tailWord_3312148) baseStart_3312148 baseEnd_3312148 := by
    simpa [prefixWord, tailWord_3312148, baseEnd_3312148] using wordTrace_append hprefix tailTrace_3312148
  have hstable : (prefixWord ++ tailWord_3312148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312148).length < 2 ^ (prefixWord ++ tailWord_3312148).sum := by decide
  have hdescent : baseEnd_3312148 < baseStart_3312148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312177 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 2, 6]
def baseStart_3312177 : Nat := 118140960795 + 3312177 * 2 ^ 59
def prefixEnd_3312177 : Nat := 4983230072969 + 3 ^ 40 * 3312177 * 2
def baseEnd_3312177 : Nat := 566912937922330941985027

theorem tailTrace_3312177 : CollatzResearch.WordTrace tailWord_3312177 prefixEnd_3312177 566912937922330941985027 := by
  unfold tailWord_3312177
  simp only [CollatzResearch.WordTrace]
  refine ⟨120805019721555878641038785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80536679814370585760692523 120805019721555878641038785)
  ·
    refine ⟨90603764791166908980779089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120805019721555878641038785 90603764791166908980779089)
    ·
      refine ⟨67952823593375181735584317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90603764791166908980779089 67952823593375181735584317)
      ·
        refine ⟨25482308847515693150844119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67952823593375181735584317 25482308847515693150844119)
        ·
          refine ⟨38223463271273539726266179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25482308847515693150844119 38223463271273539726266179)
          ·
            refine ⟨57335194906910309589399269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38223463271273539726266179 57335194906910309589399269)
            ·
              refine ⟨10750349045045683048012363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57335194906910309589399269 10750349045045683048012363)
              ·
                refine ⟨16125523567568524572018545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10750349045045683048012363 16125523567568524572018545)
                ·
                  refine ⟨12094142675676393429013909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16125523567568524572018545 12094142675676393429013909)
                  ·
                    refine ⟨566912937922330941985027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12094142675676393429013909 566912937922330941985027)
                    ·
                      rfl

theorem cell23_3312177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_3312177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312177 prefixEnd_3312177 := by exact prefixLift 3312177
  have htrace : WordTrace (prefixWord ++ tailWord_3312177) baseStart_3312177 baseEnd_3312177 := by
    simpa [prefixWord, tailWord_3312177, baseEnd_3312177] using wordTrace_append hprefix tailTrace_3312177
  have hstable : (prefixWord ++ tailWord_3312177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312177).length < 2 ^ (prefixWord ++ tailWord_3312177).sum := by decide
  have hdescent : baseEnd_3312177 < baseStart_3312177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312188 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 1, 3, 2]
def baseStart_3312188 : Nat := 118140960795 + 3312188 * 2 ^ 59
def prefixEnd_3312188 : Nat := 4983230072969 + 3 ^ 40 * 3312188 * 2
def baseEnd_3312188 : Nat := 1700744462054192282917531

theorem tailTrace_3312188 : CollatzResearch.WordTrace tailWord_3312188 prefixEnd_3312188 1700744462054192282917531 := by
  unfold tailWord_3312188
  simp only [CollatzResearch.WordTrace]
  refine ⟨60402710462258013759844609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80536947283010685013126145 60402710462258013759844609)
  ·
    refine ⟨45302032846693510319883457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60402710462258013759844609 45302032846693510319883457)
    ·
      refine ⟨33976524635020132739912593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45302032846693510319883457 33976524635020132739912593)
      ·
        refine ⟨25482393476265099554934445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33976524635020132739912593 25482393476265099554934445)
        ·
          refine ⟨9555897553599412333100417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25482393476265099554934445 9555897553599412333100417)
          ·
            refine ⟨7166923165199559249825313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9555897553599412333100417 7166923165199559249825313)
            ·
              refine ⟨5375192373899669437368985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7166923165199559249825313 5375192373899669437368985)
              ·
                refine ⟨4031394280424752078026739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5375192373899669437368985 4031394280424752078026739)
                ·
                  refine ⟨6047091420637128117040109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031394280424752078026739 6047091420637128117040109)
                  ·
                    refine ⟨2267659282738923043890041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6047091420637128117040109 2267659282738923043890041)
                    ·
                      refine ⟨1700744462054192282917531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267659282738923043890041 1700744462054192282917531)
                      ·
                        rfl

theorem cell23_3312188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_3312188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312188 prefixEnd_3312188 := by exact prefixLift 3312188
  have htrace : WordTrace (prefixWord ++ tailWord_3312188) baseStart_3312188 baseEnd_3312188 := by
    simpa [prefixWord, tailWord_3312188, baseEnd_3312188] using wordTrace_append hprefix tailTrace_3312188
  have hstable : (prefixWord ++ tailWord_3312188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312188).length < 2 ^ (prefixWord ++ tailWord_3312188).sum := by decide
  have hdescent : baseEnd_3312188 < baseStart_3312188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312196 : List Nat := [2, 3, 5, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_3312196 : Nat := 118140960795 + 3312196 * 2 ^ 59
def prefixEnd_3312196 : Nat := 4983230072969 + 3 ^ 40 * 3312196 * 2
def baseEnd_3312196 : Nat := 1700748569899428251617495

theorem tailTrace_3312196 : CollatzResearch.WordTrace tailWord_3312196 prefixEnd_3312196 1700748569899428251617495 := by
  unfold tailWord_3312196
  simp only [CollatzResearch.WordTrace]
  refine ⟨60402856354243522442990221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80537141805658029923986961 60402856354243522442990221)
  ·
    refine ⟨22651071132841320916121333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60402856354243522442990221 22651071132841320916121333)
    ·
      refine ⟨2123537918703873835886375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22651071132841320916121333 2123537918703873835886375)
      ·
        refine ⟨3185306878055810753829563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123537918703873835886375 3185306878055810753829563)
        ·
          refine ⟨4777960317083716130744345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185306878055810753829563 4777960317083716130744345)
          ·
            refine ⟨3583470237812787098058259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777960317083716130744345 3583470237812787098058259)
            ·
              refine ⟨5375205356719180647087389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583470237812787098058259 5375205356719180647087389)
              ·
                refine ⟨2015702008769692742657771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5375205356719180647087389 2015702008769692742657771)
                ·
                  refine ⟨3023553013154539113986657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015702008769692742657771 3023553013154539113986657)
                  ·
                    refine ⟨2267664759865904335489993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3023553013154539113986657 2267664759865904335489993)
                    ·
                      refine ⟨1700748569899428251617495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267664759865904335489993 1700748569899428251617495)
                      ·
                        rfl

theorem cell23_3312196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_3312196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312196 prefixEnd_3312196 := by exact prefixLift 3312196
  have htrace : WordTrace (prefixWord ++ tailWord_3312196) baseStart_3312196 baseEnd_3312196 := by
    simpa [prefixWord, tailWord_3312196, baseEnd_3312196] using wordTrace_append hprefix tailTrace_3312196
  have hstable : (prefixWord ++ tailWord_3312196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312196).length < 2 ^ (prefixWord ++ tailWord_3312196).sum := by decide
  have hdescent : baseEnd_3312196 < baseStart_3312196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312224 : List Nat := [2, 1, 1, 3, 2, 1, 2, 6, 5]
def baseStart_3312224 : Nat := 118140960795 + 3312224 * 2 ^ 59
def prefixEnd_3312224 : Nat := 4983230072969 + 3 ^ 40 * 3312224 * 2
def baseEnd_3312224 : Nat := 188973660817528238007485

theorem tailTrace_3312224 : CollatzResearch.WordTrace tailWord_3312224 prefixEnd_3312224 188973660817528238007485 := by
  unfold tailWord_3312224
  simp only [CollatzResearch.WordTrace]
  refine ⟨60403366976192802833999863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80537822634923737111999817 60403366976192802833999863)
  ·
    refine ⟨90605050464289204250999795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60403366976192802833999863 90605050464289204250999795)
    ·
      refine ⟨135907575696433806376499693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90605050464289204250999795 135907575696433806376499693)
      ·
        refine ⟨50965340886162677391187385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135907575696433806376499693 50965340886162677391187385)
        ·
          refine ⟨38224005664622008043390539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50965340886162677391187385 38224005664622008043390539)
          ·
            refine ⟨57336008496933012065085809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38224005664622008043390539 57336008496933012065085809)
            ·
              refine ⟨43002006372699759048814357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57336008496933012065085809 43002006372699759048814357)
              ·
                refine ⟨2015719048720301205413173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43002006372699759048814357 2015719048720301205413173)
                ·
                  refine ⟨188973660817528238007485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2015719048720301205413173 188973660817528238007485)
                  ·
                    rfl

theorem cell23_3312224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 5].length) (baseStart_3312224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312224 prefixEnd_3312224 := by exact prefixLift 3312224
  have htrace : WordTrace (prefixWord ++ tailWord_3312224) baseStart_3312224 baseEnd_3312224 := by
    simpa [prefixWord, tailWord_3312224, baseEnd_3312224] using wordTrace_append hprefix tailTrace_3312224
  have hstable : (prefixWord ++ tailWord_3312224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312224).length < 2 ^ (prefixWord ++ tailWord_3312224).sum := by decide
  have hdescent : baseEnd_3312224 < baseStart_3312224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312234 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_3312234 : Nat := 118140960795 + 3312234 * 2 ^ 59
def prefixEnd_3312234 : Nat := 4983230072969 + 3 ^ 40 * 3312234 * 2
def baseEnd_3312234 : Nat := 1700768082164299102942319

theorem tailTrace_3312234 : CollatzResearch.WordTrace tailWord_3312234 prefixEnd_3312234 1700768082164299102942319 := by
  unfold tailWord_3312234
  simp only [CollatzResearch.WordTrace]
  refine ⟨30201774670587344343965939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80538065788232918250575837 30201774670587344343965939)
  ·
    refine ⟨45302662005881016515948909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30201774670587344343965939 45302662005881016515948909)
    ·
      refine ⟨16988498252205381193480841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45302662005881016515948909 16988498252205381193480841)
      ·
        refine ⟨12741373689154035895110631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16988498252205381193480841 12741373689154035895110631)
        ·
          refine ⟨19112060533731053842665947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12741373689154035895110631 19112060533731053842665947)
          ·
            refine ⟨28668090800596580763998921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19112060533731053842665947 28668090800596580763998921)
            ·
              refine ⟨21501068100447435572999191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28668090800596580763998921 21501068100447435572999191)
              ·
                refine ⟨32251602150671153359498787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21501068100447435572999191 32251602150671153359498787)
                ·
                  refine ⟨48377403226006730039248181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32251602150671153359498787 48377403226006730039248181)
                  ·
                    refine ⟨4535381552438130941179517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48377403226006730039248181 4535381552438130941179517)
                    ·
                      refine ⟨1700768082164299102942319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4535381552438130941179517 1700768082164299102942319)
                      ·
                        rfl

theorem cell23_3312234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_3312234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312234 prefixEnd_3312234 := by exact prefixLift 3312234
  have htrace : WordTrace (prefixWord ++ tailWord_3312234) baseStart_3312234 baseEnd_3312234 := by
    simpa [prefixWord, tailWord_3312234, baseEnd_3312234] using wordTrace_append hprefix tailTrace_3312234
  have hstable : (prefixWord ++ tailWord_3312234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312234).length < 2 ^ (prefixWord ++ tailWord_3312234).sum := by decide
  have hdescent : baseEnd_3312234 < baseStart_3312234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312301 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_3312301 : Nat := 118140960795 + 3312301 * 2 ^ 59
def prefixEnd_3312301 : Nat := 4983230072969 + 3 ^ 40 * 3312301 * 2
def baseEnd_3312301 : Nat := 566934161789383446934837

theorem tailTrace_3312301 : CollatzResearch.WordTrace tailWord_3312301 prefixEnd_3312301 566934161789383446934837 := by
  unfold tailWord_3312301
  simp only [CollatzResearch.WordTrace]
  refine ⟨120809542373106647818552757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80539694915404431879035171 120809542373106647818552757)
  ·
    refine ⟨11325894597478748232989321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120809542373106647818552757 11325894597478748232989321)
    ·
      refine ⟨8494420948109061174741991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11325894597478748232989321 8494420948109061174741991)
      ·
        refine ⟨12741631422163591762112987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8494420948109061174741991 12741631422163591762112987)
        ·
          refine ⟨19112447133245387643169481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12741631422163591762112987 19112447133245387643169481)
          ·
            refine ⟨14334335349934040732377111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19112447133245387643169481 14334335349934040732377111)
            ·
              refine ⟨21501503024901061098565667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14334335349934040732377111 21501503024901061098565667)
              ·
                refine ⟨32252254537351591647848501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21501503024901061098565667 32252254537351591647848501)
                ·
                  refine ⟨3023648862876711716985797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32252254537351591647848501 3023648862876711716985797)
                  ·
                    refine ⟨566934161789383446934837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3023648862876711716985797 566934161789383446934837)
                    ·
                      rfl

theorem cell23_3312301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_3312301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312301 prefixEnd_3312301 := by exact prefixLift 3312301
  have htrace : WordTrace (prefixWord ++ tailWord_3312301) baseStart_3312301 baseEnd_3312301 := by
    simpa [prefixWord, tailWord_3312301, baseEnd_3312301] using wordTrace_append hprefix tailTrace_3312301
  have hstable : (prefixWord ++ tailWord_3312301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312301).length < 2 ^ (prefixWord ++ tailWord_3312301).sum := by decide
  have hdescent : baseEnd_3312301 < baseStart_3312301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312305 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 2, 5]
def baseStart_3312305 : Nat := 118140960795 + 3312305 * 2 ^ 59
def prefixEnd_3312305 : Nat := 4983230072969 + 3 ^ 40 * 3312305 * 2
def baseEnd_3312305 : Nat := 566934846430256108384831

theorem tailTrace_3312305 : CollatzResearch.WordTrace tailWord_3312305 prefixEnd_3312305 566934846430256108384831 := by
  unfold tailWord_3312305
  simp only [CollatzResearch.WordTrace]
  refine ⟨120809688265092156501698369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80539792176728104334465579 120809688265092156501698369)
  ·
    refine ⟨90607266198819117376273777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120809688265092156501698369 90607266198819117376273777)
    ·
      refine ⟨67955449649114338032205333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90607266198819117376273777 67955449649114338032205333)
      ·
        refine ⟨3185411702302234595259625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67955449649114338032205333 3185411702302234595259625)
        ·
          refine ⟨2389058776726675946444719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3185411702302234595259625 2389058776726675946444719)
          ·
            refine ⟨3583588165090013919667079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389058776726675946444719 3583588165090013919667079)
            ·
              refine ⟨5375382247635020879500619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583588165090013919667079 5375382247635020879500619)
              ·
                refine ⟨8063073371452531319250929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375382247635020879500619 8063073371452531319250929)
                ·
                  refine ⟨6047305028589398489438197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8063073371452531319250929 6047305028589398489438197)
                  ·
                    refine ⟨566934846430256108384831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6047305028589398489438197 566934846430256108384831)
                    ·
                      rfl

theorem cell23_3312305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_3312305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312305 prefixEnd_3312305 := by exact prefixLift 3312305
  have htrace : WordTrace (prefixWord ++ tailWord_3312305) baseStart_3312305 baseEnd_3312305 := by
    simpa [prefixWord, tailWord_3312305, baseEnd_3312305] using wordTrace_append hprefix tailTrace_3312305
  have hstable : (prefixWord ++ tailWord_3312305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312305).length < 2 ^ (prefixWord ++ tailWord_3312305).sum := by decide
  have hdescent : baseEnd_3312305 < baseStart_3312305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312311 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 3]
def baseStart_3312311 : Nat := 118140960795 + 3312311 * 2 ^ 59
def prefixEnd_3312311 : Nat := 4983230072969 + 3 ^ 40 * 3312311 * 2
def baseEnd_3312311 : Nat := 1700807620174695301679465

theorem tailTrace_3312311 : CollatzResearch.WordTrace tailWord_3312311 prefixEnd_3312311 1700807620174695301679465 := by
  unfold tailWord_3312311
  simp only [CollatzResearch.WordTrace]
  refine ⟨120809907103070419526416787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80539938068713613017611191 120809907103070419526416787)
  ·
    refine ⟨181214860654605629289625181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120809907103070419526416787 181214860654605629289625181)
    ·
      refine ⟨67955572745477110983609443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181214860654605629289625181 67955572745477110983609443)
      ·
        refine ⟨101933359118215666475414165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67955572745477110983609443 101933359118215666475414165)
        ·
          refine ⟨4778126208666359366035039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101933359118215666475414165 4778126208666359366035039)
          ·
            refine ⟨7167189312999539049052559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778126208666359366035039 7167189312999539049052559)
            ·
              refine ⟨10750783969499308573578839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167189312999539049052559 10750783969499308573578839)
              ·
                refine ⟨16126175954248962860368259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10750783969499308573578839 16126175954248962860368259)
                ·
                  refine ⟨24189263931373444290552389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16126175954248962860368259 24189263931373444290552389)
                  ·
                    refine ⟨4535486987132520804478573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24189263931373444290552389 4535486987132520804478573)
                    ·
                      refine ⟨1700807620174695301679465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4535486987132520804478573 1700807620174695301679465)
                      ·
                        rfl

theorem cell23_3312311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_3312311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312311 prefixEnd_3312311 := by exact prefixLift 3312311
  have htrace : WordTrace (prefixWord ++ tailWord_3312311) baseStart_3312311 baseEnd_3312311 := by
    simpa [prefixWord, tailWord_3312311, baseEnd_3312311] using wordTrace_append hprefix tailTrace_3312311
  have hstable : (prefixWord ++ tailWord_3312311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312311).length < 2 ^ (prefixWord ++ tailWord_3312311).sum := by decide
  have hdescent : baseEnd_3312311 < baseStart_3312311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312334 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3312334 : Nat := 118140960795 + 3312334 * 2 ^ 59
def prefixEnd_3312334 : Nat := 4983230072969 + 3 ^ 40 * 3312334 * 2
def baseEnd_3312334 : Nat := 1700819430229748711691859

theorem tailTrace_3312334 : CollatzResearch.WordTrace tailWord_3312334 prefixEnd_3312334 1700819430229748711691859 := by
  unfold tailWord_3312334
  simp only [CollatzResearch.WordTrace]
  refine ⟨15101343247748386806813007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80540497321324729636336037 15101343247748386806813007)
  ·
    refine ⟨22652014871622580210219511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15101343247748386806813007 22652014871622580210219511)
    ·
      refine ⟨33978022307433870315329267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22652014871622580210219511 33978022307433870315329267)
      ·
        refine ⟨50967033461150805472993901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33978022307433870315329267 50967033461150805472993901)
        ·
          refine ⟨19112637547931552052372713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50967033461150805472993901 19112637547931552052372713)
          ·
            refine ⟨14334478160948664039279535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19112637547931552052372713 14334478160948664039279535)
            ·
              refine ⟨21501717241422996058919303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14334478160948664039279535 21501717241422996058919303)
              ·
                refine ⟨32252575862134494088378955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21501717241422996058919303 32252575862134494088378955)
                ·
                  refine ⟨48378863793201741132568433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32252575862134494088378955 48378863793201741132568433)
                  ·
                    refine ⟨36284147844901305849426325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48378863793201741132568433 36284147844901305849426325)
                    ·
                      refine ⟨1700819430229748711691859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36284147844901305849426325 1700819430229748711691859)
                      ·
                        rfl

theorem cell23_3312334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3312334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312334 prefixEnd_3312334 := by exact prefixLift 3312334
  have htrace : WordTrace (prefixWord ++ tailWord_3312334) baseStart_3312334 baseEnd_3312334 := by
    simpa [prefixWord, tailWord_3312334, baseEnd_3312334] using wordTrace_append hprefix tailTrace_3312334
  have hstable : (prefixWord ++ tailWord_3312334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312334).length < 2 ^ (prefixWord ++ tailWord_3312334).sum := by decide
  have hdescent : baseEnd_3312334 < baseStart_3312334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312347 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 10]
def baseStart_3312347 : Nat := 118140960795 + 3312347 * 2 ^ 59
def prefixEnd_3312347 : Nat := 4983230072969 + 3 ^ 40 * 3312347 * 2
def baseEnd_3312347 : Nat := 1700826105478257160829299

theorem tailTrace_3312347 : CollatzResearch.WordTrace tailWord_3312347 prefixEnd_3312347 1700826105478257160829299 := by
  unfold tailWord_3312347
  simp only [CollatzResearch.WordTrace]
  refine ⟨120811220130939997674727295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80540813420626665116484863 120811220130939997674727295)
  ·
    refine ⟨181216830196409996512090943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120811220130939997674727295 181216830196409996512090943)
    ·
      refine ⟨271825245294614994768136415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181216830196409996512090943 271825245294614994768136415)
      ·
        refine ⟨407737867941922492152204623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271825245294614994768136415 407737867941922492152204623)
        ·
          refine ⟨611606801912883738228306935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407737867941922492152204623 611606801912883738228306935)
          ·
            refine ⟨917410202869325607342460403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611606801912883738228306935 917410202869325607342460403)
            ·
              refine ⟨1376115304303988411013690605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917410202869325607342460403 1376115304303988411013690605)
              ·
                refine ⟨516043239113995654130133977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1376115304303988411013690605 516043239113995654130133977)
                ·
                  refine ⟨387032429335496740597600483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516043239113995654130133977 387032429335496740597600483)
                  ·
                    refine ⟨580548644003245110896400725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 387032429335496740597600483 580548644003245110896400725)
                    ·
                      refine ⟨1700826105478257160829299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 580548644003245110896400725 1700826105478257160829299)
                      ·
                        rfl

theorem cell23_3312347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_3312347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312347 prefixEnd_3312347 := by exact prefixLift 3312347
  have htrace : WordTrace (prefixWord ++ tailWord_3312347) baseStart_3312347 baseEnd_3312347 := by
    simpa [prefixWord, tailWord_3312347, baseEnd_3312347] using wordTrace_append hprefix tailTrace_3312347
  have hstable : (prefixWord ++ tailWord_3312347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312347).length < 2 ^ (prefixWord ++ tailWord_3312347).sum := by decide
  have hdescent : baseEnd_3312347 < baseStart_3312347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312351 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 1, 5, 2]
def baseStart_3312351 : Nat := 118140960795 + 3312351 * 2 ^ 59
def prefixEnd_3312351 : Nat := 4983230072969 + 3 ^ 40 * 3312351 * 2
def baseEnd_3312351 : Nat := 1700828159400875145179281

theorem tailTrace_3312351 : CollatzResearch.WordTrace tailWord_3312351 prefixEnd_3312351 1700828159400875145179281 := by
  unfold tailWord_3312351
  simp only [CollatzResearch.WordTrace]
  refine ⟨120811366022925506357872907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80540910681950337571915271 120811366022925506357872907)
  ·
    refine ⟨181217049034388259536809361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120811366022925506357872907 181217049034388259536809361)
    ·
      refine ⟨135912786775791194652607021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181217049034388259536809361 135912786775791194652607021)
      ·
        refine ⟨50967295040921697994727633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135912786775791194652607021 50967295040921697994727633)
        ·
          refine ⟨38225471280691273496045725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50967295040921697994727633 38225471280691273496045725)
          ·
            refine ⟨14334551730259227561017147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38225471280691273496045725 14334551730259227561017147)
            ·
              refine ⟨21501827595388841341525721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14334551730259227561017147 21501827595388841341525721)
              ·
                refine ⟨16126370696541631006144291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21501827595388841341525721 16126370696541631006144291)
                ·
                  refine ⟨24189556044812446509216437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16126370696541631006144291 24189556044812446509216437)
                  ·
                    refine ⟨2267770879201166860239041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24189556044812446509216437 2267770879201166860239041)
                    ·
                      refine ⟨1700828159400875145179281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267770879201166860239041 1700828159400875145179281)
                      ·
                        rfl

theorem cell23_3312351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_3312351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312351 prefixEnd_3312351 := by exact prefixLift 3312351
  have htrace : WordTrace (prefixWord ++ tailWord_3312351) baseStart_3312351 baseEnd_3312351 := by
    simpa [prefixWord, tailWord_3312351, baseEnd_3312351] using wordTrace_append hprefix tailTrace_3312351
  have hstable : (prefixWord ++ tailWord_3312351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312351).length < 2 ^ (prefixWord ++ tailWord_3312351).sum := by decide
  have hdescent : baseEnd_3312351 < baseStart_3312351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312381 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_3312381 : Nat := 118140960795 + 3312381 * 2 ^ 59
def prefixEnd_3312381 : Nat := 4983230072969 + 3 ^ 40 * 3312381 * 2
def baseEnd_3312381 : Nat := 1700843563820510027804143

theorem tailTrace_3312381 : CollatzResearch.WordTrace tailWord_3312381 prefixEnd_3312381 1700843563820510027804143 := by
  unfold tailWord_3312381
  simp only [CollatzResearch.WordTrace]
  refine ⟨120812460212816821481464997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80541640141877880987643331 120812460212816821481464997)
  ·
    refine ⟨22652336289903154027774687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120812460212816821481464997 22652336289903154027774687)
    ·
      refine ⟨33978504434854731041662031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22652336289903154027774687 33978504434854731041662031)
      ·
        refine ⟨50967756652282096562493047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33978504434854731041662031 50967756652282096562493047)
        ·
          refine ⟨76451634978423144843739571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50967756652282096562493047 76451634978423144843739571)
          ·
            refine ⟨114677452467634717265609357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76451634978423144843739571 114677452467634717265609357)
            ·
              refine ⟨43004044675363018974603509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114677452467634717265609357 43004044675363018974603509)
              ·
                refine ⟨4031629188315283028869079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43004044675363018974603509 4031629188315283028869079)
                ·
                  refine ⟨6047443782472924543303619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031629188315283028869079 6047443782472924543303619)
                  ·
                    refine ⟨9071165673709386814955429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6047443782472924543303619 9071165673709386814955429)
                    ·
                      refine ⟨1700843563820510027804143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9071165673709386814955429 1700843563820510027804143)
                      ·
                        rfl

theorem cell23_3312381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_3312381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312381 prefixEnd_3312381 := by exact prefixLift 3312381
  have htrace : WordTrace (prefixWord ++ tailWord_3312381) baseStart_3312381 baseEnd_3312381 := by
    simpa [prefixWord, tailWord_3312381, baseEnd_3312381] using wordTrace_append hprefix tailTrace_3312381
  have hstable : (prefixWord ++ tailWord_3312381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312381).length < 2 ^ (prefixWord ++ tailWord_3312381).sum := by decide
  have hdescent : baseEnd_3312381 < baseStart_3312381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312392 : List Nat := [2, 1, 3, 2, 2, 3, 3, 2, 1, 1, 3]
def baseStart_3312392 : Nat := 118140960795 + 3312392 * 2 ^ 59
def prefixEnd_3312392 : Nat := 4983230072969 + 3 ^ 40 * 3312392 * 2
def baseEnd_3312392 : Nat := 1700849212107709484766593

theorem tailTrace_3312392 : CollatzResearch.WordTrace tailWord_3312392 prefixEnd_3312392 1700849212107709484766593 := by
  unfold tailWord_3312392
  simp only [CollatzResearch.WordTrace]
  refine ⟨60406430707888485180057715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80541907610517980240076953 60406430707888485180057715)
  ·
    refine ⟨90609646061832727770086573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60406430707888485180057715 90609646061832727770086573)
    ·
      refine ⟨33978617273187272913782465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90609646061832727770086573 33978617273187272913782465)
      ·
        refine ⟨25483962954890454685336849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33978617273187272913782465 25483962954890454685336849)
        ·
          refine ⟨19112972216167841014002637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25483962954890454685336849 19112972216167841014002637)
          ·
            refine ⟨7167364581062940380250989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19112972216167841014002637 7167364581062940380250989)
            ·
              refine ⟨2687761717898602642594121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7167364581062940380250989 2687761717898602642594121)
              ·
                refine ⟨2015821288423951981945591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2687761717898602642594121 2015821288423951981945591)
                ·
                  refine ⟨3023731932635927972918387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015821288423951981945591 3023731932635927972918387)
                  ·
                    refine ⟨4535597898953891959377581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3023731932635927972918387 4535597898953891959377581)
                    ·
                      refine ⟨1700849212107709484766593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4535597898953891959377581 1700849212107709484766593)
                      ·
                        rfl

theorem cell23_3312392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_3312392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312392 prefixEnd_3312392 := by exact prefixLift 3312392
  have htrace : WordTrace (prefixWord ++ tailWord_3312392) baseStart_3312392 baseEnd_3312392 := by
    simpa [prefixWord, tailWord_3312392, baseEnd_3312392] using wordTrace_append hprefix tailTrace_3312392
  have hstable : (prefixWord ++ tailWord_3312392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312392).length < 2 ^ (prefixWord ++ tailWord_3312392).sum := by decide
  have hdescent : baseEnd_3312392 < baseStart_3312392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312394 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_3312394 : Nat := 118140960795 + 3312394 * 2 ^ 59
def prefixEnd_3312394 : Nat := 4983230072969 + 3 ^ 40 * 3312394 * 2
def baseEnd_3312394 : Nat := 1700850239069018476941583

theorem tailTrace_3312394 : CollatzResearch.WordTrace tailWord_3312394 prefixEnd_3312394 1700850239069018476941583 := by
  unfold tailWord_3312394
  simp only [CollatzResearch.WordTrace]
  refine ⟨30203233590442431175422059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80541956241179816467792157 30203233590442431175422059)
  ·
    refine ⟨45304850385663646763133089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30203233590442431175422059 45304850385663646763133089)
    ·
      refine ⟨33978637789247735072349817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45304850385663646763133089 33978637789247735072349817)
      ·
        refine ⟨25483978341935801304262363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33978637789247735072349817 25483978341935801304262363)
        ·
          refine ⟨38225967512903701956393545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25483978341935801304262363 38225967512903701956393545)
          ·
            refine ⟨28669475634677776467295159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38225967512903701956393545 28669475634677776467295159)
            ·
              refine ⟨43004213452016664700942739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28669475634677776467295159 43004213452016664700942739)
              ·
                refine ⟨64506320178024997051414109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43004213452016664700942739 64506320178024997051414109)
                ·
                  refine ⟨24189870066759373894280291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64506320178024997051414109 24189870066759373894280291)
                  ·
                    refine ⟨36284805100139060841420437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24189870066759373894280291 36284805100139060841420437)
                    ·
                      refine ⟨1700850239069018476941583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36284805100139060841420437 1700850239069018476941583)
                      ·
                        rfl

theorem cell23_3312394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_3312394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312394 prefixEnd_3312394 := by exact prefixLift 3312394
  have htrace : WordTrace (prefixWord ++ tailWord_3312394) baseStart_3312394 baseEnd_3312394 := by
    simpa [prefixWord, tailWord_3312394, baseEnd_3312394] using wordTrace_append hprefix tailTrace_3312394
  have hstable : (prefixWord ++ tailWord_3312394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312394).length < 2 ^ (prefixWord ++ tailWord_3312394).sum := by decide
  have hdescent : baseEnd_3312394 < baseStart_3312394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312418 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_3312418 : Nat := 118140960795 + 3312418 * 2 ^ 59
def prefixEnd_3312418 : Nat := 4983230072969 + 3 ^ 40 * 3312418 * 2
def baseEnd_3312418 : Nat := 1700862562604726383041473

theorem tailTrace_3312418 : CollatzResearch.WordTrace tailWord_3312418 prefixEnd_3312418 1700862562604726383041473 := by
  unfold tailWord_3312418
  simp only [CollatzResearch.WordTrace]
  refine ⟨30203452428420694200140477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80542539809121851200374605 30203452428420694200140477)
  ·
    refine ⟨11326294660657760325052679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30203452428420694200140477 11326294660657760325052679)
    ·
      refine ⟨16989441990986640487579019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11326294660657760325052679 16989441990986640487579019)
      ·
        refine ⟨25484162986479960731368529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16989441990986640487579019 25484162986479960731368529)
        ·
          refine ⟨19113122239859970548526397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25484162986479960731368529 19113122239859970548526397)
          ·
            refine ⟨7167420839947488955697399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19113122239859970548526397 7167420839947488955697399)
            ·
              refine ⟨10751131259921233433546099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167420839947488955697399 10751131259921233433546099)
              ·
                refine ⟨16126696889881850150319149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10751131259921233433546099 16126696889881850150319149)
                ·
                  refine ⟨6047511333705693806369681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16126696889881850150319149 6047511333705693806369681)
                  ·
                    refine ⟨4535633500279270354777261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6047511333705693806369681 4535633500279270354777261)
                    ·
                      refine ⟨1700862562604726383041473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4535633500279270354777261 1700862562604726383041473)
                      ·
                        rfl

theorem cell23_3312418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_3312418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312418 prefixEnd_3312418 := by exact prefixLift 3312418
  have htrace : WordTrace (prefixWord ++ tailWord_3312418) baseStart_3312418 baseEnd_3312418 := by
    simpa [prefixWord, tailWord_3312418, baseEnd_3312418] using wordTrace_append hprefix tailTrace_3312418
  have hstable : (prefixWord ++ tailWord_3312418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312418).length < 2 ^ (prefixWord ++ tailWord_3312418).sum := by decide
  have hdescent : baseEnd_3312418 < baseStart_3312418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312435 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 1, 2, 3]
def baseStart_3312435 : Nat := 118140960795 + 3312435 * 2 ^ 59
def prefixEnd_3312435 : Nat := 4983230072969 + 3 ^ 40 * 3312435 * 2
def baseEnd_3312435 : Nat := 1700871291775852816528895

theorem tailTrace_3312435 : CollatzResearch.WordTrace tailWord_3312435 prefixEnd_3312435 1700871291775852816528895 := by
  unfold tailWord_3312435
  simp only [CollatzResearch.WordTrace]
  refine ⟨120814429754621188703930759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80542953169747459135953839 120814429754621188703930759)
  ·
    refine ⟨181221644631931783055896139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120814429754621188703930759 181221644631931783055896139)
    ·
      refine ⟨271832466947897674583844209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181221644631931783055896139 271832466947897674583844209)
      ·
        refine ⟨203874350210923255937883157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271832466947897674583844209 203874350210923255937883157)
        ·
          refine ⟨9556610166137027622088273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 203874350210923255937883157 9556610166137027622088273)
          ·
            refine ⟨7167457624602770716566205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9556610166137027622088273 7167457624602770716566205)
            ·
              refine ⟨2687796609226039018712327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7167457624602770716566205 2687796609226039018712327)
              ·
                refine ⟨4031694913839058528068491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687796609226039018712327 4031694913839058528068491)
                ·
                  refine ⟨6047542370758587792102737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031694913839058528068491 6047542370758587792102737)
                  ·
                    refine ⟨4535656778068940844077053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6047542370758587792102737 4535656778068940844077053)
                    ·
                      refine ⟨1700871291775852816528895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4535656778068940844077053 1700871291775852816528895)
                      ·
                        rfl

theorem cell23_3312435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 2, 3].length) (baseStart_3312435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312435 prefixEnd_3312435 := by exact prefixLift 3312435
  have htrace : WordTrace (prefixWord ++ tailWord_3312435) baseStart_3312435 baseEnd_3312435 := by
    simpa [prefixWord, tailWord_3312435, baseEnd_3312435] using wordTrace_append hprefix tailTrace_3312435
  have hstable : (prefixWord ++ tailWord_3312435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312435).length < 2 ^ (prefixWord ++ tailWord_3312435).sum := by decide
  have hdescent : baseEnd_3312435 < baseStart_3312435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312438 : List Nat := [5, 1, 2, 2, 3, 10]
def baseStart_3312438 : Nat := 118140960795 + 3312438 * 2 ^ 59
def prefixEnd_3312438 : Nat := 4983230072969 + 3 ^ 40 * 3312438 * 2
def baseEnd_3312438 : Nat := 6999476675793482735767

theorem tailTrace_3312438 : CollatzResearch.WordTrace tailWord_3312438 prefixEnd_3312438 6999476675793482735767 := by
  unfold tailWord_3312438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550908698350645013518123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80543026115740213477526645 7550908698350645013518123)
  ·
    refine ⟨11326363047525967520277185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7550908698350645013518123 11326363047525967520277185)
    ·
      refine ⟨8494772285644475640207889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11326363047525967520277185 8494772285644475640207889)
      ·
        refine ⟨6371079214233356730155917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8494772285644475640207889 6371079214233356730155917)
        ·
          refine ⟨2389154705337508773808469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6371079214233356730155917 2389154705337508773808469)
          ·
            refine ⟨6999476675793482735767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2389154705337508773808469 6999476675793482735767)
            ·
              rfl

theorem cell23_3312438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 10].length) (baseStart_3312438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312438 prefixEnd_3312438 := by exact prefixLift 3312438
  have htrace : WordTrace (prefixWord ++ tailWord_3312438) baseStart_3312438 baseEnd_3312438 := by
    simpa [prefixWord, tailWord_3312438, baseEnd_3312438] using wordTrace_append hprefix tailTrace_3312438
  have hstable : (prefixWord ++ tailWord_3312438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312438).length < 2 ^ (prefixWord ++ tailWord_3312438).sum := by decide
  have hdescent : baseEnd_3312438 < baseStart_3312438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312464 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 1, 8]
def baseStart_3312464 : Nat := 118140960795 + 3312464 * 2 ^ 59
def prefixEnd_3312464 : Nat := 4983230072969 + 3 ^ 40 * 3312464 * 2
def baseEnd_3312464 : Nat := 566962060904944401022087

theorem tailTrace_3312464 : CollatzResearch.WordTrace tailWord_3312464 prefixEnd_3312464 566962060904944401022087 := by
  unfold tailWord_3312464
  simp only [CollatzResearch.WordTrace]
  refine ⟨60407743735758063328368223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80543658314344084437824297 60407743735758063328368223)
  ·
    refine ⟨90611615603637094992552335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60407743735758063328368223 90611615603637094992552335)
    ·
      refine ⟨135917423405455642488828503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90611615603637094992552335 135917423405455642488828503)
      ·
        refine ⟨203876135108183463733242755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135917423405455642488828503 203876135108183463733242755)
        ·
          refine ⟨305814202662275195599864133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203876135108183463733242755 305814202662275195599864133)
          ·
            refine ⟨57340162999176599174974525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305814202662275195599864133 57340162999176599174974525)
            ·
              refine ⟨21502561124691224690615447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57340162999176599174974525 21502561124691224690615447)
              ·
                refine ⟨32253841687036837035923171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21502561124691224690615447 32253841687036837035923171)
                ·
                  refine ⟨48380762530555255553884757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32253841687036837035923171 48380762530555255553884757)
                  ·
                    refine ⟨566962060904944401022087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48380762530555255553884757 566962060904944401022087)
                    ·
                      rfl

theorem cell23_3312464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_3312464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312464 prefixEnd_3312464 := by exact prefixLift 3312464
  have htrace : WordTrace (prefixWord ++ tailWord_3312464) baseStart_3312464 baseEnd_3312464 := by
    simpa [prefixWord, tailWord_3312464, baseEnd_3312464] using wordTrace_append hprefix tailTrace_3312464
  have hstable : (prefixWord ++ tailWord_3312464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312464).length < 2 ^ (prefixWord ++ tailWord_3312464).sum := by decide
  have hdescent : baseEnd_3312464 < baseStart_3312464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312504 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_3312504 : Nat := 118140960795 + 3312504 * 2 ^ 59
def prefixEnd_3312504 : Nat := 4983230072969 + 3 ^ 40 * 3312504 * 2
def baseEnd_3312504 : Nat := 1700906721941013046566077

theorem tailTrace_3312504 : CollatzResearch.WordTrace tailWord_3312504 prefixEnd_3312504 1700906721941013046566077 := by
  unfold tailWord_3312504
  simp only [CollatzResearch.WordTrace]
  refine ⟨60408473195685606744096283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80544630927580808992128377 60408473195685606744096283)
  ·
    refine ⟨90612709793528410116144425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60408473195685606744096283 90612709793528410116144425)
    ·
      refine ⟨67959532345146307587108319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90612709793528410116144425 67959532345146307587108319)
      ·
        refine ⟨101939298517719461380662479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67959532345146307587108319 101939298517719461380662479)
        ·
          refine ⟨152908947776579192070993719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101939298517719461380662479 152908947776579192070993719)
          ·
            refine ⟨229363421664868788106490579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152908947776579192070993719 229363421664868788106490579)
            ·
              refine ⟨344045132497303182159735869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229363421664868788106490579 344045132497303182159735869)
              ·
                refine ⟨129016924686488693309900951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344045132497303182159735869 129016924686488693309900951)
                ·
                  refine ⟨193525387029733039964851427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129016924686488693309900951 193525387029733039964851427)
                  ·
                    refine ⟨290288080544599559947277141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193525387029733039964851427 290288080544599559947277141)
                    ·
                      refine ⟨1700906721941013046566077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 290288080544599559947277141 1700906721941013046566077)
                      ·
                        rfl

theorem cell23_3312504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_3312504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312504 prefixEnd_3312504 := by exact prefixLift 3312504
  have htrace : WordTrace (prefixWord ++ tailWord_3312504) baseStart_3312504 baseEnd_3312504 := by
    simpa [prefixWord, tailWord_3312504, baseEnd_3312504] using wordTrace_append hprefix tailTrace_3312504
  have hstable : (prefixWord ++ tailWord_3312504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312504).length < 2 ^ (prefixWord ++ tailWord_3312504).sum := by decide
  have hdescent : baseEnd_3312504 < baseStart_3312504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312505 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 4, 2, 2]
def baseStart_3312505 : Nat := 118140960795 + 3312505 * 2 ^ 59
def prefixEnd_3312505 : Nat := 4983230072969 + 3 ^ 40 * 3312505 * 2
def baseEnd_3312505 : Nat := 1700907235421667542653573

theorem tailTrace_3312505 : CollatzResearch.WordTrace tailWord_3312505 prefixEnd_3312505 1700907235421667542653573 := by
  unfold tailWord_3312505
  simp only [CollatzResearch.WordTrace]
  refine ⟨120816982864367590658978969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80544655242911727105985979 120816982864367590658978969)
  ·
    refine ⟨90612737148275692994234227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120816982864367590658978969 90612737148275692994234227)
    ·
      refine ⟨135919105722413539491351341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90612737148275692994234227 135919105722413539491351341)
      ·
        refine ⟨50969664645905077309256753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135919105722413539491351341 50969664645905077309256753)
        ·
          refine ⟨38227248484428807981942565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50969664645905077309256753 38227248484428807981942565)
          ·
            refine ⟨7167609090830401496614231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38227248484428807981942565 7167609090830401496614231)
            ·
              refine ⟨10751413636245602244921347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167609090830401496614231 10751413636245602244921347)
              ·
                refine ⟨16127120454368403367382021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10751413636245602244921347 16127120454368403367382021)
                ·
                  refine ⟨3023835085194075631384129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16127120454368403367382021 3023835085194075631384129)
                  ·
                    refine ⟨2267876313895556723538097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3023835085194075631384129 2267876313895556723538097)
                    ·
                      refine ⟨1700907235421667542653573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267876313895556723538097 1700907235421667542653573)
                      ·
                        rfl

theorem cell23_3312505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_3312505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312505 prefixEnd_3312505 := by exact prefixLift 3312505
  have htrace : WordTrace (prefixWord ++ tailWord_3312505) baseStart_3312505 baseEnd_3312505 := by
    simpa [prefixWord, tailWord_3312505, baseEnd_3312505] using wordTrace_append hprefix tailTrace_3312505
  have hstable : (prefixWord ++ tailWord_3312505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312505).length < 2 ^ (prefixWord ++ tailWord_3312505).sum := by decide
  have hdescent : baseEnd_3312505 < baseStart_3312505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312522 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2]
def baseStart_3312522 : Nat := 118140960795 + 3312522 * 2 ^ 59
def prefixEnd_3312522 : Nat := 4983230072969 + 3 ^ 40 * 3312522 * 2
def baseEnd_3312522 : Nat := 1700915964592793976140995

theorem tailTrace_3312522 : CollatzResearch.WordTrace tailWord_3312522 prefixEnd_3312522 1700915964592793976140995 := by
  unfold tailWord_3312522
  simp only [CollatzResearch.WordTrace]
  refine ⟨30204400726326500640586955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80545068603537335041565213 30204400726326500640586955)
  ·
    refine ⟨45306601089489750960880433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30204400726326500640586955 45306601089489750960880433)
    ·
      refine ⟨33979950817117313220660325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45306601089489750960880433 33979950817117313220660325)
      ·
        refine ⟨6371240778209496228873811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33979950817117313220660325 6371240778209496228873811)
        ·
          refine ⟨9556861167314244343310717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6371240778209496228873811 9556861167314244343310717)
          ·
            refine ⟨3583822937742841628741519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9556861167314244343310717 3583822937742841628741519)
            ·
              refine ⟨5375734406614262443112279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583822937742841628741519 5375734406614262443112279)
              ·
                refine ⟨8063601609921393664668419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375734406614262443112279 8063601609921393664668419)
                ·
                  refine ⟨12095402414882090497002629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8063601609921393664668419 12095402414882090497002629)
                  ·
                    refine ⟨2267887952790391968187993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12095402414882090497002629 2267887952790391968187993)
                    ·
                      refine ⟨1700915964592793976140995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267887952790391968187993 1700915964592793976140995)
                      ·
                        rfl

theorem cell23_3312522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_3312522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312522 prefixEnd_3312522 := by exact prefixLift 3312522
  have htrace : WordTrace (prefixWord ++ tailWord_3312522) baseStart_3312522 baseEnd_3312522 := by
    simpa [prefixWord, tailWord_3312522, baseEnd_3312522] using wordTrace_append hprefix tailTrace_3312522
  have hstable : (prefixWord ++ tailWord_3312522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312522).length < 2 ^ (prefixWord ++ tailWord_3312522).sum := by decide
  have hdescent : baseEnd_3312522 < baseStart_3312522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312541 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_3312541 : Nat := 118140960795 + 3312541 * 2 ^ 59
def prefixEnd_3312541 : Nat := 4983230072969 + 3 ^ 40 * 3312541 * 2
def baseEnd_3312541 : Nat := 566975240241743133934469

theorem tailTrace_3312541 : CollatzResearch.WordTrace tailWord_3312541 prefixEnd_3312541 566975240241743133934469 := by
  unfold tailWord_3312541
  simp only [CollatzResearch.WordTrace]
  refine ⟨120818295892237168807289477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80545530594824779204859651 120818295892237168807289477)
  ·
    refine ⟨22653430479794469151366777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120818295892237168807289477 22653430479794469151366777)
    ·
      refine ⟨16990072859845851863525083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22653430479794469151366777 16990072859845851863525083)
      ·
        refine ⟨25485109289768777795287625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16990072859845851863525083 25485109289768777795287625)
        ·
          refine ⟨19113831967326583346465719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25485109289768777795287625 19113831967326583346465719)
          ·
            refine ⟨28670747950989875019698579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19113831967326583346465719 28670747950989875019698579)
            ·
              refine ⟨43006121926484812529547869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28670747950989875019698579 43006121926484812529547869)
              ·
                refine ⟨16127295722431804698580451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43006121926484812529547869 16127295722431804698580451)
                ·
                  refine ⟨24190943583647707047870677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16127295722431804698580451 24190943583647707047870677)
                  ·
                    refine ⟨566975240241743133934469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24190943583647707047870677 566975240241743133934469)
                    ·
                      rfl

theorem cell23_3312541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_3312541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312541 prefixEnd_3312541 := by exact prefixLift 3312541
  have htrace : WordTrace (prefixWord ++ tailWord_3312541) baseStart_3312541 baseEnd_3312541 := by
    simpa [prefixWord, tailWord_3312541, baseEnd_3312541] using wordTrace_append hprefix tailTrace_3312541
  have hstable : (prefixWord ++ tailWord_3312541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312541).length < 2 ^ (prefixWord ++ tailWord_3312541).sum := by decide
  have hdescent : baseEnd_3312541 < baseStart_3312541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312545 : List Nat := [1, 2, 3, 4, 1, 1, 3, 3, 5]
def baseStart_3312545 : Nat := 118140960795 + 3312545 * 2 ^ 59
def prefixEnd_3312545 : Nat := 4983230072969 + 3 ^ 40 * 3312545 * 2
def baseEnd_3312545 : Nat := 188991974960871931794821

theorem tailTrace_3312545 : CollatzResearch.WordTrace tailWord_3312545 prefixEnd_3312545 188991974960871931794821 := by
  unfold tailWord_3312545
  simp only [CollatzResearch.WordTrace]
  refine ⟨120818441784222677490435089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80545627856148451660290059 120818441784222677490435089)
  ·
    refine ⟨90613831338167008117826317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120818441784222677490435089 90613831338167008117826317)
    ·
      refine ⟨33980186751812628044184869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90613831338167008117826317 33980186751812628044184869)
      ·
        refine ⟨6371285015964867758284663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33980186751812628044184869 6371285015964867758284663)
        ·
          refine ⟨9556927523947301637426995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6371285015964867758284663 9556927523947301637426995)
          ·
            refine ⟨14335391285920952456140493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9556927523947301637426995 14335391285920952456140493)
            ·
              refine ⟨5375771732220357171052685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14335391285920952456140493 5375771732220357171052685)
              ·
                refine ⟨2015914399582633939144757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5375771732220357171052685 2015914399582633939144757)
                ·
                  refine ⟨188991974960871931794821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2015914399582633939144757 188991974960871931794821)
                  ·
                    rfl

theorem cell23_3312545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 5].length) (baseStart_3312545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312545 prefixEnd_3312545 := by exact prefixLift 3312545
  have htrace : WordTrace (prefixWord ++ tailWord_3312545) baseStart_3312545 baseEnd_3312545 := by
    simpa [prefixWord, tailWord_3312545, baseEnd_3312545] using wordTrace_append hprefix tailTrace_3312545
  have hstable : (prefixWord ++ tailWord_3312545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312545).length < 2 ^ (prefixWord ++ tailWord_3312545).sum := by decide
  have hdescent : baseEnd_3312545 < baseStart_3312545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312588 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 5, 4]
def baseStart_3312588 : Nat := 118140960795 + 3312588 * 2 ^ 59
def prefixEnd_3312588 : Nat := 4983230072969 + 3 ^ 40 * 3312588 * 2
def baseEnd_3312588 : Nat := 566983284771996905971897

theorem tailTrace_3312588 : CollatzResearch.WordTrace tailWord_3312588 prefixEnd_3312588 566983284771996905971897 := by
  unfold tailWord_3312588
  simp only [CollatzResearch.WordTrace]
  refine ⟨60410005061533447917125209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80546673415377930556166945 60410005061533447917125209)
  ·
    refine ⟨45307503796150085937843907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60410005061533447917125209 45307503796150085937843907)
    ·
      refine ⟨67961255694225128906765861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45307503796150085937843907 67961255694225128906765861)
      ·
        refine ⟨12742735442667211670018599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67961255694225128906765861 12742735442667211670018599)
        ·
          refine ⟨19114103164000817505027899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12742735442667211670018599 19114103164000817505027899)
          ·
            refine ⟨28671154746001226257541849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19114103164000817505027899 28671154746001226257541849)
            ·
              refine ⟨21503366059500919693156387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28671154746001226257541849 21503366059500919693156387)
              ·
                refine ⟨32255049089251379539734581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21503366059500919693156387 32255049089251379539734581)
                ·
                  refine ⟨3023910852117316831850117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32255049089251379539734581 3023910852117316831850117)
                  ·
                    refine ⟨566983284771996905971897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3023910852117316831850117 566983284771996905971897)
                    ·
                      rfl

theorem cell23_3312588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_3312588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312588 prefixEnd_3312588 := by exact prefixLift 3312588
  have htrace : WordTrace (prefixWord ++ tailWord_3312588) baseStart_3312588 baseEnd_3312588 := by
    simpa [prefixWord, tailWord_3312588, baseEnd_3312588] using wordTrace_append hprefix tailTrace_3312588
  have hstable : (prefixWord ++ tailWord_3312588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312588).length < 2 ^ (prefixWord ++ tailWord_3312588).sum := by decide
  have hdescent : baseEnd_3312588 < baseStart_3312588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312615 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3312615 : Nat := 118140960795 + 3312615 * 2 ^ 59
def prefixEnd_3312615 : Nat := 4983230072969 + 3 ^ 40 * 3312615 * 2
def baseEnd_3312615 : Nat := 1700963718293662112278067

theorem tailTrace_3312615 : CollatzResearch.WordTrace tailWord_3312615 prefixEnd_3312615 1700963718293662112278067 := by
  unfold tailWord_3312615
  simp only [CollatzResearch.WordTrace]
  refine ⟨120820994893969079445483299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80547329929312719630322199 120820994893969079445483299)
  ·
    refine ⟨181231492340953619168224949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120820994893969079445483299 181231492340953619168224949)
    ·
      refine ⟨16990452406964401797021089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181231492340953619168224949 16990452406964401797021089)
      ·
        refine ⟨12742839305223301347765817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16990452406964401797021089 12742839305223301347765817)
        ·
          refine ⟨9557129478917476010824363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12742839305223301347765817 9557129478917476010824363)
          ·
            refine ⟨14335694218376214016236545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9557129478917476010824363 14335694218376214016236545)
            ·
              refine ⟨10751770663782160512177409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14335694218376214016236545 10751770663782160512177409)
              ·
                refine ⟨8063827997836620384133057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10751770663782160512177409 8063827997836620384133057)
                ·
                  refine ⟨6047870998377465288099793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8063827997836620384133057 6047870998377465288099793)
                  ·
                    refine ⟨4535903248783098966074845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6047870998377465288099793 4535903248783098966074845)
                    ·
                      refine ⟨1700963718293662112278067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4535903248783098966074845 1700963718293662112278067)
                      ·
                        rfl

theorem cell23_3312615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3312615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312615 prefixEnd_3312615 := by exact prefixLift 3312615
  have htrace : WordTrace (prefixWord ++ tailWord_3312615) baseStart_3312615 baseEnd_3312615 := by
    simpa [prefixWord, tailWord_3312615, baseEnd_3312615] using wordTrace_append hprefix tailTrace_3312615
  have hstable : (prefixWord ++ tailWord_3312615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312615).length < 2 ^ (prefixWord ++ tailWord_3312615).sum := by decide
  have hdescent : baseEnd_3312615 < baseStart_3312615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312618 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 6]
def baseStart_3312618 : Nat := 118140960795 + 3312618 * 2 ^ 59
def prefixEnd_3312618 : Nat := 4983230072969 + 3 ^ 40 * 3312618 * 2
def baseEnd_3312618 : Nat := 188996139859513955615617

theorem tailTrace_3312618 : CollatzResearch.WordTrace tailWord_3312618 prefixEnd_3312618 188996139859513955615617 := by
  unfold tailWord_3312618
  simp only [CollatzResearch.WordTrace]
  refine ⟨30205276078239552739460627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80547402875305473971895005 30205276078239552739460627)
  ·
    refine ⟨45307914117359329109190941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30205276078239552739460627 45307914117359329109190941)
    ·
      refine ⟨16990467794009748415946603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45307914117359329109190941 16990467794009748415946603)
      ·
        refine ⟨25485701691014622623919905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16990467794009748415946603 25485701691014622623919905)
        ·
          refine ⟨19114276268260966967939929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25485701691014622623919905 19114276268260966967939929)
          ·
            refine ⟨14335707201195725225954947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19114276268260966967939929 14335707201195725225954947)
            ·
              refine ⟨21503560801793587838932421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14335707201195725225954947 21503560801793587838932421)
              ·
                refine ⟨4031917650336297719799829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21503560801793587838932421 4031917650336297719799829)
                ·
                  refine ⟨188996139859513955615617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4031917650336297719799829 188996139859513955615617)
                  ·
                    rfl

theorem cell23_3312618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_3312618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312618 prefixEnd_3312618 := by exact prefixLift 3312618
  have htrace : WordTrace (prefixWord ++ tailWord_3312618) baseStart_3312618 baseEnd_3312618 := by
    simpa [prefixWord, tailWord_3312618, baseEnd_3312618] using wordTrace_append hprefix tailTrace_3312618
  have hstable : (prefixWord ++ tailWord_3312618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312618).length < 2 ^ (prefixWord ++ tailWord_3312618).sum := by decide
  have hdescent : baseEnd_3312618 < baseStart_3312618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312629 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3312629 : Nat := 118140960795 + 3312629 * 2 ^ 59
def prefixEnd_3312629 : Nat := 4983230072969 + 3 ^ 40 * 3312629 * 2
def baseEnd_3312629 : Nat := 1700970907022825057503003

theorem tailTrace_3312629 : CollatzResearch.WordTrace tailWord_3312629 prefixEnd_3312629 1700970907022825057503003 := by
  unfold tailWord_3312629
  simp only [CollatzResearch.WordTrace]
  refine ⟨120821505515918359836492941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80547670343945573224328627 120821505515918359836492941)
  ·
    refine ⟨45308064568469384938684853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120821505515918359836492941 45308064568469384938684853)
    ·
      refine ⟨4247631053294004838001705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45308064568469384938684853 4247631053294004838001705)
      ·
        refine ⟨3185723289970503628501279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4247631053294004838001705 3185723289970503628501279)
        ·
          refine ⟨4778584934955755442751919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185723289970503628501279 4778584934955755442751919)
          ·
            refine ⟨7167877402433633164127879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778584934955755442751919 7167877402433633164127879)
            ·
              refine ⟨10751816103650449746191819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167877402433633164127879 10751816103650449746191819)
              ·
                refine ⟨16127724155475674619287729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10751816103650449746191819 16127724155475674619287729)
                ·
                  refine ⟨12095793116606755964465797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16127724155475674619287729 12095793116606755964465797)
                  ·
                    refine ⟨2267961209363766743337337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12095793116606755964465797 2267961209363766743337337)
                    ·
                      refine ⟨1700970907022825057503003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2267961209363766743337337 1700970907022825057503003)
                      ·
                        rfl

theorem cell23_3312629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3312629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312629 prefixEnd_3312629 := by exact prefixLift 3312629
  have htrace : WordTrace (prefixWord ++ tailWord_3312629) baseStart_3312629 baseEnd_3312629 := by
    simpa [prefixWord, tailWord_3312629, baseEnd_3312629] using wordTrace_append hprefix tailTrace_3312629
  have hstable : (prefixWord ++ tailWord_3312629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312629).length < 2 ^ (prefixWord ++ tailWord_3312629).sum := by decide
  have hdescent : baseEnd_3312629 < baseStart_3312629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312645 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 3, 1, 3]
def baseStart_3312645 : Nat := 118140960795 + 3312645 * 2 ^ 59
def prefixEnd_3312645 : Nat := 4983230072969 + 3 ^ 40 * 3312645 * 2
def baseEnd_3312645 : Nat := 1700979122713296994902929

theorem tailTrace_3312645 : CollatzResearch.WordTrace tailWord_3312645 prefixEnd_3312645 1700979122713296994902929 := by
  unfold tailWord_3312645
  simp only [CollatzResearch.WordTrace]
  refine ⟨120822089083860394569075389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80548059389240263046050259 120822089083860394569075389)
  ·
    refine ⟨45308283406447647963403271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120822089083860394569075389 45308283406447647963403271)
    ·
      refine ⟨67962425109671471945104907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45308283406447647963403271 67962425109671471945104907)
      ·
        refine ⟨101943637664507207917657361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67962425109671471945104907 101943637664507207917657361)
        ·
          refine ⟨76457728248380405938243021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101943637664507207917657361 76457728248380405938243021)
          ·
            refine ⟨28671648093142652226841133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76457728248380405938243021 28671648093142652226841133)
            ·
              refine ⟨10751868034928494585065425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28671648093142652226841133 10751868034928494585065425)
              ·
                refine ⟨8063901026196370938799069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10751868034928494585065425 8063901026196370938799069)
                ·
                  refine ⟨3023962884823639102049651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8063901026196370938799069 3023962884823639102049651)
                  ·
                    refine ⟨4535944327235458653074477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3023962884823639102049651 4535944327235458653074477)
                    ·
                      refine ⟨1700979122713296994902929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4535944327235458653074477 1700979122713296994902929)
                      ·
                        rfl

theorem cell23_3312645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_3312645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312645 prefixEnd_3312645 := by exact prefixLift 3312645
  have htrace : WordTrace (prefixWord ++ tailWord_3312645) baseStart_3312645 baseEnd_3312645 := by
    simpa [prefixWord, tailWord_3312645, baseEnd_3312645] using wordTrace_append hprefix tailTrace_3312645
  have hstable : (prefixWord ++ tailWord_3312645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312645).length < 2 ^ (prefixWord ++ tailWord_3312645).sum := by decide
  have hdescent : baseEnd_3312645 < baseStart_3312645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312648 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 3, 5]
def baseStart_3312648 : Nat := 118140960795 + 3312648 * 2 ^ 59
def prefixEnd_3312648 : Nat := 4983230072969 + 3 ^ 40 * 3312648 * 2
def baseEnd_3312648 : Nat := 566993554385086827721805

theorem tailTrace_3312648 : CollatzResearch.WordTrace tailWord_3312648 prefixEnd_3312648 566993554385086827721805 := by
  unfold tailWord_3312648
  simp only [CollatzResearch.WordTrace]
  refine ⟨60411099251424763040717299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80548132335233017387623065 60411099251424763040717299)
  ·
    refine ⟨90616648877137144561075949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60411099251424763040717299 90616648877137144561075949)
    ·
      refine ⟨33981243328926429210403481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90616648877137144561075949 33981243328926429210403481)
      ·
        refine ⟨25485932496694821907802611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33981243328926429210403481 25485932496694821907802611)
        ·
          refine ⟨38228898745042232861703917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25485932496694821907802611 38228898745042232861703917)
          ·
            refine ⟨14335837029390837323138969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38228898745042232861703917 14335837029390837323138969)
            ·
              refine ⟨10751877772043127992354227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14335837029390837323138969 10751877772043127992354227)
              ·
                refine ⟨16127816658064691988531341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10751877772043127992354227 16127816658064691988531341)
                ·
                  refine ⟨6047931246774259495699253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16127816658064691988531341 6047931246774259495699253)
                  ·
                    refine ⟨566993554385086827721805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6047931246774259495699253 566993554385086827721805)
                    ·
                      rfl

theorem cell23_3312648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_3312648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312648 prefixEnd_3312648 := by exact prefixLift 3312648
  have htrace : WordTrace (prefixWord ++ tailWord_3312648) baseStart_3312648 baseEnd_3312648 := by
    simpa [prefixWord, tailWord_3312648, baseEnd_3312648] using wordTrace_append hprefix tailTrace_3312648
  have hstable : (prefixWord ++ tailWord_3312648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312648).length < 2 ^ (prefixWord ++ tailWord_3312648).sum := by decide
  have hdescent : baseEnd_3312648 < baseStart_3312648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312665 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 1, 5]
def baseStart_3312665 : Nat := 118140960795 + 3312665 * 2 ^ 59
def prefixEnd_3312665 : Nat := 4983230072969 + 3 ^ 40 * 3312665 * 2
def baseEnd_3312665 : Nat := 566996464108795638884279

theorem tailTrace_3312665 : CollatzResearch.WordTrace tailWord_3312665 prefixEnd_3312665 566996464108795638884279 := by
  unfold tailWord_3312665
  simp only [CollatzResearch.WordTrace]
  refine ⟨120822818543787937984803449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80548545695858625323202299 120822818543787937984803449)
  ·
    refine ⟨90617113907840953488602587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120822818543787937984803449 90617113907840953488602587)
    ·
      refine ⟨135925670861761430232903881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90617113907840953488602587 135925670861761430232903881)
      ·
        refine ⟨101944253146321072674677911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135925670861761430232903881 101944253146321072674677911)
        ·
          refine ⟨152916379719481609012016867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101944253146321072674677911 152916379719481609012016867)
          ·
            refine ⟨229374569579222413518025301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152916379719481609012016867 229374569579222413518025301)
            ·
              refine ⟨2687983237256512658414359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 229374569579222413518025301 2687983237256512658414359)
              ·
                refine ⟨4031974855884768987621539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687983237256512658414359 4031974855884768987621539)
                ·
                  refine ⟨6047962283827153481432309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031974855884768987621539 6047962283827153481432309)
                  ·
                    refine ⟨566996464108795638884279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6047962283827153481432309 566996464108795638884279)
                    ·
                      rfl

theorem cell23_3312665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 5].length) (baseStart_3312665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312665 prefixEnd_3312665 := by exact prefixLift 3312665
  have htrace : WordTrace (prefixWord ++ tailWord_3312665) baseStart_3312665 baseEnd_3312665 := by
    simpa [prefixWord, tailWord_3312665, baseEnd_3312665] using wordTrace_append hprefix tailTrace_3312665
  have hstable : (prefixWord ++ tailWord_3312665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312665).length < 2 ^ (prefixWord ++ tailWord_3312665).sum := by decide
  have hdescent : baseEnd_3312665 < baseStart_3312665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312679 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3312679 : Nat := 118140960795 + 3312679 * 2 ^ 59
def prefixEnd_3312679 : Nat := 4983230072969 + 3 ^ 40 * 3312679 * 2
def baseEnd_3312679 : Nat := 1700996581055549861877773

theorem tailTrace_3312679 : CollatzResearch.WordTrace tailWord_3312679 prefixEnd_3312679 1700996581055549861877773 := by
  unfold tailWord_3312679
  simp only [CollatzResearch.WordTrace]
  refine ⟨120823329165737218375813091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80548886110491478917208727 120823329165737218375813091)
  ·
    refine ⟨181234993748605827563719637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120823329165737218375813091 181234993748605827563719637)
    ·
      refine ⟨4247695165982949083524679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 181234993748605827563719637 4247695165982949083524679)
      ·
        refine ⟨6371542748974423625287019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4247695165982949083524679 6371542748974423625287019)
        ·
          refine ⟨9557314123461635437930529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6371542748974423625287019 9557314123461635437930529)
          ·
            refine ⟨7167985592596226578447897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9557314123461635437930529 7167985592596226578447897)
            ·
              refine ⟨5375989194447169933835923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7167985592596226578447897 5375989194447169933835923)
              ·
                refine ⟨8063983791670754900753885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375989194447169933835923 8063983791670754900753885)
                ·
                  refine ⟨3023993921876533087782707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8063983791670754900753885 3023993921876533087782707)
                  ·
                    refine ⟨4535990882814799631674061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3023993921876533087782707 4535990882814799631674061)
                    ·
                      refine ⟨1700996581055549861877773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4535990882814799631674061 1700996581055549861877773)
                      ·
                        rfl

theorem cell23_3312679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3312679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312679 prefixEnd_3312679 := by exact prefixLift 3312679
  have htrace : WordTrace (prefixWord ++ tailWord_3312679) baseStart_3312679 baseEnd_3312679 := by
    simpa [prefixWord, tailWord_3312679, baseEnd_3312679] using wordTrace_append hprefix tailTrace_3312679
  have hstable : (prefixWord ++ tailWord_3312679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312679).length < 2 ^ (prefixWord ++ tailWord_3312679).sum := by decide
  have hdescent : baseEnd_3312679 < baseStart_3312679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312688 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 5]
def baseStart_3312688 : Nat := 118140960795 + 3312688 * 2 ^ 59
def prefixEnd_3312688 : Nat := 4983230072969 + 3 ^ 40 * 3312688 * 2
def baseEnd_3312688 : Nat := 1701001202381440326665231

theorem tailTrace_3312688 : CollatzResearch.WordTrace tailWord_3312688 prefixEnd_3312688 1701001202381440326665231 := by
  unfold tailWord_3312688
  simp only [CollatzResearch.WordTrace]
  refine ⟨60411828711352306456445359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80549104948469741941927145 60411828711352306456445359)
  ·
    refine ⟨90617743067028459684668039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60411828711352306456445359 90617743067028459684668039)
    ·
      refine ⟨135926614600542689527002059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90617743067028459684668039 135926614600542689527002059)
      ·
        refine ⟨203889921900814034290503089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135926614600542689527002059 203889921900814034290503089)
        ·
          refine ⟨152917441425610525717877317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203889921900814034290503089 152917441425610525717877317)
          ·
            refine ⟨28672020267301973572101997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152917441425610525717877317 28672020267301973572101997)
            ·
              refine ⟨10752007600238240089538249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28672020267301973572101997 10752007600238240089538249)
              ·
                refine ⟨8064005700178680067153687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10752007600238240089538249 8064005700178680067153687)
                ·
                  refine ⟨12096008550268020100730531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8064005700178680067153687 12096008550268020100730531)
                  ·
                    refine ⟨18144012825402030151095797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12096008550268020100730531 18144012825402030151095797)
                    ·
                      refine ⟨1701001202381440326665231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18144012825402030151095797 1701001202381440326665231)
                      ·
                        rfl

theorem cell23_3312688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_3312688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312688 prefixEnd_3312688 := by exact prefixLift 3312688
  have htrace : WordTrace (prefixWord ++ tailWord_3312688) baseStart_3312688 baseEnd_3312688 := by
    simpa [prefixWord, tailWord_3312688, baseEnd_3312688] using wordTrace_append hprefix tailTrace_3312688
  have hstable : (prefixWord ++ tailWord_3312688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312688).length < 2 ^ (prefixWord ++ tailWord_3312688).sum := by decide
  have hdescent : baseEnd_3312688 < baseStart_3312688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312691 : List Nat := [1, 1, 1, 2, 4, 1, 1, 12]
def baseStart_3312691 : Nat := 118140960795 + 3312691 * 2 ^ 59
def prefixEnd_3312691 : Nat := 4983230072969 + 3 ^ 40 * 3312691 * 2
def baseEnd_3312691 : Nat := 63000101586051993145471

theorem tailTrace_3312691 : CollatzResearch.WordTrace tailWord_3312691 prefixEnd_3312691 63000101586051993145471 := by
  unfold tailWord_3312691
  simp only [CollatzResearch.WordTrace]
  refine ⟨120823766841693744425249927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80549177894462496283499951 120823766841693744425249927)
  ·
    refine ⟨181235650262540616637874891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120823766841693744425249927 181235650262540616637874891)
    ·
      refine ⟨271853475393810924956812337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181235650262540616637874891 271853475393810924956812337)
      ·
        refine ⟨203890106545358193717609253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271853475393810924956812337 203890106545358193717609253)
        ·
          refine ⟨38229394977254661322051735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203890106545358193717609253 38229394977254661322051735)
          ·
            refine ⟨57344092465881991983077603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38229394977254661322051735 57344092465881991983077603)
            ·
              refine ⟨86016138698822987974616405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57344092465881991983077603 86016138698822987974616405)
              ·
                refine ⟨63000101586051993145471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 86016138698822987974616405 63000101586051993145471)
                ·
                  rfl

theorem cell23_3312691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 12].length) (baseStart_3312691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312691 prefixEnd_3312691 := by exact prefixLift 3312691
  have htrace : WordTrace (prefixWord ++ tailWord_3312691) baseStart_3312691 baseEnd_3312691 := by
    simpa [prefixWord, tailWord_3312691, baseEnd_3312691] using wordTrace_append hprefix tailTrace_3312691
  have hstable : (prefixWord ++ tailWord_3312691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312691).length < 2 ^ (prefixWord ++ tailWord_3312691).sum := by decide
  have hdescent : baseEnd_3312691 < baseStart_3312691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312702 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3312702 : Nat := 118140960795 + 3312702 * 2 ^ 59
def prefixEnd_3312702 : Nat := 4983230072969 + 3 ^ 40 * 3312702 * 2
def baseEnd_3312702 : Nat := 1701008391110603271890167

theorem tailTrace_3312702 : CollatzResearch.WordTrace tailWord_3312702 prefixEnd_3312702 1701008391110603271890167 := by
  unfold tailWord_3312702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15103021005581736662987545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80549445363102595535933573 15103021005581736662987545)
  ·
    refine ⟨11327265754186302497240659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15103021005581736662987545 11327265754186302497240659)
    ·
      refine ⟨16990898631279453745860989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11327265754186302497240659 16990898631279453745860989)
      ·
        refine ⟨6371586986729795154697871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16990898631279453745860989 6371586986729795154697871)
        ·
          refine ⟨9557380480094692732046807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6371586986729795154697871 9557380480094692732046807)
          ·
            refine ⟨14336070720142039098070211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9557380480094692732046807 14336070720142039098070211)
            ·
              refine ⟨21504106080213058647105317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14336070720142039098070211 21504106080213058647105317)
              ·
                refine ⟨4032019890039948496332247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21504106080213058647105317 4032019890039948496332247)
                ·
                  refine ⟨6048029835059922744498371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032019890039948496332247 6048029835059922744498371)
                  ·
                    refine ⟨9072044752589884116747557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6048029835059922744498371 9072044752589884116747557)
                    ·
                      refine ⟨1701008391110603271890167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9072044752589884116747557 1701008391110603271890167)
                      ·
                        rfl

theorem cell23_3312702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3312702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312702 prefixEnd_3312702 := by exact prefixLift 3312702
  have htrace : WordTrace (prefixWord ++ tailWord_3312702) baseStart_3312702 baseEnd_3312702 := by
    simpa [prefixWord, tailWord_3312702, baseEnd_3312702] using wordTrace_append hprefix tailTrace_3312702
  have hstable : (prefixWord ++ tailWord_3312702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312702).length < 2 ^ (prefixWord ++ tailWord_3312702).sum := by decide
  have hdescent : baseEnd_3312702 < baseStart_3312702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312722 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_3312722 : Nat := 118140960795 + 3312722 * 2 ^ 59
def prefixEnd_3312722 : Nat := 4983230072969 + 3 ^ 40 * 3312722 * 2
def baseEnd_3312722 : Nat := 1701018660723693193640075

theorem tailTrace_3312722 : CollatzResearch.WordTrace tailWord_3312722 prefixEnd_3312722 1701018660723693193640075 := by
  unfold tailWord_3312722
  simp only [CollatzResearch.WordTrace]
  refine ⟨30206224376145359179907105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80549931669720957813085613 30206224376145359179907105)
  ·
    refine ⟨22654668282109019384930329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30206224376145359179907105 22654668282109019384930329)
    ·
      refine ⟨16991001211581764538697747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22654668282109019384930329 16991001211581764538697747)
      ·
        refine ⟨25486501817372646808046621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16991001211581764538697747 25486501817372646808046621)
        ·
          refine ⟨9557438181514742553017483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25486501817372646808046621 9557438181514742553017483)
          ·
            refine ⟨14336157272272113829526225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9557438181514742553017483 14336157272272113829526225)
            ·
              refine ⟨10752117954204085372144669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14336157272272113829526225 10752117954204085372144669)
              ·
                refine ⟨4032044232826532014554251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10752117954204085372144669 4032044232826532014554251)
                ·
                  refine ⟨6048066349239798021831377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032044232826532014554251 6048066349239798021831377)
                  ·
                    refine ⟨4536049761929848516373533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6048066349239798021831377 4536049761929848516373533)
                    ·
                      refine ⟨1701018660723693193640075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4536049761929848516373533 1701018660723693193640075)
                      ·
                        rfl

theorem cell23_3312722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_3312722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312722 prefixEnd_3312722 := by exact prefixLift 3312722
  have htrace : WordTrace (prefixWord ++ tailWord_3312722) baseStart_3312722 baseEnd_3312722 := by
    simpa [prefixWord, tailWord_3312722, baseEnd_3312722] using wordTrace_append hprefix tailTrace_3312722
  have hstable : (prefixWord ++ tailWord_3312722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312722).length < 2 ^ (prefixWord ++ tailWord_3312722).sum := by decide
  have hdescent : baseEnd_3312722 < baseStart_3312722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312735 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 4, 1, 3]
def baseStart_3312735 : Nat := 118140960795 + 3312735 * 2 ^ 59
def prefixEnd_3312735 : Nat := 4983230072969 + 3 ^ 40 * 3312735 * 2
def baseEnd_3312735 : Nat := 1701025335972201642777515

theorem tailTrace_3312735 : CollatzResearch.WordTrace tailWord_3312735 prefixEnd_3312735 1701025335972201642777515 := by
  unfold tailWord_3312735
  simp only [CollatzResearch.WordTrace]
  refine ⟨120825371653534339939851659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80550247769022893293234439 120825371653534339939851659)
  ·
    refine ⟨181238057480301509909777489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120825371653534339939851659 181238057480301509909777489)
    ·
      refine ⟨135928543110226132432333117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181238057480301509909777489 135928543110226132432333117)
      ·
        refine ⟨50973203666334799662124919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135928543110226132432333117 50973203666334799662124919)
        ·
          refine ⟨76459805499502199493187379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50973203666334799662124919 76459805499502199493187379)
          ·
            refine ⟨114689708249253299239781069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76459805499502199493187379 114689708249253299239781069)
            ·
              refine ⟨43008640593469987214917901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114689708249253299239781069 43008640593469987214917901)
              ·
                refine ⟨16128240222551245205594213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43008640593469987214917901 16128240222551245205594213)
                ·
                  refine ⟨3024045041728358476048915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16128240222551245205594213 3024045041728358476048915)
                  ·
                    refine ⟨4536067562592537714073373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3024045041728358476048915 4536067562592537714073373)
                    ·
                      refine ⟨1701025335972201642777515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4536067562592537714073373 1701025335972201642777515)
                      ·
                        rfl

theorem cell23_3312735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_3312735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312735 prefixEnd_3312735 := by exact prefixLift 3312735
  have htrace : WordTrace (prefixWord ++ tailWord_3312735) baseStart_3312735 baseEnd_3312735 := by
    simpa [prefixWord, tailWord_3312735, baseEnd_3312735] using wordTrace_append hprefix tailTrace_3312735
  have hstable : (prefixWord ++ tailWord_3312735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312735).length < 2 ^ (prefixWord ++ tailWord_3312735).sum := by decide
  have hdescent : baseEnd_3312735 < baseStart_3312735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312736 : List Nat := [2, 1, 1, 3, 2, 2, 5, 2, 1, 2, 2]
def baseStart_3312736 : Nat := 118140960795 + 3312736 * 2 ^ 59
def prefixEnd_3312736 : Nat := 4983230072969 + 3 ^ 40 * 3312736 * 2
def baseEnd_3312736 : Nat := 1701025849452856138865011

theorem tailTrace_3312736 : CollatzResearch.WordTrace tailWord_3312736 prefixEnd_3312736 1701025849452856138865011 := by
  unfold tailWord_3312736
  simp only [CollatzResearch.WordTrace]
  refine ⟨60412704063265358555319031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80550272084353811407092041 60412704063265358555319031)
  ·
    refine ⟨90619056094898037832978547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60412704063265358555319031 90619056094898037832978547)
    ·
      refine ⟨135928584142347056749467821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90619056094898037832978547 135928584142347056749467821)
      ·
        refine ⟨50973219053380146281050433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135928584142347056749467821 50973219053380146281050433)
        ·
          refine ⟨38229914290035109710787825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50973219053380146281050433 38229914290035109710787825)
          ·
            refine ⟨28672435717526332283090869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38229914290035109710787825 28672435717526332283090869)
            ·
              refine ⟨2688040848518093651539769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28672435717526332283090869 2688040848518093651539769)
              ·
                refine ⟨2016030636388570238654827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2688040848518093651539769 2016030636388570238654827)
                ·
                  refine ⟨3024045954582855357982241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016030636388570238654827 3024045954582855357982241)
                  ·
                    refine ⟨2268034465937141518486681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3024045954582855357982241 2268034465937141518486681)
                    ·
                      refine ⟨1701025849452856138865011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2268034465937141518486681 1701025849452856138865011)
                      ·
                        rfl

theorem cell23_3312736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_3312736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312736 prefixEnd_3312736 := by exact prefixLift 3312736
  have htrace : WordTrace (prefixWord ++ tailWord_3312736) baseStart_3312736 baseEnd_3312736 := by
    simpa [prefixWord, tailWord_3312736, baseEnd_3312736] using wordTrace_append hprefix tailTrace_3312736
  have hstable : (prefixWord ++ tailWord_3312736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312736).length < 2 ^ (prefixWord ++ tailWord_3312736).sum := by decide
  have hdescent : baseEnd_3312736 < baseStart_3312736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312752 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 2, 1, 3]
def baseStart_3312752 : Nat := 118140960795 + 3312752 * 2 ^ 59
def prefixEnd_3312752 : Nat := 4983230072969 + 3 ^ 40 * 3312752 * 2
def baseEnd_3312752 : Nat := 1701034065143328076264937

theorem tailTrace_3312752 : CollatzResearch.WordTrace tailWord_3312752 prefixEnd_3312752 1701034065143328076264937 := by
  unfold tailWord_3312752
  simp only [CollatzResearch.WordTrace]
  refine ⟨60412995847236375921610255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80550661129648501228813673 60412995847236375921610255)
  ·
    refine ⟨90619493770854563882415383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60412995847236375921610255 90619493770854563882415383)
    ·
      refine ⟨135929240656281845823623075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90619493770854563882415383 135929240656281845823623075)
      ·
        refine ⟨203893860984422768735434613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135929240656281845823623075 203893860984422768735434613)
        ·
          refine ⟨19115049467289634568946995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203893860984422768735434613 19115049467289634568946995)
          ·
            refine ⟨28672574200934451853420493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19115049467289634568946995 28672574200934451853420493)
            ·
              refine ⟨10752215325350419445032685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28672574200934451853420493 10752215325350419445032685)
              ·
                refine ⟨4032080747006407291887257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10752215325350419445032685 4032080747006407291887257)
                ·
                  refine ⟨3024060560254805468915443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4032080747006407291887257 3024060560254805468915443)
                  ·
                    refine ⟨4536090840382208203373165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3024060560254805468915443 4536090840382208203373165)
                    ·
                      refine ⟨1701034065143328076264937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4536090840382208203373165 1701034065143328076264937)
                      ·
                        rfl

theorem cell23_3312752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2, 1, 3].length) (baseStart_3312752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312752 prefixEnd_3312752 := by exact prefixLift 3312752
  have htrace : WordTrace (prefixWord ++ tailWord_3312752) baseStart_3312752 baseEnd_3312752 := by
    simpa [prefixWord, tailWord_3312752, baseEnd_3312752] using wordTrace_append hprefix tailTrace_3312752
  have hstable : (prefixWord ++ tailWord_3312752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312752).length < 2 ^ (prefixWord ++ tailWord_3312752).sum := by decide
  have hdescent : baseEnd_3312752 < baseStart_3312752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312766 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3312766 : Nat := 118140960795 + 3312766 * 2 ^ 59
def prefixEnd_3312766 : Nat := 4983230072969 + 3 ^ 40 * 3312766 * 2
def baseEnd_3312766 : Nat := 1701041253872491021489873

theorem tailTrace_3312766 : CollatzResearch.WordTrace tailWord_3312766 prefixEnd_3312766 1701041253872491021489873 := by
  unfold tailWord_3312766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15103312789552754029278769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80551001544281354822820101 15103312789552754029278769)
  ·
    refine ⟨11327484592164565521959077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15103312789552754029278769 11327484592164565521959077)
    ·
      refine ⟨2123903361030856035367327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11327484592164565521959077 2123903361030856035367327)
      ·
        refine ⟨3185855041546284053050991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123903361030856035367327 3185855041546284053050991)
        ·
          refine ⟨4778782562319426079576487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185855041546284053050991 4778782562319426079576487)
          ·
            refine ⟨7168173843479139119364731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778782562319426079576487 7168173843479139119364731)
            ·
              refine ⟨10752260765218708679047097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7168173843479139119364731 10752260765218708679047097)
              ·
                refine ⟨8064195573914031509285323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10752260765218708679047097 8064195573914031509285323)
                ·
                  refine ⟨12096293360871047263927985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8064195573914031509285323 12096293360871047263927985)
                  ·
                    refine ⟨9072220020653285447945989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12096293360871047263927985 9072220020653285447945989)
                    ·
                      refine ⟨1701041253872491021489873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9072220020653285447945989 1701041253872491021489873)
                      ·
                        rfl

theorem cell23_3312766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3312766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312766 prefixEnd_3312766 := by exact prefixLift 3312766
  have htrace : WordTrace (prefixWord ++ tailWord_3312766) baseStart_3312766 baseEnd_3312766 := by
    simpa [prefixWord, tailWord_3312766, baseEnd_3312766] using wordTrace_append hprefix tailTrace_3312766
  have hstable : (prefixWord ++ tailWord_3312766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312766).length < 2 ^ (prefixWord ++ tailWord_3312766).sum := by decide
  have hdescent : baseEnd_3312766 < baseStart_3312766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312802 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3312802 : Nat := 118140960795 + 3312802 * 2 ^ 59
def prefixEnd_3312802 : Nat := 4983230072969 + 3 ^ 40 * 3312802 * 2
def baseEnd_3312802 : Nat := 567019913058684293546569

theorem tailTrace_3312802 : CollatzResearch.WordTrace tailWord_3312802 prefixEnd_3312802 567019913058684293546569 := by
  unfold tailWord_3312802
  simp only [CollatzResearch.WordTrace]
  refine ⟨30206953836072902595635165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80551876896194406921693773 30206953836072902595635165)
  ·
    refine ⟨11327607688527338473363187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30206953836072902595635165 11327607688527338473363187)
    ·
      refine ⟨16991411532791007710044781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11327607688527338473363187 16991411532791007710044781)
      ·
        refine ⟨6371779324796627891266793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16991411532791007710044781 6371779324796627891266793)
        ·
          refine ⟨4778834493597470918450095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6371779324796627891266793 4778834493597470918450095)
          ·
            refine ⟨7168251740396206377675143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778834493597470918450095 7168251740396206377675143)
            ·
              refine ⟨10752377610594309566512715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7168251740396206377675143 10752377610594309566512715)
              ·
                refine ⟨16128566415891464349769073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10752377610594309566512715 16128566415891464349769073)
                ·
                  refine ⟨12096424811918598262326805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16128566415891464349769073 12096424811918598262326805)
                  ·
                    refine ⟨567019913058684293546569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12096424811918598262326805 567019913058684293546569)
                    ·
                      rfl

theorem cell23_3312802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3312802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312802 prefixEnd_3312802 := by exact prefixLift 3312802
  have htrace : WordTrace (prefixWord ++ tailWord_3312802) baseStart_3312802 baseEnd_3312802 := by
    simpa [prefixWord, tailWord_3312802, baseEnd_3312802] using wordTrace_append hprefix tailTrace_3312802
  have hstable : (prefixWord ++ tailWord_3312802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312802).length < 2 ^ (prefixWord ++ tailWord_3312802).sum := by decide
  have hdescent : baseEnd_3312802 < baseStart_3312802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312805 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_3312805 : Nat := 118140960795 + 3312805 * 2 ^ 59
def prefixEnd_3312805 : Nat := 4983230072969 + 3 ^ 40 * 3312805 * 2
def baseEnd_3312805 : Nat := 1701061279618016368902193

theorem tailTrace_3312805 : CollatzResearch.WordTrace tailWord_3312805 prefixEnd_3312805 1701061279618016368902193 := by
  unfold tailWord_3312805
  simp only [CollatzResearch.WordTrace]
  refine ⟨120827924763280741894899869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80551949842187161263266579 120827924763280741894899869)
  ·
    refine ⟨45310471786230278210587451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120827924763280741894899869 45310471786230278210587451)
    ·
      refine ⟨67965707679345417315881177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45310471786230278210587451 67965707679345417315881177)
      ·
        refine ⟨50974280759509062986910883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67965707679345417315881177 50974280759509062986910883)
        ·
          refine ⟨76461421139263594480366325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50974280759509062986910883 76461421139263594480366325)
          ·
            refine ⟨7168258231805961982534343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76461421139263594480366325 7168258231805961982534343)
            ·
              refine ⟨10752387347708942973801515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7168258231805961982534343 10752387347708942973801515)
              ·
                refine ⟨16128581021563414460702273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10752387347708942973801515 16128581021563414460702273)
                ·
                  refine ⟨12096435766172560845526705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16128581021563414460702273 12096435766172560845526705)
                  ·
                    refine ⟨9072326824629420634145029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12096435766172560845526705 9072326824629420634145029)
                    ·
                      refine ⟨1701061279618016368902193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9072326824629420634145029 1701061279618016368902193)
                      ·
                        rfl

theorem cell23_3312805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_3312805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312805 prefixEnd_3312805 := by exact prefixLift 3312805
  have htrace : WordTrace (prefixWord ++ tailWord_3312805) baseStart_3312805 baseEnd_3312805 := by
    simpa [prefixWord, tailWord_3312805, baseEnd_3312805] using wordTrace_append hprefix tailTrace_3312805
  have hstable : (prefixWord ++ tailWord_3312805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312805).length < 2 ^ (prefixWord ++ tailWord_3312805).sum := by decide
  have hdescent : baseEnd_3312805 < baseStart_3312805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312835 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 1, 7, 2]
def baseStart_3312835 : Nat := 118140960795 + 3312835 * 2 ^ 59
def prefixEnd_3312835 : Nat := 4983230072969 + 3 ^ 40 * 3312835 * 2
def baseEnd_3312835 : Nat := 1701076684037651251527055

theorem tailTrace_3312835 : CollatzResearch.WordTrace tailWord_3312835 prefixEnd_3312835 1701076684037651251527055 := by
  unfold tailWord_3312835
  simp only [CollatzResearch.WordTrace]
  refine ⟨120829018953172057018491959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80552679302114704678994639 120829018953172057018491959)
  ·
    refine ⟨181243528429758085527737939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120829018953172057018491959 181243528429758085527737939)
    ·
      refine ⟨271865292644637128291606909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181243528429758085527737939 271865292644637128291606909)
      ·
        refine ⟨101949484741738923109352591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271865292644637128291606909 101949484741738923109352591)
        ·
          refine ⟨152924227112608384664028887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101949484741738923109352591 152924227112608384664028887)
          ·
            refine ⟨229386340668912576996043331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152924227112608384664028887 229386340668912576996043331)
            ·
              refine ⟨344079511003368865494064997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229386340668912576996043331 344079511003368865494064997)
              ·
                refine ⟨64514908313131662280137187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344079511003368865494064997 64514908313131662280137187)
                ·
                  refine ⟨96772362469697493420205781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64514908313131662280137187 96772362469697493420205781)
                  ·
                    refine ⟨2268102245383535002036073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 96772362469697493420205781 2268102245383535002036073)
                    ·
                      refine ⟨1701076684037651251527055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2268102245383535002036073 1701076684037651251527055)
                      ·
                        rfl

theorem cell23_3312835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 7, 2].length) (baseStart_3312835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312835 prefixEnd_3312835 := by exact prefixLift 3312835
  have htrace : WordTrace (prefixWord ++ tailWord_3312835) baseStart_3312835 baseEnd_3312835 := by
    simpa [prefixWord, tailWord_3312835, baseEnd_3312835] using wordTrace_append hprefix tailTrace_3312835
  have hstable : (prefixWord ++ tailWord_3312835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312835).length < 2 ^ (prefixWord ++ tailWord_3312835).sum := by decide
  have hdescent : baseEnd_3312835 < baseStart_3312835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312865 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_3312865 : Nat := 118140960795 + 3312865 * 2 ^ 59
def prefixEnd_3312865 : Nat := 4983230072969 + 3 ^ 40 * 3312865 * 2
def baseEnd_3312865 : Nat := 1701092088457286134151917

theorem tailTrace_3312865 : CollatzResearch.WordTrace tailWord_3312865 prefixEnd_3312865 1701092088457286134151917 := by
  unfold tailWord_3312865
  simp only [CollatzResearch.WordTrace]
  refine ⟨120830113143063372142084049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80553408762042248094722699 120830113143063372142084049)
  ·
    refine ⟨90622584857297529106563037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120830113143063372142084049 90622584857297529106563037)
    ·
      refine ⟨33983469321486573414961139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90622584857297529106563037 33983469321486573414961139)
      ·
        refine ⟨50975203982229860122441709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33983469321486573414961139 50975203982229860122441709)
        ·
          refine ⟨19115701493336197545915641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50975203982229860122441709 19115701493336197545915641)
          ·
            refine ⟨14336776120002148159436731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19115701493336197545915641 14336776120002148159436731)
            ·
              refine ⟨21505164180003222239155097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14336776120002148159436731 21505164180003222239155097)
              ·
                refine ⟨16128873135002416679366323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21505164180003222239155097 16128873135002416679366323)
                ·
                  refine ⟨24193309702503625019049485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16128873135002416679366323 24193309702503625019049485)
                  ·
                    refine ⟨9072491138438859382143557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24193309702503625019049485 9072491138438859382143557)
                    ·
                      refine ⟨1701092088457286134151917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9072491138438859382143557 1701092088457286134151917)
                      ·
                        rfl

theorem cell23_3312865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_3312865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312865 prefixEnd_3312865 := by exact prefixLift 3312865
  have htrace : WordTrace (prefixWord ++ tailWord_3312865) baseStart_3312865 baseEnd_3312865 := by
    simpa [prefixWord, tailWord_3312865, baseEnd_3312865] using wordTrace_append hprefix tailTrace_3312865
  have hstable : (prefixWord ++ tailWord_3312865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312865).length < 2 ^ (prefixWord ++ tailWord_3312865).sum := by decide
  have hdescent : baseEnd_3312865 < baseStart_3312865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312905 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 6]
def baseStart_3312905 : Nat := 118140960795 + 3312905 * 2 ^ 59
def prefixEnd_3312905 : Nat := 4983230072969 + 3 ^ 40 * 3312905 * 2
def baseEnd_3312905 : Nat := 189012514187051775294637

theorem tailTrace_3312905 : CollatzResearch.WordTrace tailWord_3312905 prefixEnd_3312905 189012514187051775294637 := by
  unfold tailWord_3312905
  simp only [CollatzResearch.WordTrace]
  refine ⟨120831572062918458973540169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80554381375278972649026779 120831572062918458973540169)
  ·
    refine ⟨90623679047188844230155127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120831572062918458973540169 90623679047188844230155127)
    ·
      refine ⟨135935518570783266345232691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90623679047188844230155127 135935518570783266345232691)
      ·
        refine ⟨203903277856174899517849037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135935518570783266345232691 203903277856174899517849037)
        ·
          refine ⟨76463729196065587319193389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203903277856174899517849037 76463729196065587319193389)
          ·
            refine ⟨28673898448524595244697521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76463729196065587319193389 28673898448524595244697521)
            ·
              refine ⟨21505423836393446433523141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28673898448524595244697521 21505423836393446433523141)
              ·
                refine ⟨4032266969323771206285589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21505423836393446433523141 4032266969323771206285589)
                ·
                  refine ⟨189012514187051775294637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4032266969323771206285589 189012514187051775294637)
                  ·
                    rfl

theorem cell23_3312905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 6].length) (baseStart_3312905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312905 prefixEnd_3312905 := by exact prefixLift 3312905
  have htrace : WordTrace (prefixWord ++ tailWord_3312905) baseStart_3312905 baseEnd_3312905 := by
    simpa [prefixWord, tailWord_3312905, baseEnd_3312905] using wordTrace_append hprefix tailTrace_3312905
  have hstable : (prefixWord ++ tailWord_3312905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312905).length < 2 ^ (prefixWord ++ tailWord_3312905).sum := by decide
  have hdescent : baseEnd_3312905 < baseStart_3312905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312922 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 6]
def baseStart_3312922 : Nat := 118140960795 + 3312922 * 2 ^ 59
def prefixEnd_3312922 : Nat := 4983230072969 + 3 ^ 40 * 3312922 * 2
def baseEnd_3312922 : Nat := 189013484094954712348795

theorem tailTrace_3312922 : CollatzResearch.WordTrace tailWord_3312922 prefixEnd_3312922 189013484094954712348795 := by
  unfold tailWord_3312922
  simp only [CollatzResearch.WordTrace]
  refine ⟨30208048025964217719227255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80554794735904580584606013 30208048025964217719227255)
  ·
    refine ⟨45312072038946326578840883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30208048025964217719227255 45312072038946326578840883)
    ·
      refine ⟨67968108058419489868261325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45312072038946326578840883 67968108058419489868261325)
      ·
        refine ⟨25488040521907308700597997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67968108058419489868261325 25488040521907308700597997)
        ·
          refine ⟨9558015195715240762724249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25488040521907308700597997 9558015195715240762724249)
          ·
            refine ⟨7168511396786430572043187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9558015195715240762724249 7168511396786430572043187)
            ·
              refine ⟨10752767095179645858064781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7168511396786430572043187 10752767095179645858064781)
              ·
                refine ⟨4032287660692367196774293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10752767095179645858064781 4032287660692367196774293)
                ·
                  refine ⟨189013484094954712348795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4032287660692367196774293 189013484094954712348795)
                  ·
                    rfl

theorem cell23_3312922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_3312922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312922 prefixEnd_3312922 := by exact prefixLift 3312922
  have htrace : WordTrace (prefixWord ++ tailWord_3312922) baseStart_3312922 baseEnd_3312922 := by
    simpa [prefixWord, tailWord_3312922, baseEnd_3312922] using wordTrace_append hprefix tailTrace_3312922
  have hstable : (prefixWord ++ tailWord_3312922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312922).length < 2 ^ (prefixWord ++ tailWord_3312922).sum := by decide
  have hdescent : baseEnd_3312922 < baseStart_3312922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312959 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 2, 3, 2]
def baseStart_3312959 : Nat := 118140960795 + 3312959 * 2 ^ 59
def prefixEnd_3312959 : Nat := 4983230072969 + 3 ^ 40 * 3312959 * 2
def baseEnd_3312959 : Nat := 1701140355638808766376485

theorem tailTrace_3312959 : CollatzResearch.WordTrace tailWord_3312959 prefixEnd_3312959 1701140355638808766376485 := by
  unfold tailWord_3312959
  simp only [CollatzResearch.WordTrace]
  refine ⟨120833541604722826196005931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80555694403148550797337287 120833541604722826196005931)
  ·
    refine ⟨181250312407084239294008897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120833541604722826196005931 181250312407084239294008897)
    ·
      refine ⟨135937734305313179470506673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181250312407084239294008897 135937734305313179470506673)
      ·
        refine ⟨101953300728984884602880005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135937734305313179470506673 101953300728984884602880005)
        ·
          refine ⟨19116243886684665863040001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101953300728984884602880005 19116243886684665863040001)
          ·
            refine ⟨14337182915013499397280001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19116243886684665863040001 14337182915013499397280001)
            ·
              refine ⟨10752887186260124547960001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14337182915013499397280001 10752887186260124547960001)
              ·
                refine ⟨8064665389695093410970001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10752887186260124547960001 8064665389695093410970001)
                ·
                  refine ⟨6048499042271320058227501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8064665389695093410970001 6048499042271320058227501)
                  ·
                    refine ⟨2268187140851745021835313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6048499042271320058227501 2268187140851745021835313)
                    ·
                      refine ⟨1701140355638808766376485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2268187140851745021835313 1701140355638808766376485)
                      ·
                        rfl

theorem cell23_3312959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 3, 2].length) (baseStart_3312959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312959 prefixEnd_3312959 := by exact prefixLift 3312959
  have htrace : WordTrace (prefixWord ++ tailWord_3312959) baseStart_3312959 baseEnd_3312959 := by
    simpa [prefixWord, tailWord_3312959, baseEnd_3312959] using wordTrace_append hprefix tailTrace_3312959
  have hstable : (prefixWord ++ tailWord_3312959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312959).length < 2 ^ (prefixWord ++ tailWord_3312959).sum := by decide
  have hdescent : baseEnd_3312959 < baseStart_3312959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312972 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3312972 : Nat := 118140960795 + 3312972 * 2 ^ 59
def prefixEnd_3312972 : Nat := 4983230072969 + 3 ^ 40 * 3312972 * 2
def baseEnd_3312972 : Nat := 1701147030887317215513925

theorem tailTrace_3312972 : CollatzResearch.WordTrace tailWord_3312972 prefixEnd_3312972 1701147030887317215513925 := by
  unfold tailWord_3312972
  simp only [CollatzResearch.WordTrace]
  refine ⟨60417007876837864708114585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80556010502450486277486113 60417007876837864708114585)
  ·
    refine ⟨45312755907628398531085939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60417007876837864708114585 45312755907628398531085939)
    ·
      refine ⟨67969133861442597796628909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45312755907628398531085939 67969133861442597796628909)
      ·
        refine ⟨25488425198040974173735841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67969133861442597796628909 25488425198040974173735841)
        ·
          refine ⟨19116318898530730630301881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25488425198040974173735841 19116318898530730630301881)
          ·
            refine ⟨14337239173898047972726411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19116318898530730630301881 14337239173898047972726411)
            ·
              refine ⟨21505858760847071959089617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14337239173898047972726411 21505858760847071959089617)
              ·
                refine ⟨16129394070635303969317213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21505858760847071959089617 16129394070635303969317213)
                ·
                  refine ⟨6048522776488238988493955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16129394070635303969317213 6048522776488238988493955)
                  ·
                    refine ⟨9072784164732358482740933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6048522776488238988493955 9072784164732358482740933)
                    ·
                      refine ⟨1701147030887317215513925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9072784164732358482740933 1701147030887317215513925)
                      ·
                        rfl

theorem cell23_3312972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3312972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312972 prefixEnd_3312972 := by exact prefixLift 3312972
  have htrace : WordTrace (prefixWord ++ tailWord_3312972) baseStart_3312972 baseEnd_3312972 := by
    simpa [prefixWord, tailWord_3312972, baseEnd_3312972] using wordTrace_append hprefix tailTrace_3312972
  have hstable : (prefixWord ++ tailWord_3312972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312972).length < 2 ^ (prefixWord ++ tailWord_3312972).sum := by decide
  have hdescent : baseEnd_3312972 < baseStart_3312972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312985 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 6]
def baseStart_3312985 : Nat := 118140960795 + 3312985 * 2 ^ 59
def prefixEnd_3312985 : Nat := 4983230072969 + 3 ^ 40 * 3312985 * 2
def baseEnd_3312985 : Nat := 1701153706135825664651365

theorem tailTrace_3312985 : CollatzResearch.WordTrace tailWord_3312985 prefixEnd_3312985 1701153706135825664651365 := by
  unfold tailWord_3312985
  simp only [CollatzResearch.WordTrace]
  refine ⟨120834489902628632636452409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80556326601752421757634939 120834489902628632636452409)
  ·
    refine ⟨90625867426971474477339307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120834489902628632636452409 90625867426971474477339307)
    ·
      refine ⟨135938801140457211716008961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90625867426971474477339307 135938801140457211716008961)
      ·
        refine ⟨101954100855342908787006721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135938801140457211716008961 101954100855342908787006721)
        ·
          refine ⟨76465575641507181590255041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101954100855342908787006721 76465575641507181590255041)
          ·
            refine ⟨57349181731130386192691281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76465575641507181590255041 57349181731130386192691281)
            ·
              refine ⟨43011886298347789644518461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57349181731130386192691281 43011886298347789644518461)
              ·
                refine ⟨16129457361880421116694423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43011886298347789644518461 16129457361880421116694423)
                ·
                  refine ⟨24194186042820631675041635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16129457361880421116694423 24194186042820631675041635)
                  ·
                    refine ⟨36291279064230947512562453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24194186042820631675041635 36291279064230947512562453)
                    ·
                      refine ⟨1701153706135825664651365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36291279064230947512562453 1701153706135825664651365)
                      ·
                        rfl

theorem cell23_3312985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_3312985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3312985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3312985 prefixEnd_3312985 := by exact prefixLift 3312985
  have htrace : WordTrace (prefixWord ++ tailWord_3312985) baseStart_3312985 baseEnd_3312985 := by
    simpa [prefixWord, tailWord_3312985, baseEnd_3312985] using wordTrace_append hprefix tailTrace_3312985
  have hstable : (prefixWord ++ tailWord_3312985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312985).length < 2 ^ (prefixWord ++ tailWord_3312985).sum := by decide
  have hdescent : baseEnd_3312985 < baseStart_3312985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313026 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3313026 : Nat := 118140960795 + 3313026 * 2 ^ 59
def prefixEnd_3313026 : Nat := 4983230072969 + 3 ^ 40 * 3313026 * 2
def baseEnd_3313026 : Nat := 1701174758842660004238677

theorem tailTrace_3313026 : CollatzResearch.WordTrace tailWord_3313026 prefixEnd_3313026 1701174758842660004238677 := by
  unfold tailWord_3313026
  simp only [CollatzResearch.WordTrace]
  refine ⟨30208996323870024159673733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80557323530320064425796621 30208996323870024159673733)
  ·
    refine ⟨5664186810725629529938825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30208996323870024159673733 5664186810725629529938825)
    ·
      refine ⟨4248140108044222147454119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5664186810725629529938825 4248140108044222147454119)
      ·
        refine ⟨6372210162066333221181179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248140108044222147454119 6372210162066333221181179)
        ·
          refine ⟨9558315243099499831771769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6372210162066333221181179 9558315243099499831771769)
          ·
            refine ⟨7168736432324624873828827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9558315243099499831771769 7168736432324624873828827)
            ·
              refine ⟨10753104648486937310743241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7168736432324624873828827 10753104648486937310743241)
              ·
                refine ⟨8064828486365202983057431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10753104648486937310743241 8064828486365202983057431)
                ·
                  refine ⟨12097242729547804474586147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8064828486365202983057431 12097242729547804474586147)
                  ·
                    refine ⟨18145864094321706711879221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12097242729547804474586147 18145864094321706711879221)
                    ·
                      refine ⟨1701174758842660004238677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18145864094321706711879221 1701174758842660004238677)
                      ·
                        rfl

theorem cell23_3313026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3313026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313026 prefixEnd_3313026 := by exact prefixLift 3313026
  have htrace : WordTrace (prefixWord ++ tailWord_3313026) baseStart_3313026 baseEnd_3313026 := by
    simpa [prefixWord, tailWord_3313026, baseEnd_3313026] using wordTrace_append hprefix tailTrace_3313026
  have hstable : (prefixWord ++ tailWord_3313026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313026).length < 2 ^ (prefixWord ++ tailWord_3313026).sum := by decide
  have hdescent : baseEnd_3313026 < baseStart_3313026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313102 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_3313102 : Nat := 118140960795 + 3313102 * 2 ^ 59
def prefixEnd_3313102 : Nat := 4983230072969 + 3 ^ 40 * 3313102 * 2
def baseEnd_3313102 : Nat := 189023753708044634098703

theorem tailTrace_3313102 : CollatzResearch.WordTrace tailWord_3313102 prefixEnd_3313102 189023753708044634098703 := by
  unfold tailWord_3313102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15104844655400595202307695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80559171495469841078974373 15104844655400595202307695)
  ·
    refine ⟨22657266983100892803461543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15104844655400595202307695 22657266983100892803461543)
    ·
      refine ⟨33985900474651339205192315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22657266983100892803461543 33985900474651339205192315)
      ·
        refine ⟨50978850711977008807788473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33985900474651339205192315 50978850711977008807788473)
        ·
          refine ⟨38234138033982756605841355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50978850711977008807788473 38234138033982756605841355)
          ·
            refine ⟨57351207050974134908762033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38234138033982756605841355 57351207050974134908762033)
            ·
              refine ⟨43013405288230601181571525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57351207050974134908762033 43013405288230601181571525)
              ·
                refine ⟨8065013491543237721544661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43013405288230601181571525 8065013491543237721544661)
                ·
                  refine ⟨189023753708044634098703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8065013491543237721544661 189023753708044634098703)
                  ·
                    rfl

theorem cell23_3313102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_3313102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313102 prefixEnd_3313102 := by exact prefixLift 3313102
  have htrace : WordTrace (prefixWord ++ tailWord_3313102) baseStart_3313102 baseEnd_3313102 := by
    simpa [prefixWord, tailWord_3313102, baseEnd_3313102] using wordTrace_append hprefix tailTrace_3313102
  have hstable : (prefixWord ++ tailWord_3313102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313102).length < 2 ^ (prefixWord ++ tailWord_3313102).sum := by decide
  have hdescent : baseEnd_3313102 < baseStart_3313102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313119 : List Nat := [1, 1, 2, 3, 3, 1, 2, 5, 5]
def baseStart_3313119 : Nat := 118140960795 + 3313119 * 2 ^ 59
def prefixEnd_3313119 : Nat := 4983230072969 + 3 ^ 40 * 3313119 * 2
def baseEnd_3313119 : Nat := 189024723615947571152861

theorem tailTrace_3313119 : CollatzResearch.WordTrace tailWord_3313119 prefixEnd_3313119 189024723615947571152861 := by
  unfold tailWord_3313119
  simp only [CollatzResearch.WordTrace]
  refine ⟨120839377284143173521830411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80559584856095449014553607 120839377284143173521830411)
  ·
    refine ⟨181259065926214760282745617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120839377284143173521830411 181259065926214760282745617)
    ·
      refine ⟨135944299444661070212059213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181259065926214760282745617 135944299444661070212059213)
      ·
        refine ⟨50979112291747901329522205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135944299444661070212059213 50979112291747901329522205)
        ·
          refine ⟨19117167109405462998570827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50979112291747901329522205 19117167109405462998570827)
          ·
            refine ⟨28675750664108194497856241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19117167109405462998570827 28675750664108194497856241)
            ·
              refine ⟨21506812998081145873392181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28675750664108194497856241 21506812998081145873392181)
              ·
                refine ⟨2016263718570107425630517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21506812998081145873392181 2016263718570107425630517)
                ·
                  refine ⟨189024723615947571152861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2016263718570107425630517 189024723615947571152861)
                  ·
                    rfl

theorem cell23_3313119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 5].length) (baseStart_3313119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313119 prefixEnd_3313119 := by exact prefixLift 3313119
  have htrace : WordTrace (prefixWord ++ tailWord_3313119) baseStart_3313119 baseEnd_3313119 := by
    simpa [prefixWord, tailWord_3313119, baseEnd_3313119] using wordTrace_append hprefix tailTrace_3313119
  have hstable : (prefixWord ++ tailWord_3313119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313119).length < 2 ^ (prefixWord ++ tailWord_3313119).sum := by decide
  have hdescent : baseEnd_3313119 < baseStart_3313119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313130 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_3313130 : Nat := 118140960795 + 3313130 * 2 ^ 59
def prefixEnd_3313130 : Nat := 4983230072969 + 3 ^ 40 * 3313130 * 2
def baseEnd_3313130 : Nat := 1701228160830727597338199

theorem tailTrace_3313130 : CollatzResearch.WordTrace tailWord_3313130 prefixEnd_3313130 1701228160830727597338199 := by
  unfold tailWord_3313130
  simp only [CollatzResearch.WordTrace]
  refine ⟨30209944621775830600120211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80559852324735548266987229 30209944621775830600120211)
  ·
    refine ⟨45314916932663745900180317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30209944621775830600120211 45314916932663745900180317)
    ·
      refine ⟨16993093849748904712567619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45314916932663745900180317 16993093849748904712567619)
      ·
        refine ⟨25489640774623357068851429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16993093849748904712567619 25489640774623357068851429)
        ·
          refine ⟨4779307645241879450409643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25489640774623357068851429 4779307645241879450409643)
          ·
            refine ⟨7168961467862819175614465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4779307645241879450409643 7168961467862819175614465)
            ·
              refine ⟨5376721100897114381710849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7168961467862819175614465 5376721100897114381710849)
              ·
                refine ⟨4032540825672835786283137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5376721100897114381710849 4032540825672835786283137)
                ·
                  refine ⟨3024405619254626839712353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4032540825672835786283137 3024405619254626839712353)
                  ·
                    refine ⟨2268304214440970129784265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3024405619254626839712353 2268304214440970129784265)
                    ·
                      refine ⟨1701228160830727597338199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2268304214440970129784265 1701228160830727597338199)
                      ·
                        rfl

theorem cell23_3313130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_3313130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313130 prefixEnd_3313130 := by exact prefixLift 3313130
  have htrace : WordTrace (prefixWord ++ tailWord_3313130) baseStart_3313130 baseEnd_3313130 := by
    simpa [prefixWord, tailWord_3313130, baseEnd_3313130] using wordTrace_append hprefix tailTrace_3313130
  have hstable : (prefixWord ++ tailWord_3313130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313130).length < 2 ^ (prefixWord ++ tailWord_3313130).sum := by decide
  have hdescent : baseEnd_3313130 < baseStart_3313130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313132 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_3313132 : Nat := 118140960795 + 3313132 * 2 ^ 59
def prefixEnd_3313132 : Nat := 4983230072969 + 3 ^ 40 * 3313132 * 2
def baseEnd_3313132 : Nat := 567076395930678863171063

theorem tailTrace_3313132 : CollatzResearch.WordTrace tailWord_3313132 prefixEnd_3313132 567076395930678863171063 := by
  unfold tailWord_3313132
  simp only [CollatzResearch.WordTrace]
  refine ⟨60419925716548038371026825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80559900955397384494702433 60419925716548038371026825)
  ·
    refine ⟨45314944287411028778270119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60419925716548038371026825 45314944287411028778270119)
    ·
      refine ⟨67972416431116543167405179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45314944287411028778270119 67972416431116543167405179)
      ·
        refine ⟨101958624646674814751107769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67972416431116543167405179 101958624646674814751107769)
        ·
          refine ⟨76468968485006111063330827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101958624646674814751107769 76468968485006111063330827)
          ·
            refine ⟨114703452727509166594996241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76468968485006111063330827 114703452727509166594996241)
            ·
              refine ⟨86027589545631874946247181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114703452727509166594996241 86027589545631874946247181)
              ·
                refine ⟨32260346079611953104842693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86027589545631874946247181 32260346079611953104842693)
                ·
                  refine ⟨6048814889927241207158005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32260346079611953104842693 6048814889927241207158005)
                  ·
                    refine ⟨567076395930678863171063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6048814889927241207158005 567076395930678863171063)
                    ·
                      rfl

theorem cell23_3313132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_3313132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313132 prefixEnd_3313132 := by exact prefixLift 3313132
  have htrace : WordTrace (prefixWord ++ tailWord_3313132) baseStart_3313132 baseEnd_3313132 := by
    simpa [prefixWord, tailWord_3313132, baseEnd_3313132] using wordTrace_append hprefix tailTrace_3313132
  have hstable : (prefixWord ++ tailWord_3313132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313132).length < 2 ^ (prefixWord ++ tailWord_3313132).sum := by decide
  have hdescent : baseEnd_3313132 < baseStart_3313132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313136 : List Nat := [2, 1, 1, 1, 3, 4, 4, 2, 5]
def baseStart_3313136 : Nat := 118140960795 + 3313136 * 2 ^ 59
def prefixEnd_3313136 : Nat := 4983230072969 + 3 ^ 40 * 3313136 * 2
def baseEnd_3313136 : Nat := 189025693523850508207019

theorem tailTrace_3313136 : CollatzResearch.WordTrace tailWord_3313136 prefixEnd_3313136 189025693523850508207019 := by
  unfold tailWord_3313136
  simp only [CollatzResearch.WordTrace]
  refine ⟨60419998662540792712599631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80559998216721056950132841 60419998662540792712599631)
  ·
    refine ⟨90629997993811189068899447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60419998662540792712599631 90629997993811189068899447)
    ·
      refine ⟨135944996990716783603349171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90629997993811189068899447 135944996990716783603349171)
      ·
        refine ⟨203917495486075175405023757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135944996990716783603349171 203917495486075175405023757)
        ·
          refine ⟨76469060807278190776883909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203917495486075175405023757 76469060807278190776883909)
          ·
            refine ⟨14337948901364660770665733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76469060807278190776883909 14337948901364660770665733)
            ·
              refine ⟨2688365419005873894499825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14337948901364660770665733 2688365419005873894499825)
              ·
                refine ⟨2016274064254405420874869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2688365419005873894499825 2016274064254405420874869)
                ·
                  refine ⟨189025693523850508207019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2016274064254405420874869 189025693523850508207019)
                  ·
                    rfl

theorem cell23_3313136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 5].length) (baseStart_3313136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313136 prefixEnd_3313136 := by exact prefixLift 3313136
  have htrace : WordTrace (prefixWord ++ tailWord_3313136) baseStart_3313136 baseEnd_3313136 := by
    simpa [prefixWord, tailWord_3313136, baseEnd_3313136] using wordTrace_append hprefix tailTrace_3313136
  have hstable : (prefixWord ++ tailWord_3313136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313136).length < 2 ^ (prefixWord ++ tailWord_3313136).sum := by decide
  have hdescent : baseEnd_3313136 < baseStart_3313136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313169 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 1, 6, 2]
def baseStart_3313169 : Nat := 118140960795 + 3313169 * 2 ^ 59
def prefixEnd_3313169 : Nat := 4983230072969 + 3 ^ 40 * 3313169 * 2
def baseEnd_3313169 : Nat := 1701248186576252944750519

theorem tailTrace_3313169 : CollatzResearch.WordTrace tailWord_3313169 prefixEnd_3313169 1701248186576252944750519 := by
  unfold tailWord_3313169
  simp only [CollatzResearch.WordTrace]
  refine ⟨120841200933962032061150561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80560800622641354707433707 120841200933962032061150561)
  ·
    refine ⟨90630900700471524045862921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120841200933962032061150561 90630900700471524045862921)
    ·
      refine ⟨67973175525353643034397191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90630900700471524045862921 67973175525353643034397191)
      ·
        refine ⟨101959763288030464551595787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67973175525353643034397191 101959763288030464551595787)
        ·
          refine ⟨152939644932045696827393681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101959763288030464551595787 152939644932045696827393681)
          ·
            refine ⟨114704733699034272620545261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152939644932045696827393681 114704733699034272620545261)
            ·
              refine ⟨43014275137137852232704473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114704733699034272620545261 43014275137137852232704473)
              ·
                refine ⟨32260706352853389174528355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43014275137137852232704473 32260706352853389174528355)
                ·
                  refine ⟨48391059529280083761792533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32260706352853389174528355 48391059529280083761792533)
                  ·
                    refine ⟨2268330915435003926334025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48391059529280083761792533 2268330915435003926334025)
                    ·
                      refine ⟨1701248186576252944750519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2268330915435003926334025 1701248186576252944750519)
                      ·
                        rfl

theorem cell23_3313169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 6, 2].length) (baseStart_3313169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313169 prefixEnd_3313169 := by exact prefixLift 3313169
  have htrace : WordTrace (prefixWord ++ tailWord_3313169) baseStart_3313169 baseEnd_3313169 := by
    simpa [prefixWord, tailWord_3313169, baseEnd_3313169] using wordTrace_append hprefix tailTrace_3313169
  have hstable : (prefixWord ++ tailWord_3313169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313169).length < 2 ^ (prefixWord ++ tailWord_3313169).sum := by decide
  have hdescent : baseEnd_3313169 < baseStart_3313169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313186 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_3313186 : Nat := 118140960795 + 3313186 * 2 ^ 59
def prefixEnd_3313186 : Nat := 4983230072969 + 3 ^ 40 * 3313186 * 2
def baseEnd_3313186 : Nat := 1701256915747379378237941

theorem tailTrace_3313186 : CollatzResearch.WordTrace tailWord_3313186 prefixEnd_3313186 1701256915747379378237941 := by
  unfold tailWord_3313186
  simp only [CollatzResearch.WordTrace]
  refine ⟨30210455243725110991129853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80561213983266962643012941 30210455243725110991129853)
  ·
    refine ⟨11328920716396916621673695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30210455243725110991129853 11328920716396916621673695)
    ·
      refine ⟨16993381074595374932510543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11328920716396916621673695 16993381074595374932510543)
      ·
        refine ⟨25490071611893062398765815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16993381074595374932510543 25490071611893062398765815)
        ·
          refine ⟨38235107417839593598148723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25490071611893062398765815 38235107417839593598148723)
          ·
            refine ⟨57352661126759390397223085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38235107417839593598148723 57352661126759390397223085)
            ·
              refine ⟨21507247922534771398958657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57352661126759390397223085 21507247922534771398958657)
              ·
                refine ⟨16130435941901078549218993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21507247922534771398958657 16130435941901078549218993)
                ·
                  refine ⟨12097826956425808911914245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16130435941901078549218993 12097826956425808911914245)
                  ·
                    refine ⟨2268342554329839170983921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12097826956425808911914245 2268342554329839170983921)
                    ·
                      refine ⟨1701256915747379378237941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2268342554329839170983921 1701256915747379378237941)
                      ·
                        rfl

theorem cell23_3313186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_3313186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313186 prefixEnd_3313186 := by exact prefixLift 3313186
  have htrace : WordTrace (prefixWord ++ tailWord_3313186) baseStart_3313186 baseEnd_3313186 := by
    simpa [prefixWord, tailWord_3313186, baseEnd_3313186] using wordTrace_append hprefix tailTrace_3313186
  have hstable : (prefixWord ++ tailWord_3313186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313186).length < 2 ^ (prefixWord ++ tailWord_3313186).sum := by decide
  have hdescent : baseEnd_3313186 < baseStart_3313186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313189 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 4, 2, 3]
def baseStart_3313189 : Nat := 118140960795 + 3313189 * 2 ^ 59
def prefixEnd_3313189 : Nat := 4983230072969 + 3 ^ 40 * 3313189 * 2
def baseEnd_3313189 : Nat := 1701258456189342866500427

theorem tailTrace_3313189 : CollatzResearch.WordTrace tailWord_3313189 prefixEnd_3313189 1701258456189342866500427 := by
  unfold tailWord_3313189
  simp only [CollatzResearch.WordTrace]
  refine ⟨120841930393889575476878621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80561286929259716984585747 120841930393889575476878621)
  ·
    refine ⟨45315723897708590803829483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120841930393889575476878621 45315723897708590803829483)
    ·
      refine ⟨67973585846562886205744225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45315723897708590803829483 67973585846562886205744225)
      ·
        refine ⟨50980189384922164654308169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67973585846562886205744225 50980189384922164654308169)
        ·
          refine ⟨38235142038691623490731127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50980189384922164654308169 38235142038691623490731127)
          ·
            refine ⟨57352713058037435236096691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38235142038691623490731127 57352713058037435236096691)
            ·
              refine ⟨86029069587056152854145037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57352713058037435236096691 86029069587056152854145037)
              ·
                refine ⟨32260901095146057320304389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86029069587056152854145037 32260901095146057320304389)
                ·
                  refine ⟨6048918955339885747557073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32260901095146057320304389 6048918955339885747557073)
                  ·
                    refine ⟨4536689216504914310667805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6048918955339885747557073 4536689216504914310667805)
                    ·
                      refine ⟨1701258456189342866500427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4536689216504914310667805 1701258456189342866500427)
                      ·
                        rfl

theorem cell23_3313189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_3313189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313189 prefixEnd_3313189 := by exact prefixLift 3313189
  have htrace : WordTrace (prefixWord ++ tailWord_3313189) baseStart_3313189 baseEnd_3313189 := by
    simpa [prefixWord, tailWord_3313189, baseEnd_3313189] using wordTrace_append hprefix tailTrace_3313189
  have hstable : (prefixWord ++ tailWord_3313189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313189).length < 2 ^ (prefixWord ++ tailWord_3313189).sum := by decide
  have hdescent : baseEnd_3313189 < baseStart_3313189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313253 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 3]
def baseStart_3313253 : Nat := 118140960795 + 3313253 * 2 ^ 59
def prefixEnd_3313253 : Nat := 4983230072969 + 3 ^ 40 * 3313253 * 2
def baseEnd_3313253 : Nat := 1701291318951230616100133

theorem tailTrace_3313253 : CollatzResearch.WordTrace tailWord_3313253 prefixEnd_3313253 1701291318951230616100133 := by
  unfold tailWord_3313253
  simp only [CollatzResearch.WordTrace]
  refine ⟨120844264665657714407208413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80562843110438476271472275 120844264665657714407208413)
  ·
    refine ⟨45316599249621642902703155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120844264665657714407208413 45316599249621642902703155)
    ·
      refine ⟨67974898874432464354054733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45316599249621642902703155 67974898874432464354054733)
      ·
        refine ⟨25490587077912174132770525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67974898874432464354054733 25490587077912174132770525)
        ·
          refine ⟨9558970154217065299788947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25490587077912174132770525 9558970154217065299788947)
          ·
            refine ⟨14338455231325597949683421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9558970154217065299788947 14338455231325597949683421)
            ·
              refine ⟨5376920711747099231131283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14338455231325597949683421 5376920711747099231131283)
              ·
                refine ⟨8065381067620648846696925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5376920711747099231131283 8065381067620648846696925)
                ·
                  refine ⟨3024517900357743317511347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8065381067620648846696925 3024517900357743317511347)
                  ·
                    refine ⟨4536776850536614976267021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3024517900357743317511347 4536776850536614976267021)
                    ·
                      refine ⟨1701291318951230616100133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4536776850536614976267021 1701291318951230616100133)
                      ·
                        rfl

theorem cell23_3313253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_3313253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313253 prefixEnd_3313253 := by exact prefixLift 3313253
  have htrace : WordTrace (prefixWord ++ tailWord_3313253) baseStart_3313253 baseEnd_3313253 := by
    simpa [prefixWord, tailWord_3313253, baseEnd_3313253] using wordTrace_append hprefix tailTrace_3313253
  have hstable : (prefixWord ++ tailWord_3313253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313253).length < 2 ^ (prefixWord ++ tailWord_3313253).sum := by decide
  have hdescent : baseEnd_3313253 < baseStart_3313253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313289 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 4]
def baseStart_3313289 : Nat := 118140960795 + 3313289 * 2 ^ 59
def prefixEnd_3313289 : Nat := 4983230072969 + 3 ^ 40 * 3313289 * 2
def baseEnd_3313289 : Nat := 1701309804254792475249967

theorem tailTrace_3313289 : CollatzResearch.WordTrace tailWord_3313289 prefixEnd_3313289 1701309804254792475249967 := by
  unfold tailWord_3313289
  simp only [CollatzResearch.WordTrace]
  refine ⟨120845577693527292555518921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80563718462351528370345947 120845577693527292555518921)
  ·
    refine ⟨90634183270145469416639191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120845577693527292555518921 90634183270145469416639191)
    ·
      refine ⟨135951274905218204124958787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90634183270145469416639191 135951274905218204124958787)
      ·
        refine ⟨203926912357827306187438181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135951274905218204124958787 203926912357827306187438181)
        ·
          refine ⟨38236296067092619910144659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203926912357827306187438181 38236296067092619910144659)
          ·
            refine ⟨57354444100638929865216989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38236296067092619910144659 57354444100638929865216989)
            ·
              refine ⟨21507916537739598699456371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57354444100638929865216989 21507916537739598699456371)
              ·
                refine ⟨32261874806609398049184557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21507916537739598699456371 32261874806609398049184557)
                ·
                  refine ⟨12098203052478524268444209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32261874806609398049184557 12098203052478524268444209)
                  ·
                    refine ⟨9073652289358893201333157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12098203052478524268444209 9073652289358893201333157)
                    ·
                      refine ⟨1701309804254792475249967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9073652289358893201333157 1701309804254792475249967)
                      ·
                        rfl

theorem cell23_3313289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_3313289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313289 prefixEnd_3313289 := by exact prefixLift 3313289
  have htrace : WordTrace (prefixWord ++ tailWord_3313289) baseStart_3313289 baseEnd_3313289 := by
    simpa [prefixWord, tailWord_3313289, baseEnd_3313289] using wordTrace_append hprefix tailTrace_3313289
  have hstable : (prefixWord ++ tailWord_3313289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313289).length < 2 ^ (prefixWord ++ tailWord_3313289).sum := by decide
  have hdescent : baseEnd_3313289 < baseStart_3313289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313296 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 3]
def baseStart_3313296 : Nat := 118140960795 + 3313296 * 2 ^ 59
def prefixEnd_3313296 : Nat := 4983230072969 + 3 ^ 40 * 3313296 * 2
def baseEnd_3313296 : Nat := 1701313398619373947862435

theorem tailTrace_3313296 : CollatzResearch.WordTrace tailWord_3313296 prefixEnd_3313296 1701313398619373947862435 := by
  unfold tailWord_3313296
  simp only [CollatzResearch.WordTrace]
  refine ⟨60422916502250966375511871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80563888669667955167349161 60422916502250966375511871)
  ·
    refine ⟨90634374753376449563267807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60422916502250966375511871 90634374753376449563267807)
    ·
      refine ⟨135951562130064674344901711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90634374753376449563267807 135951562130064674344901711)
      ·
        refine ⟨203927343195097011517352567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135951562130064674344901711 203927343195097011517352567)
        ·
          refine ⟨305891014792645517276028851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203927343195097011517352567 305891014792645517276028851)
          ·
            refine ⟨458836522188968275914043277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305891014792645517276028851 458836522188968275914043277)
            ·
              refine ⟨172063695820863103467766229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458836522188968275914043277 172063695820863103467766229)
              ·
                refine ⟨4032742870801478987525771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 172063695820863103467766229 4032742870801478987525771)
                ·
                  refine ⟨6049114306202218481288657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032742870801478987525771 6049114306202218481288657)
                  ·
                    refine ⟨4536835729651663860966493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6049114306202218481288657 4536835729651663860966493)
                    ·
                      refine ⟨1701313398619373947862435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4536835729651663860966493 1701313398619373947862435)
                      ·
                        rfl

theorem cell23_3313296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 3].length) (baseStart_3313296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313296 prefixEnd_3313296 := by exact prefixLift 3313296
  have htrace : WordTrace (prefixWord ++ tailWord_3313296) baseStart_3313296 baseEnd_3313296 := by
    simpa [prefixWord, tailWord_3313296, baseEnd_3313296] using wordTrace_append hprefix tailTrace_3313296
  have hstable : (prefixWord ++ tailWord_3313296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313296).length < 2 ^ (prefixWord ++ tailWord_3313296).sum := by decide
  have hdescent : baseEnd_3313296 < baseStart_3313296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313303 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 2, 4]
def baseStart_3313303 : Nat := 118140960795 + 3313303 * 2 ^ 59
def prefixEnd_3313303 : Nat := 4983230072969 + 3 ^ 40 * 3313303 * 2
def baseEnd_3313303 : Nat := 567105664327985140158301

theorem tailTrace_3313303 : CollatzResearch.WordTrace tailWord_3313303 prefixEnd_3313303 567105664327985140158301 := by
  unfold tailWord_3313303
  simp only [CollatzResearch.WordTrace]
  refine ⟨120846088315476572946528563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80564058876984381964352375 120846088315476572946528563)
  ·
    refine ⟨181269132473214859419792845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120846088315476572946528563 181269132473214859419792845)
    ·
      refine ⟨67975924677455572282422317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181269132473214859419792845 67975924677455572282422317)
      ·
        refine ⟨25490971754045839605908369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67975924677455572282422317 25490971754045839605908369)
        ·
          refine ⟨19118228815534379704431277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25490971754045839605908369 19118228815534379704431277)
          ·
            refine ⟨7169335805825392389161729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19118228815534379704431277 7169335805825392389161729)
            ·
              refine ⟨5377001854369044291871297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7169335805825392389161729 5377001854369044291871297)
              ·
                refine ⟨4032751390776783218903473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5377001854369044291871297 4032751390776783218903473)
                ·
                  refine ⟨3024563543082587414177605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4032751390776783218903473 3024563543082587414177605)
                  ·
                    refine ⟨567105664327985140158301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3024563543082587414177605 567105664327985140158301)
                    ·
                      rfl

theorem cell23_3313303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_3313303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313303 prefixEnd_3313303 := by exact prefixLift 3313303
  have htrace : WordTrace (prefixWord ++ tailWord_3313303) baseStart_3313303 baseEnd_3313303 := by
    simpa [prefixWord, tailWord_3313303, baseEnd_3313303] using wordTrace_append hprefix tailTrace_3313303
  have hstable : (prefixWord ++ tailWord_3313303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313303).length < 2 ^ (prefixWord ++ tailWord_3313303).sum := by decide
  have hdescent : baseEnd_3313303 < baseStart_3313303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313316 : List Nat := [2, 3, 1, 2, 2, 4, 1, 8]
def baseStart_3313316 : Nat := 118140960795 + 3313316 * 2 ^ 59
def prefixEnd_3313316 : Nat := 4983230072969 + 3 ^ 40 * 3313316 * 2
def baseEnd_3313316 : Nat := 63011987712313476652309

theorem tailTrace_3313316 : CollatzResearch.WordTrace tailWord_3313316 prefixEnd_3313316 63011987712313476652309 := by
  unfold tailWord_3313316
  simp only [CollatzResearch.WordTrace]
  refine ⟨60423281232214738083375901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80564374976286317444501201 60423281232214738083375901)
  ·
    refine ⟨22658730462080526781265963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60423281232214738083375901 22658730462080526781265963)
    ·
      refine ⟨33988095693120790171898945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22658730462080526781265963 33988095693120790171898945)
      ·
        refine ⟨25491071769840592628924209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33988095693120790171898945 25491071769840592628924209)
        ·
          refine ⟨19118303827380444471693157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25491071769840592628924209 19118303827380444471693157)
          ·
            refine ⟨3584681967633833338442467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19118303827380444471693157 3584681967633833338442467)
            ·
              refine ⟨5377022951450750007663701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3584681967633833338442467 5377022951450750007663701)
              ·
                refine ⟨63011987712313476652309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5377022951450750007663701 63011987712313476652309)
                ·
                  rfl

theorem cell23_3313316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 8].length) (baseStart_3313316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313316 prefixEnd_3313316 := by exact prefixLift 3313316
  have htrace : WordTrace (prefixWord ++ tailWord_3313316) baseStart_3313316 baseEnd_3313316 := by
    simpa [prefixWord, tailWord_3313316, baseEnd_3313316] using wordTrace_append hprefix tailTrace_3313316
  have hstable : (prefixWord ++ tailWord_3313316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313316).length < 2 ^ (prefixWord ++ tailWord_3313316).sum := by decide
  have hdescent : baseEnd_3313316 < baseStart_3313316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313333 : List Nat := [1, 3, 3, 3, 2, 1, 3, 7]
def baseStart_3313333 : Nat := 118140960795 + 3313333 * 2 ^ 59
def prefixEnd_3313333 : Nat := 4983230072969 + 3 ^ 40 * 3313333 * 2
def baseEnd_3313333 : Nat := 63012311014947789003695

theorem tailTrace_3313333 : CollatzResearch.WordTrace tailWord_3313333 prefixEnd_3313333 63012311014947789003695 := by
  unfold tailWord_3313333
  simp only [CollatzResearch.WordTrace]
  refine ⟨120847182505367888070120653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80564788336911925380080435 120847182505367888070120653)
  ·
    refine ⟨45317693439512958026295245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120847182505367888070120653 45317693439512958026295245)
    ·
      refine ⟨16994135039817359259860717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45317693439512958026295245 16994135039817359259860717)
      ·
        refine ⟨6372800639931509722447769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16994135039817359259860717 6372800639931509722447769)
        ·
          refine ⟨4779600479948632291835827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6372800639931509722447769 4779600479948632291835827)
          ·
            refine ⟨7169400719922948437753741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4779600479948632291835827 7169400719922948437753741)
            ·
              refine ⟨2688525269971105664157653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7169400719922948437753741 2688525269971105664157653)
              ·
                refine ⟨63012311014947789003695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2688525269971105664157653 63012311014947789003695)
                ·
                  rfl

theorem cell23_3313333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 7].length) (baseStart_3313333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313333 prefixEnd_3313333 := by exact prefixLift 3313333
  have htrace : WordTrace (prefixWord ++ tailWord_3313333) baseStart_3313333 baseEnd_3313333 := by
    simpa [prefixWord, tailWord_3313333, baseEnd_3313333] using wordTrace_append hprefix tailTrace_3313333
  have hstable : (prefixWord ++ tailWord_3313333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313333).length < 2 ^ (prefixWord ++ tailWord_3313333).sum := by decide
  have hdescent : baseEnd_3313333 < baseStart_3313333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313349 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_3313349 : Nat := 118140960795 + 3313349 * 2 ^ 59
def prefixEnd_3313349 : Nat := 4983230072969 + 3 ^ 40 * 3313349 * 2
def baseEnd_3313349 : Nat := 1701340613094062240499691

theorem tailTrace_3313349 : CollatzResearch.WordTrace tailWord_3313349 prefixEnd_3313349 1701340613094062240499691 := by
  unfold tailWord_3313349
  simp only [CollatzResearch.WordTrace]
  refine ⟨120847766073309922802703101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80565177382206615201802067 120847766073309922802703101)
  ·
    refine ⟨45317912277491221051013663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120847766073309922802703101 45317912277491221051013663)
    ·
      refine ⟨67976868416236831576520495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45317912277491221051013663 67976868416236831576520495)
      ·
        refine ⟨101965302624355247364780743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67976868416236831576520495 101965302624355247364780743)
        ·
          refine ⟨152947953936532871047171115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101965302624355247364780743 152947953936532871047171115)
          ·
            refine ⟨229421930904799306570756673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152947953936532871047171115 229421930904799306570756673)
            ·
              refine ⟨172066448178599479928067505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229421930904799306570756673 172066448178599479928067505)
              ·
                refine ⟨129049836133949609946050629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172066448178599479928067505 129049836133949609946050629)
                ·
                  refine ⟨24196844275115551864884493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129049836133949609946050629 24196844275115551864884493)
                  ·
                    refine ⟨9073816603168331949331685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24196844275115551864884493 9073816603168331949331685)
                    ·
                      refine ⟨1701340613094062240499691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9073816603168331949331685 1701340613094062240499691)
                      ·
                        rfl

theorem cell23_3313349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_3313349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313349 prefixEnd_3313349 := by exact prefixLift 3313349
  have htrace : WordTrace (prefixWord ++ tailWord_3313349) baseStart_3313349 baseEnd_3313349 := by
    simpa [prefixWord, tailWord_3313349, baseEnd_3313349] using wordTrace_append hprefix tailTrace_3313349
  have hstable : (prefixWord ++ tailWord_3313349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313349).length < 2 ^ (prefixWord ++ tailWord_3313349).sum := by decide
  have hdescent : baseEnd_3313349 < baseStart_3313349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313377 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 2, 1, 3]
def baseStart_3313377 : Nat := 118140960795 + 3313377 * 2 ^ 59
def prefixEnd_3313377 : Nat := 4983230072969 + 3 ^ 40 * 3313377 * 2
def baseEnd_3313377 : Nat := 1701354990552388130949563

theorem tailTrace_3313377 : CollatzResearch.WordTrace tailWord_3313377 prefixEnd_3313377 1701354990552388130949563 := by
  unfold tailWord_3313377
  simp only [CollatzResearch.WordTrace]
  refine ⟨120848787317208483584722385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80565858211472322389814923 120848787317208483584722385)
  ·
    refine ⟨90636590487906362688541789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120848787317208483584722385 90636590487906362688541789)
    ·
      refine ⟨33988721432964886008203171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90636590487906362688541789 33988721432964886008203171)
      ·
        refine ⟨50983082149447329012304757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33988721432964886008203171 50983082149447329012304757)
        ·
          refine ⟨4779663951510687094903571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50983082149447329012304757 4779663951510687094903571)
          ·
            refine ⟨7169495927266030642355357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4779663951510687094903571 7169495927266030642355357)
            ·
              refine ⟨2688560972724761490883259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7169495927266030642355357 2688560972724761490883259)
              ·
                refine ⟨4032841459087142236324889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688560972724761490883259 4032841459087142236324889)
                ·
                  refine ⟨3024631094315356677243667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4032841459087142236324889 3024631094315356677243667)
                  ·
                    refine ⟨4536946641473035015865501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3024631094315356677243667 4536946641473035015865501)
                    ·
                      refine ⟨1701354990552388130949563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4536946641473035015865501 1701354990552388130949563)
                      ·
                        rfl

theorem cell23_3313377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_3313377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313377 prefixEnd_3313377 := by exact prefixLift 3313377
  have htrace : WordTrace (prefixWord ++ tailWord_3313377) baseStart_3313377 baseEnd_3313377 := by
    simpa [prefixWord, tailWord_3313377, baseEnd_3313377] using wordTrace_append hprefix tailTrace_3313377
  have hstable : (prefixWord ++ tailWord_3313377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313377).length < 2 ^ (prefixWord ++ tailWord_3313377).sum := by decide
  have hdescent : baseEnd_3313377 < baseStart_3313377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313386 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_3313386 : Nat := 118140960795 + 3313386 * 2 ^ 59
def prefixEnd_3313386 : Nat := 4983230072969 + 3 ^ 40 * 3313386 * 2
def baseEnd_3313386 : Nat := 1701359611878278595737021

theorem tailTrace_3313386 : CollatzResearch.WordTrace tailWord_3313386 prefixEnd_3313386 1701359611878278595737021 := by
  unfold tailWord_3313386
  simp only [CollatzResearch.WordTrace]
  refine ⟨30212278893543969530450003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80566077049450585414533341 30212278893543969530450003)
  ·
    refine ⟨45318418340315954295675005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30212278893543969530450003 45318418340315954295675005)
    ·
      refine ⟨16994406877618482860878127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45318418340315954295675005 16994406877618482860878127)
      ·
        refine ⟨25491610316427724291317191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16994406877618482860878127 25491610316427724291317191)
        ·
          refine ⟨38237415474641586436975787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25491610316427724291317191 38237415474641586436975787)
          ·
            refine ⟨57356123211962379655463681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38237415474641586436975787 57356123211962379655463681)
            ·
              refine ⟨43017092408971784741597761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57356123211962379655463681 43017092408971784741597761)
              ·
                refine ⟨32262819306728838556198321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43017092408971784741597761 32262819306728838556198321)
                ·
                  refine ⟨24197114480046628917148741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32262819306728838556198321 24197114480046628917148741)
                  ·
                    refine ⟨4536958965008742921965389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24197114480046628917148741 4536958965008742921965389)
                    ·
                      refine ⟨1701359611878278595737021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4536958965008742921965389 1701359611878278595737021)
                      ·
                        rfl

theorem cell23_3313386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_3313386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313386 prefixEnd_3313386 := by exact prefixLift 3313386
  have htrace : WordTrace (prefixWord ++ tailWord_3313386) baseStart_3313386 baseEnd_3313386 := by
    simpa [prefixWord, tailWord_3313386, baseEnd_3313386] using wordTrace_append hprefix tailTrace_3313386
  have hstable : (prefixWord ++ tailWord_3313386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313386).length < 2 ^ (prefixWord ++ tailWord_3313386).sum := by decide
  have hdescent : baseEnd_3313386 < baseStart_3313386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313428 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_3313428 : Nat := 118140960795 + 3313428 * 2 ^ 59
def prefixEnd_3313428 : Nat := 4983230072969 + 3 ^ 40 * 3313428 * 2
def baseEnd_3313428 : Nat := 1701381178065767431411829

theorem tailTrace_3313428 : CollatzResearch.WordTrace tailWord_3313428 prefixEnd_3313428 1701381178065767431411829 := by
  unfold tailWord_3313428
  simp only [CollatzResearch.WordTrace]
  refine ⟨60425323720011859647414469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80567098293349146196552625 60425323720011859647414469)
  ·
    refine ⟨11329748197502223683890213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60425323720011859647414469 11329748197502223683890213)
    ·
      refine ⟨2124327787031666940729415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11329748197502223683890213 2124327787031666940729415)
      ·
        refine ⟨3186491680547500411094123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2124327787031666940729415 3186491680547500411094123)
        ·
          refine ⟨4779737520821250616641185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3186491680547500411094123 4779737520821250616641185)
          ·
            refine ⟨3584803140615937962480889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4779737520821250616641185 3584803140615937962480889)
            ·
              refine ⟨2688602355461953471860667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3584803140615937962480889 2688602355461953471860667)
              ·
                refine ⟨4032903533192930207791001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688602355461953471860667 4032903533192930207791001)
                ·
                  refine ⟨3024677649894697655843251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4032903533192930207791001 3024677649894697655843251)
                  ·
                    refine ⟨4537016474842046483764877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3024677649894697655843251 4537016474842046483764877)
                    ·
                      refine ⟨1701381178065767431411829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4537016474842046483764877 1701381178065767431411829)
                      ·
                        rfl

theorem cell23_3313428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_3313428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313428 prefixEnd_3313428 := by exact prefixLift 3313428
  have htrace : WordTrace (prefixWord ++ tailWord_3313428) baseStart_3313428 baseEnd_3313428 := by
    simpa [prefixWord, tailWord_3313428, baseEnd_3313428] using wordTrace_append hprefix tailTrace_3313428
  have hstable : (prefixWord ++ tailWord_3313428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313428).length < 2 ^ (prefixWord ++ tailWord_3313428).sum := by decide
  have hdescent : baseEnd_3313428 < baseStart_3313428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313434 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2]
def baseStart_3313434 : Nat := 118140960795 + 3313434 * 2 ^ 59
def prefixEnd_3313434 : Nat := 4983230072969 + 3 ^ 40 * 3313434 * 2
def baseEnd_3313434 : Nat := 1701384258949694407936801

theorem tailTrace_3313434 : CollatzResearch.WordTrace tailWord_3313434 prefixEnd_3313434 1701384258949694407936801 := by
  unfold tailWord_3313434
  simp only [CollatzResearch.WordTrace]
  refine ⟨30212716569500495579886839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80567244185334654879698237 30212716569500495579886839)
  ·
    refine ⟨45319074854250743369830259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30212716569500495579886839 45319074854250743369830259)
    ·
      refine ⟨67978612281376115054745389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45319074854250743369830259 67978612281376115054745389)
      ·
        refine ⟨25491979605516043145529521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67978612281376115054745389 25491979605516043145529521)
        ·
          refine ⟨19118984704137032359147141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25491979605516043145529521 19118984704137032359147141)
          ·
            refine ⟨3584809632025693567340089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19118984704137032359147141 3584809632025693567340089)
            ·
              refine ⟨2688607224019270175505067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3584809632025693567340089 2688607224019270175505067)
              ·
                refine ⟨4032910836028905263257601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688607224019270175505067 4032910836028905263257601)
                ·
                  refine ⟨3024683127021678947443201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4032910836028905263257601 3024683127021678947443201)
                  ·
                    refine ⟨2268512345266259210582401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3024683127021678947443201 2268512345266259210582401)
                    ·
                      refine ⟨1701384258949694407936801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2268512345266259210582401 1701384258949694407936801)
                      ·
                        rfl

theorem cell23_3313434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_3313434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313434 prefixEnd_3313434 := by exact prefixLift 3313434
  have htrace : WordTrace (prefixWord ++ tailWord_3313434) baseStart_3313434 baseEnd_3313434 := by
    simpa [prefixWord, tailWord_3313434, baseEnd_3313434] using wordTrace_append hprefix tailTrace_3313434
  have hstable : (prefixWord ++ tailWord_3313434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313434).length < 2 ^ (prefixWord ++ tailWord_3313434).sum := by decide
  have hdescent : baseEnd_3313434 < baseStart_3313434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313436 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_3313436 : Nat := 118140960795 + 3313436 * 2 ^ 59
def prefixEnd_3313436 : Nat := 4983230072969 + 3 ^ 40 * 3313436 * 2
def baseEnd_3313436 : Nat := 567128428637001133370597

theorem tailTrace_3313436 : CollatzResearch.WordTrace tailWord_3313436 prefixEnd_3313436 567128428637001133370597 := by
  unfold tailWord_3313436
  simp only [CollatzResearch.WordTrace]
  refine ⟨60425469611997368330560081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80567292815996491107413441 60425469611997368330560081)
  ·
    refine ⟨45319102208998026247920061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60425469611997368330560081 45319102208998026247920061)
    ·
      refine ⟨16994663328374259842970023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45319102208998026247920061 16994663328374259842970023)
      ·
        refine ⟨25491994992561389764455035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16994663328374259842970023 25491994992561389764455035)
        ·
          refine ⟨38237992488842084646682553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25491994992561389764455035 38237992488842084646682553)
          ·
            refine ⟨28678494366631563485011915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38237992488842084646682553 28678494366631563485011915)
            ·
              refine ⟨43017741549947345227517873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28678494366631563485011915 43017741549947345227517873)
              ·
                refine ⟨32263306162460508920638405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43017741549947345227517873 32263306162460508920638405)
                ·
                  refine ⟨6049369905461345422619701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32263306162460508920638405 6049369905461345422619701)
                  ·
                    refine ⟨567128428637001133370597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6049369905461345422619701 567128428637001133370597)
                    ·
                      rfl

theorem cell23_3313436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_3313436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313436 prefixEnd_3313436 := by exact prefixLift 3313436
  have htrace : WordTrace (prefixWord ++ tailWord_3313436) baseStart_3313436 baseEnd_3313436 := by
    simpa [prefixWord, tailWord_3313436, baseEnd_3313436] using wordTrace_append hprefix tailTrace_3313436
  have hstable : (prefixWord ++ tailWord_3313436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313436).length < 2 ^ (prefixWord ++ tailWord_3313436).sum := by decide
  have hdescent : baseEnd_3313436 < baseStart_3313436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313438 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3313438 : Nat := 118140960795 + 3313438 * 2 ^ 59
def prefixEnd_3313438 : Nat := 4983230072969 + 3 ^ 40 * 3313438 * 2
def baseEnd_3313438 : Nat := 1701386312872312392286783

theorem tailTrace_3313438 : CollatzResearch.WordTrace tailWord_3313438 prefixEnd_3313438 1701386312872312392286783 := by
  unfold tailWord_3313438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15106376521248436375336621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80567341446658327335128645 15106376521248436375336621)
  ·
    refine ⟨5664891195468163640751233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15106376521248436375336621 5664891195468163640751233)
    ·
      refine ⟨4248668396601122730563425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5664891195468163640751233 4248668396601122730563425)
      ·
        refine ⟨3186501297450842047922569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4248668396601122730563425 3186501297450842047922569)
        ·
          refine ⟨2389875973088131535941927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3186501297450842047922569 2389875973088131535941927)
          ·
            refine ⟨3584813959632197303912891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389875973088131535941927 3584813959632197303912891)
            ·
              refine ⟨5377220939448295955869337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3584813959632197303912891 5377220939448295955869337)
              ·
                refine ⟨4032915704586221966902003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5377220939448295955869337 4032915704586221966902003)
                ·
                  refine ⟨6049373556879332950353005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032915704586221966902003 6049373556879332950353005)
                  ·
                    refine ⟨2268515083829749856382377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6049373556879332950353005 2268515083829749856382377)
                    ·
                      refine ⟨1701386312872312392286783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2268515083829749856382377 1701386312872312392286783)
                      ·
                        rfl

theorem cell23_3313438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3313438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313438 prefixEnd_3313438 := by exact prefixLift 3313438
  have htrace : WordTrace (prefixWord ++ tailWord_3313438) baseStart_3313438 baseEnd_3313438 := by
    simpa [prefixWord, tailWord_3313438, baseEnd_3313438] using wordTrace_append hprefix tailTrace_3313438
  have hstable : (prefixWord ++ tailWord_3313438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313438).length < 2 ^ (prefixWord ++ tailWord_3313438).sum := by decide
  have hdescent : baseEnd_3313438 < baseStart_3313438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313486 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3313486 : Nat := 118140960795 + 3313486 * 2 ^ 59
def prefixEnd_3313486 : Nat := 4983230072969 + 3 ^ 40 * 3313486 * 2
def baseEnd_3313486 : Nat := 1701410959943728204486561

theorem tailTrace_3313486 : CollatzResearch.WordTrace tailWord_3313486 prefixEnd_3313486 1701410959943728204486561 := by
  unfold tailWord_3313486
  simp only [CollatzResearch.WordTrace]
  refine ⟨15106595359226699400055039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80568508582542396800293541 15106595359226699400055039)
  ·
    refine ⟨22659893038840049100082559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15106595359226699400055039 22659893038840049100082559)
    ·
      refine ⟨33989839558260073650123839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22659893038840049100082559 33989839558260073650123839)
      ·
        refine ⟨50984759337390110475185759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33989839558260073650123839 50984759337390110475185759)
        ·
          refine ⟨76477139006085165712778639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50984759337390110475185759 76477139006085165712778639)
          ·
            refine ⟨114715708509127748569167959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76477139006085165712778639 114715708509127748569167959)
            ·
              refine ⟨172073562763691622853751939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114715708509127748569167959 172073562763691622853751939)
              ·
                refine ⟨258110344145537434280627909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172073562763691622853751939 258110344145537434280627909)
                ·
                  refine ⟨48395689527288268927617733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258110344145537434280627909 48395689527288268927617733)
                  ·
                    refine ⟨9074191786366550423928325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48395689527288268927617733 9074191786366550423928325)
                    ·
                      refine ⟨1701410959943728204486561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9074191786366550423928325 1701410959943728204486561)
                      ·
                        rfl

theorem cell23_3313486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3313486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313486 prefixEnd_3313486 := by exact prefixLift 3313486
  have htrace : WordTrace (prefixWord ++ tailWord_3313486) baseStart_3313486 baseEnd_3313486 := by
    simpa [prefixWord, tailWord_3313486, baseEnd_3313486] using wordTrace_append hprefix tailTrace_3313486
  have hstable : (prefixWord ++ tailWord_3313486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313486).length < 2 ^ (prefixWord ++ tailWord_3313486).sum := by decide
  have hdescent : baseEnd_3313486 < baseStart_3313486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313490 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_3313490 : Nat := 118140960795 + 3313490 * 2 ^ 59
def prefixEnd_3313490 : Nat := 4983230072969 + 3 ^ 40 * 3313490 * 2
def baseEnd_3313490 : Nat := 1701413013866346188836543

theorem tailTrace_3313490 : CollatzResearch.WordTrace tailWord_3313490 prefixEnd_3313490 1701413013866346188836543 := by
  unfold tailWord_3313490
  simp only [CollatzResearch.WordTrace]
  refine ⟨30213227191449775970896481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80568605843866069255723949 30213227191449775970896481)
  ·
    refine ⟨22659920393587331978172361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30213227191449775970896481 22659920393587331978172361)
    ·
      refine ⟨16994940295190498983629271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22659920393587331978172361 16994940295190498983629271)
      ·
        refine ⟨25492410442785748475443907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16994940295190498983629271 25492410442785748475443907)
        ·
          refine ⟨38238615664178622713165861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25492410442785748475443907 38238615664178622713165861)
          ·
            refine ⟨7169740437033491758718599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38238615664178622713165861 7169740437033491758718599)
            ·
              refine ⟨10754610655550237638077899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7169740437033491758718599 10754610655550237638077899)
              ·
                refine ⟨16131915983325356457116849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10754610655550237638077899 16131915983325356457116849)
                ·
                  refine ⟨12098936987494017342837637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16131915983325356457116849 12098936987494017342837637)
                  ·
                    refine ⟨2268550685155128251782057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12098936987494017342837637 2268550685155128251782057)
                    ·
                      refine ⟨1701413013866346188836543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2268550685155128251782057 1701413013866346188836543)
                      ·
                        rfl

theorem cell23_3313490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_3313490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313490 prefixEnd_3313490 := by exact prefixLift 3313490
  have htrace : WordTrace (prefixWord ++ tailWord_3313490) baseStart_3313490 baseEnd_3313490 := by
    simpa [prefixWord, tailWord_3313490, baseEnd_3313490] using wordTrace_append hprefix tailTrace_3313490
  have hstable : (prefixWord ++ tailWord_3313490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313490).length < 2 ^ (prefixWord ++ tailWord_3313490).sum := by decide
  have hdescent : baseEnd_3313490 < baseStart_3313490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313507 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 2, 1, 4]
def baseStart_3313507 : Nat := 118140960795 + 3313507 * 2 ^ 59
def prefixEnd_3313507 : Nat := 4983230072969 + 3 ^ 40 * 3313507 * 2
def baseEnd_3313507 : Nat := 1701421743037472622323965

theorem tailTrace_3313507 : CollatzResearch.WordTrace tailWord_3313507 prefixEnd_3313507 1701421743037472622323965 := by
  unfold tailWord_3313507
  simp only [CollatzResearch.WordTrace]
  refine ⟨120853528806737515786954775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80569019204491677191303183 120853528806737515786954775)
  ·
    refine ⟨181280293210106273680432163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120853528806737515786954775 181280293210106273680432163)
    ·
      refine ⟨271920439815159410520648245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181280293210106273680432163 271920439815159410520648245)
      ·
        refine ⟨25492541232671194736310773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271920439815159410520648245 25492541232671194736310773)
        ·
          refine ⟨2389925740562924506529135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25492541232671194736310773 2389925740562924506529135)
          ·
            refine ⟨3584888610844386759793703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389925740562924506529135 3584888610844386759793703)
            ·
              refine ⟨5377332916266580139690555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3584888610844386759793703 5377332916266580139690555)
              ·
                refine ⟨8065999374399870209535833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5377332916266580139690555 8065999374399870209535833)
                ·
                  refine ⟨6049499530799902657151875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8065999374399870209535833 6049499530799902657151875)
                  ·
                    refine ⟨9074249296199853985727813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6049499530799902657151875 9074249296199853985727813)
                    ·
                      refine ⟨1701421743037472622323965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9074249296199853985727813 1701421743037472622323965)
                      ·
                        rfl

theorem cell23_3313507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_3313507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313507 prefixEnd_3313507 := by exact prefixLift 3313507
  have htrace : WordTrace (prefixWord ++ tailWord_3313507) baseStart_3313507 baseEnd_3313507 := by
    simpa [prefixWord, tailWord_3313507, baseEnd_3313507] using wordTrace_append hprefix tailTrace_3313507
  have hstable : (prefixWord ++ tailWord_3313507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313507).length < 2 ^ (prefixWord ++ tailWord_3313507).sum := by decide
  have hdescent : baseEnd_3313507 < baseStart_3313507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313523 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 7, 1, 3]
def baseStart_3313523 : Nat := 118140960795 + 3313523 * 2 ^ 59
def prefixEnd_3313523 : Nat := 4983230072969 + 3 ^ 40 * 3313523 * 2
def baseEnd_3313523 : Nat := 1701429958727944559723891

theorem tailTrace_3313523 : CollatzResearch.WordTrace tailWord_3313523 prefixEnd_3313523 1701429958727944559723891 := by
  unfold tailWord_3313523
  simp only [CollatzResearch.WordTrace]
  refine ⟨120854112374679550519537223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80569408249786367013024815 120854112374679550519537223)
  ·
    refine ⟨181281168562019325779305835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120854112374679550519537223 181281168562019325779305835)
    ·
      refine ⟨271921752843028988668958753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181281168562019325779305835 271921752843028988668958753)
      ·
        refine ⟨203941314632271741501719065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271921752843028988668958753 203941314632271741501719065)
        ·
          refine ⟨152955985974203806126289299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203941314632271741501719065 152955985974203806126289299)
          ·
            refine ⟨229433978961305709189433949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152955985974203806126289299 229433978961305709189433949)
            ·
              refine ⟨86037742110489640946037731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229433978961305709189433949 86037742110489640946037731)
              ·
                refine ⟨129056613165734461419056597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86037742110489640946037731 129056613165734461419056597)
                ·
                  refine ⟨3024764371071901439509139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 129056613165734461419056597 3024764371071901439509139)
                  ·
                    refine ⟨4537146556607852159263709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3024764371071901439509139 4537146556607852159263709)
                    ·
                      refine ⟨1701429958727944559723891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4537146556607852159263709 1701429958727944559723891)
                      ·
                        rfl

theorem cell23_3313523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 1, 3].length) (baseStart_3313523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313523 prefixEnd_3313523 := by exact prefixLift 3313523
  have htrace : WordTrace (prefixWord ++ tailWord_3313523) baseStart_3313523 baseEnd_3313523 := by
    simpa [prefixWord, tailWord_3313523, baseEnd_3313523] using wordTrace_append hprefix tailTrace_3313523
  have hstable : (prefixWord ++ tailWord_3313523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313523).length < 2 ^ (prefixWord ++ tailWord_3313523).sum := by decide
  have hdescent : baseEnd_3313523 < baseStart_3313523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313534 : List Nat := [4, 2, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3313534 : Nat := 118140960795 + 3313534 * 2 ^ 59
def prefixEnd_3313534 : Nat := 4983230072969 + 3 ^ 40 * 3313534 * 2
def baseEnd_3313534 : Nat := 567145202338381338895447

theorem tailTrace_3313534 : CollatzResearch.WordTrace tailWord_3313534 prefixEnd_3313534 567145202338381338895447 := by
  unfold tailWord_3313534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15106814197204962424773457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80569675718426466265458437 15106814197204962424773457)
  ·
    refine ⟨11330110647903721818580093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15106814197204962424773457 11330110647903721818580093)
    ·
      refine ⟨4248791492963895681967535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11330110647903721818580093 4248791492963895681967535)
      ·
        refine ⟨6373187239445843522951303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248791492963895681967535 6373187239445843522951303)
        ·
          refine ⟨9559780859168765284426955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6373187239445843522951303 9559780859168765284426955)
          ·
            refine ⟨14339671288753147926640433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9559780859168765284426955 14339671288753147926640433)
            ·
              refine ⟨10754753466564860944980325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14339671288753147926640433 10754753466564860944980325)
              ·
                refine ⟨2016516274980911427183811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10754753466564860944980325 2016516274980911427183811)
                ·
                  refine ⟨3024774412471367140775717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016516274980911427183811 3024774412471367140775717)
                  ·
                    refine ⟨567145202338381338895447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3024774412471367140775717 567145202338381338895447)
                    ·
                      rfl

theorem cell23_3313534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3313534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313534 prefixEnd_3313534 := by exact prefixLift 3313534
  have htrace : WordTrace (prefixWord ++ tailWord_3313534) baseStart_3313534 baseEnd_3313534 := by
    simpa [prefixWord, tailWord_3313534, baseEnd_3313534] using wordTrace_append hprefix tailTrace_3313534
  have hstable : (prefixWord ++ tailWord_3313534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313534).length < 2 ^ (prefixWord ++ tailWord_3313534).sum := by decide
  have hdescent : baseEnd_3313534 < baseStart_3313534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313540 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_3313540 : Nat := 118140960795 + 3313540 * 2 ^ 59
def prefixEnd_3313540 : Nat := 4983230072969 + 3 ^ 40 * 3313540 * 2
def baseEnd_3313540 : Nat := 1701438687899070993211313

theorem tailTrace_3313540 : CollatzResearch.WordTrace tailWord_3313540 prefixEnd_3313540 1701438687899070993211313 := by
  unfold tailWord_3313540
  simp only [CollatzResearch.WordTrace]
  refine ⟨60427366207808981211453037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80569821610411974948604049 60427366207808981211453037)
  ·
    refine ⟨22660262327928367954294889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60427366207808981211453037 22660262327928367954294889)
    ·
      refine ⟨16995196745946275965721167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22660262327928367954294889 16995196745946275965721167)
      ·
        refine ⟨25492795118919413948581751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16995196745946275965721167 25492795118919413948581751)
        ·
          refine ⟨38239192678379120922872627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25492795118919413948581751 38239192678379120922872627)
          ·
            refine ⟨57358789017568681384308941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38239192678379120922872627 57358789017568681384308941)
            ·
              refine ⟨21509545881588255519115853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57358789017568681384308941 21509545881588255519115853)
              ·
                refine ⟨8066079705595595819668445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21509545881588255519115853 8066079705595595819668445)
                ·
                  refine ⟨3024779889598348432375667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8066079705595595819668445 3024779889598348432375667)
                  ·
                    refine ⟨4537169834397522648563501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3024779889598348432375667 4537169834397522648563501)
                    ·
                      refine ⟨1701438687899070993211313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4537169834397522648563501 1701438687899070993211313)
                      ·
                        rfl

theorem cell23_3313540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_3313540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313540 prefixEnd_3313540 := by exact prefixLift 3313540
  have htrace : WordTrace (prefixWord ++ tailWord_3313540) baseStart_3313540 baseEnd_3313540 := by
    simpa [prefixWord, tailWord_3313540, baseEnd_3313540] using wordTrace_append hprefix tailTrace_3313540
  have hstable : (prefixWord ++ tailWord_3313540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313540).length < 2 ^ (prefixWord ++ tailWord_3313540).sum := by decide
  have hdescent : baseEnd_3313540 < baseStart_3313540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313583 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 5]
def baseStart_3313583 : Nat := 118140960795 + 3313583 * 2 ^ 59
def prefixEnd_3313583 : Nat := 4983230072969 + 3 ^ 40 * 3313583 * 2
def baseEnd_3313583 : Nat := 1701460767567214324973615

theorem tailTrace_3313583 : CollatzResearch.WordTrace tailWord_3313583 prefixEnd_3313583 1701460767567214324973615 := by
  unfold tailWord_3313583
  simp only [CollatzResearch.WordTrace]
  refine ⟨120856300754462180766721403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80570867169641453844480935 120856300754462180766721403)
  ·
    refine ⟨181284451131693271150082105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120856300754462180766721403 181284451131693271150082105)
    ·
      refine ⟨135963338348769953362561579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181284451131693271150082105 135963338348769953362561579)
      ·
        refine ⟨203945007523154930043842369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135963338348769953362561579 203945007523154930043842369)
        ·
          refine ⟨152958755642366197532881777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203945007523154930043842369 152958755642366197532881777)
          ·
            refine ⟨114719066731774648149661333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152958755642366197532881777 114719066731774648149661333)
            ·
              refine ⟨5377456253051936632015375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114719066731774648149661333 5377456253051936632015375)
              ·
                refine ⟨8066184379577904948023063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5377456253051936632015375 8066184379577904948023063)
                ·
                  refine ⟨12099276569366857422034595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8066184379577904948023063 12099276569366857422034595)
                  ·
                    refine ⟨18148914854050286133051893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12099276569366857422034595 18148914854050286133051893)
                    ·
                      refine ⟨1701460767567214324973615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18148914854050286133051893 1701460767567214324973615)
                      ·
                        rfl

theorem cell23_3313583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 5].length) (baseStart_3313583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313583 prefixEnd_3313583 := by exact prefixLift 3313583
  have htrace : WordTrace (prefixWord ++ tailWord_3313583) baseStart_3313583 baseEnd_3313583 := by
    simpa [prefixWord, tailWord_3313583, baseEnd_3313583] using wordTrace_append hprefix tailTrace_3313583
  have hstable : (prefixWord ++ tailWord_3313583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313583).length < 2 ^ (prefixWord ++ tailWord_3313583).sum := by decide
  have hdescent : baseEnd_3313583 < baseStart_3313583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313634 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3313634 : Nat := 118140960795 + 3313634 * 2 ^ 59
def prefixEnd_3313634 : Nat := 4983230072969 + 3 ^ 40 * 3313634 * 2
def baseEnd_3313634 : Nat := 1701486955080593625435881

theorem tailTrace_3313634 : CollatzResearch.WordTrace tailWord_3313634 prefixEnd_3313634 1701486955080593625435881 := by
  unfold tailWord_3313634
  simp only [CollatzResearch.WordTrace]
  refine ⟨30214540219319354119206989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80572107251518277651218637 30214540219319354119206989)
  ·
    refine ⟨11330452582244757794702621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30214540219319354119206989 11330452582244757794702621)
    ·
      refine ⟨4248919718341784173013483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11330452582244757794702621 4248919718341784173013483)
      ·
        refine ⟨6373379577512676259520225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248919718341784173013483 6373379577512676259520225)
        ·
          refine ⟨4780034683134507194640169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6373379577512676259520225 4780034683134507194640169)
          ·
            refine ⟨3585026012350880395980127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4780034683134507194640169 3585026012350880395980127)
            ·
              refine ⟨5377539018526320593970191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585026012350880395980127 5377539018526320593970191)
              ·
                refine ⟨8066308527789480890955287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5377539018526320593970191 8066308527789480890955287)
                ·
                  refine ⟨12099462791684221336432931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8066308527789480890955287 12099462791684221336432931)
                  ·
                    refine ⟨18149194187526332004649397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12099462791684221336432931 18149194187526332004649397)
                    ·
                      refine ⟨1701486955080593625435881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18149194187526332004649397 1701486955080593625435881)
                      ·
                        rfl

theorem cell23_3313634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3313634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313634 prefixEnd_3313634 := by exact prefixLift 3313634
  have htrace : WordTrace (prefixWord ++ tailWord_3313634) baseStart_3313634 baseEnd_3313634 := by
    simpa [prefixWord, tailWord_3313634, baseEnd_3313634] using wordTrace_append hprefix tailTrace_3313634
  have hstable : (prefixWord ++ tailWord_3313634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313634).length < 2 ^ (prefixWord ++ tailWord_3313634).sum := by decide
  have hdescent : baseEnd_3313634 < baseStart_3313634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313647 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 2, 1, 3]
def baseStart_3313647 : Nat := 118140960795 + 3313647 * 2 ^ 59
def prefixEnd_3313647 : Nat := 4983230072969 + 3 ^ 40 * 3313647 * 2
def baseEnd_3313647 : Nat := 1701493630329102074573321

theorem tailTrace_3313647 : CollatzResearch.WordTrace tailWord_3313647 prefixEnd_3313647 1701493630329102074573321 := by
  unfold tailWord_3313647
  simp only [CollatzResearch.WordTrace]
  refine ⟨120858635026230319697051195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80572423350820213131367463 120858635026230319697051195)
  ·
    refine ⟨181287952539345479545576793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120858635026230319697051195 181287952539345479545576793)
    ·
      refine ⟨135965964404509109659182595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181287952539345479545576793 135965964404509109659182595)
      ·
        refine ⟨203948946606763664488773893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135965964404509109659182595 203948946606763664488773893)
        ·
          refine ⟨38240427488768187091645105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203948946606763664488773893 38240427488768187091645105)
          ·
            refine ⟨28680320616576140318733829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38240427488768187091645105 28680320616576140318733829)
            ·
              refine ⟨5377560115608026309762593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28680320616576140318733829 5377560115608026309762593)
              ·
                refine ⟨4033170086706019732321945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5377560115608026309762593 4033170086706019732321945)
                ·
                  refine ⟨3024877565029514799241459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4033170086706019732321945 3024877565029514799241459)
                  ·
                    refine ⟨4537316347544272198862189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3024877565029514799241459 4537316347544272198862189)
                    ·
                      refine ⟨1701493630329102074573321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4537316347544272198862189 1701493630329102074573321)
                      ·
                        rfl

theorem cell23_3313647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 1, 3].length) (baseStart_3313647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313647 prefixEnd_3313647 := by exact prefixLift 3313647
  have htrace : WordTrace (prefixWord ++ tailWord_3313647) baseStart_3313647 baseEnd_3313647 := by
    simpa [prefixWord, tailWord_3313647, baseEnd_3313647] using wordTrace_append hprefix tailTrace_3313647
  have hstable : (prefixWord ++ tailWord_3313647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313647).length < 2 ^ (prefixWord ++ tailWord_3313647).sum := by decide
  have hdescent : baseEnd_3313647 < baseStart_3313647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313710 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_3313710 : Nat := 118140960795 + 3313710 * 2 ^ 59
def prefixEnd_3313710 : Nat := 4983230072969 + 3 ^ 40 * 3313710 * 2
def baseEnd_3313710 : Nat := 189058442178926147565059

theorem tailTrace_3313710 : CollatzResearch.WordTrace tailWord_3313710 prefixEnd_3313710 189058442178926147565059 := by
  unfold tailWord_3313710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15107616603125260182074323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80573955216668054304396389 15107616603125260182074323)
  ·
    refine ⟨22661424904687890273111485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15107616603125260182074323 22661424904687890273111485)
    ·
      refine ⟨8498034339257958852416807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22661424904687890273111485 8498034339257958852416807)
      ·
        refine ⟨12747051508886938278625211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8498034339257958852416807 12747051508886938278625211)
        ·
          refine ⟨19120577263330407417937817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12747051508886938278625211 19120577263330407417937817)
          ·
            refine ⟨14340432947497805563453363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19120577263330407417937817 14340432947497805563453363)
            ·
              refine ⟨21510649421246708345180045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14340432947497805563453363 21510649421246708345180045)
              ·
                refine ⟨8066493532967515629442517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21510649421246708345180045 8066493532967515629442517)
                ·
                  refine ⟨189058442178926147565059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8066493532967515629442517 189058442178926147565059)
                  ·
                    rfl

theorem cell23_3313710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_3313710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313710 prefixEnd_3313710 := by exact prefixLift 3313710
  have htrace : WordTrace (prefixWord ++ tailWord_3313710) baseStart_3313710 baseEnd_3313710 := by
    simpa [prefixWord, tailWord_3313710, baseEnd_3313710] using wordTrace_append hprefix tailTrace_3313710
  have hstable : (prefixWord ++ tailWord_3313710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313710).length < 2 ^ (prefixWord ++ tailWord_3313710).sum := by decide
  have hdescent : baseEnd_3313710 < baseStart_3313710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313721 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 1, 4, 2]
def baseStart_3313721 : Nat := 118140960795 + 3313721 * 2 ^ 59
def prefixEnd_3313721 : Nat := 4983230072969 + 3 ^ 40 * 3313721 * 2
def baseEnd_3313721 : Nat := 1701531627897534785047981

theorem tailTrace_3313721 : CollatzResearch.WordTrace tailWord_3313721 prefixEnd_3313721 1701531627897534785047981 := by
  unfold tailWord_3313721
  simp only [CollatzResearch.WordTrace]
  refine ⟨120861334027962230335245017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80574222685308153556830011 120861334027962230335245017)
  ·
    refine ⟨90646000520971672751433763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120861334027962230335245017 90646000520971672751433763)
    ·
      refine ⟨135969000781457509127150645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90646000520971672751433763 135969000781457509127150645)
      ·
        refine ⟨12747093823261641480670373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135969000781457509127150645 12747093823261641480670373)
        ·
          refine ⟨2390080091861557777625695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12747093823261641480670373 2390080091861557777625695)
          ·
            refine ⟨3585120137792336666438543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390080091861557777625695 3585120137792336666438543)
            ·
              refine ⟨5377680206688504999657815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585120137792336666438543 5377680206688504999657815)
              ·
                refine ⟨8066520310032757499486723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5377680206688504999657815 8066520310032757499486723)
                ·
                  refine ⟨12099780465049136249230085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8066520310032757499486723 12099780465049136249230085)
                  ·
                    refine ⟨2268708837196713046730641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12099780465049136249230085 2268708837196713046730641)
                    ·
                      refine ⟨1701531627897534785047981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2268708837196713046730641 1701531627897534785047981)
                      ·
                        rfl

theorem cell23_3313721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_3313721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313721 prefixEnd_3313721 := by exact prefixLift 3313721
  have htrace : WordTrace (prefixWord ++ tailWord_3313721) baseStart_3313721 baseEnd_3313721 := by
    simpa [prefixWord, tailWord_3313721, baseEnd_3313721] using wordTrace_append hprefix tailTrace_3313721
  have hstable : (prefixWord ++ tailWord_3313721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313721).length < 2 ^ (prefixWord ++ tailWord_3313721).sum := by decide
  have hdescent : baseEnd_3313721 < baseStart_3313721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313723 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 4, 5]
def baseStart_3313723 : Nat := 118140960795 + 3313723 * 2 ^ 59
def prefixEnd_3313723 : Nat := 4983230072969 + 3 ^ 40 * 3313723 * 2
def baseEnd_3313723 : Nat := 567177551619614592407657

theorem tailTrace_3313723 : CollatzResearch.WordTrace tailWord_3313723 prefixEnd_3313723 567177551619614592407657 := by
  unfold tailWord_3313723
  simp only [CollatzResearch.WordTrace]
  refine ⟨120861406973954984676817823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80574271315969989784545215 120861406973954984676817823)
  ·
    refine ⟨181292110460932477015226735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120861406973954984676817823 181292110460932477015226735)
    ·
      refine ⟨271938165691398715522840103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181292110460932477015226735 271938165691398715522840103)
      ·
        refine ⟨407907248537098073284260155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271938165691398715522840103 407907248537098073284260155)
        ·
          refine ⟨611860872805647109926390233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407907248537098073284260155 611860872805647109926390233)
          ·
            refine ⟨458895654604235332444792675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611860872805647109926390233 458895654604235332444792675)
            ·
              refine ⟨688343481906352998667189013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458895654604235332444792675 688343481906352998667189013)
              ·
                refine ⟨32266100714360296812524485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 688343481906352998667189013 32266100714360296812524485)
                ·
                  refine ⟨6049893883942555652348341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32266100714360296812524485 6049893883942555652348341)
                  ·
                    refine ⟨567177551619614592407657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6049893883942555652348341 567177551619614592407657)
                    ·
                      rfl

theorem cell23_3313723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 5].length) (baseStart_3313723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313723 prefixEnd_3313723 := by exact prefixLift 3313723
  have htrace : WordTrace (prefixWord ++ tailWord_3313723) baseStart_3313723 baseEnd_3313723 := by
    simpa [prefixWord, tailWord_3313723, baseEnd_3313723] using wordTrace_append hprefix tailTrace_3313723
  have hstable : (prefixWord ++ tailWord_3313723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313723).length < 2 ^ (prefixWord ++ tailWord_3313723).sum := by decide
  have hdescent : baseEnd_3313723 < baseStart_3313723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313733 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_3313733 : Nat := 118140960795 + 3313733 * 2 ^ 59
def prefixEnd_3313733 : Nat := 4983230072969 + 3 ^ 40 * 3313733 * 2
def baseEnd_3313733 : Nat := 1701537789665388738097925

theorem tailTrace_3313733 : CollatzResearch.WordTrace tailWord_3313733 prefixEnd_3313733 1701537789665388738097925 := by
  unfold tailWord_3313733
  simp only [CollatzResearch.WordTrace]
  refine ⟨120861771703918756384681853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80574514469279170923121235 120861771703918756384681853)
  ·
    refine ⟨45323164388969533644255695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120861771703918756384681853 45323164388969533644255695)
    ·
      refine ⟨67984746583454300466383543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45323164388969533644255695 67984746583454300466383543)
      ·
        refine ⟨101977119875181450699575315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67984746583454300466383543 101977119875181450699575315)
        ·
          refine ⟨152965679812772176049362973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101977119875181450699575315 152965679812772176049362973)
          ·
            refine ⟨57362129929789566018511115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152965679812772176049362973 57362129929789566018511115)
            ·
              refine ⟨86043194894684349027766673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57362129929789566018511115 86043194894684349027766673)
              ·
                refine ⟨64532396171013261770825005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86043194894684349027766673 64532396171013261770825005)
                ·
                  refine ⟨24199648564129973164059377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64532396171013261770825005 24199648564129973164059377)
                  ·
                    refine ⟨18149736423097479873044533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24199648564129973164059377 18149736423097479873044533)
                    ·
                      refine ⟨1701537789665388738097925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18149736423097479873044533 1701537789665388738097925)
                      ·
                        rfl

theorem cell23_3313733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_3313733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313733 prefixEnd_3313733 := by exact prefixLift 3313733
  have htrace : WordTrace (prefixWord ++ tailWord_3313733) baseStart_3313733 baseEnd_3313733 := by
    simpa [prefixWord, tailWord_3313733, baseEnd_3313733] using wordTrace_append hprefix tailTrace_3313733
  have hstable : (prefixWord ++ tailWord_3313733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313733).length < 2 ^ (prefixWord ++ tailWord_3313733).sum := by decide
  have hdescent : baseEnd_3313733 < baseStart_3313733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313757 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3313757 : Nat := 118140960795 + 3313757 * 2 ^ 59
def prefixEnd_3313757 : Nat := 4983230072969 + 3 ^ 40 * 3313757 * 2
def baseEnd_3313757 : Nat := 567183371067032214732605

theorem tailTrace_3313757 : CollatzResearch.WordTrace tailWord_3313757 prefixEnd_3313757 567183371067032214732605 := by
  unfold tailWord_3313757
  simp only [CollatzResearch.WordTrace]
  refine ⟨120862647055831808483555525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80575098037221205655703683 120862647055831808483555525)
  ·
    refine ⟨22661746322968464090666661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120862647055831808483555525 22661746322968464090666661)
    ·
      refine ⟨4249077435556587016999999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22661746322968464090666661 4249077435556587016999999)
      ·
        refine ⟨6373616153334880525499999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4249077435556587016999999 6373616153334880525499999)
        ·
          refine ⟨9560424230002320788249999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6373616153334880525499999 9560424230002320788249999)
          ·
            refine ⟨14340636345003481182374999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9560424230002320788249999 14340636345003481182374999)
            ·
              refine ⟨21510954517505221773562499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14340636345003481182374999 21510954517505221773562499)
              ·
                refine ⟨32266431776257832660343749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21510954517505221773562499 32266431776257832660343749)
                ·
                  refine ⟨6049955958048343623814453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32266431776257832660343749 6049955958048343623814453)
                  ·
                    refine ⟨567183371067032214732605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6049955958048343623814453 567183371067032214732605)
                    ·
                      rfl

theorem cell23_3313757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3313757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313757 prefixEnd_3313757 := by exact prefixLift 3313757
  have htrace : WordTrace (prefixWord ++ tailWord_3313757) baseStart_3313757 baseEnd_3313757 := by
    simpa [prefixWord, tailWord_3313757, baseEnd_3313757] using wordTrace_append hprefix tailTrace_3313757
  have hstable : (prefixWord ++ tailWord_3313757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313757).length < 2 ^ (prefixWord ++ tailWord_3313757).sum := by decide
  have hdescent : baseEnd_3313757 < baseStart_3313757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313760 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 4]
def baseStart_3313760 : Nat := 118140960795 + 3313760 * 2 ^ 59
def prefixEnd_3313760 : Nat := 4983230072969 + 3 ^ 40 * 3313760 * 2
def baseEnd_3313760 : Nat := 1701551653643060132460301

theorem tailTrace_3313760 : CollatzResearch.WordTrace tailWord_3313760 prefixEnd_3313760 1701551653643060132460301 := by
  unfold tailWord_3313760
  simp only [CollatzResearch.WordTrace]
  refine ⟨60431378237410469997957367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80575170983213959997276489 60431378237410469997957367)
  ·
    refine ⟨90647067356115704996936051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60431378237410469997957367 90647067356115704996936051)
    ·
      refine ⟨135970601034173557495404077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90647067356115704996936051 135970601034173557495404077)
      ·
        refine ⟨50988975387815084060776529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135970601034173557495404077 50988975387815084060776529)
        ·
          refine ⟨38241731540861313045582397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50988975387815084060776529 38241731540861313045582397)
          ·
            refine ⟨14340649327822992392093399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38241731540861313045582397 14340649327822992392093399)
            ·
              refine ⟨21510973991734488588140099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14340649327822992392093399 21510973991734488588140099)
              ·
                refine ⟨32266460987601732882210149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21510973991734488588140099 32266460987601732882210149)
                ·
                  refine ⟨6049961435175324915414403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32266460987601732882210149 6049961435175324915414403)
                  ·
                    refine ⟨9074942152762987373121605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6049961435175324915414403 9074942152762987373121605)
                    ·
                      refine ⟨1701551653643060132460301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9074942152762987373121605 1701551653643060132460301)
                      ·
                        rfl

theorem cell23_3313760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_3313760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313760 prefixEnd_3313760 := by exact prefixLift 3313760
  have htrace : WordTrace (prefixWord ++ tailWord_3313760) baseStart_3313760 baseEnd_3313760 := by
    simpa [prefixWord, tailWord_3313760, baseEnd_3313760] using wordTrace_append hprefix tailTrace_3313760
  have hstable : (prefixWord ++ tailWord_3313760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313760).length < 2 ^ (prefixWord ++ tailWord_3313760).sum := by decide
  have hdescent : baseEnd_3313760 < baseStart_3313760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313797 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 2, 2, 3]
def baseStart_3313797 : Nat := 118140960795 + 3313797 * 2 ^ 59
def prefixEnd_3313797 : Nat := 4983230072969 + 3 ^ 40 * 3313797 * 2
def baseEnd_3313797 : Nat := 1701570652427276487697631

theorem tailTrace_3313797 : CollatzResearch.WordTrace tailWord_3313797 prefixEnd_3313797 1701570652427276487697631 := by
  unfold tailWord_3313797
  simp only [CollatzResearch.WordTrace]
  refine ⟨120864105975686895315011645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80576070650457930210007763 120864105975686895315011645)
  ·
    refine ⟨45324039740882585743129367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120864105975686895315011645 45324039740882585743129367)
    ·
      refine ⟨67986059611323878614694051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45324039740882585743129367 67986059611323878614694051)
      ·
        refine ⟨101979089416985817922041077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67986059611323878614694051 101979089416985817922041077)
        ·
          refine ⟨9560539632842420430191351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101979089416985817922041077 9560539632842420430191351)
          ·
            refine ⟨14340809449263630645287027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9560539632842420430191351 14340809449263630645287027)
            ·
              refine ⟨21511214173895445967930541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14340809449263630645287027 21511214173895445967930541)
              ·
                refine ⟨8066705315210792237973953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21511214173895445967930541 8066705315210792237973953)
                ·
                  refine ⟨6050028986408094178480465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8066705315210792237973953 6050028986408094178480465)
                  ·
                    refine ⟨4537521739806070633860349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6050028986408094178480465 4537521739806070633860349)
                    ·
                      refine ⟨1701570652427276487697631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4537521739806070633860349 1701570652427276487697631)
                      ·
                        rfl

theorem cell23_3313797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_3313797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313797 prefixEnd_3313797 := by exact prefixLift 3313797
  have htrace : WordTrace (prefixWord ++ tailWord_3313797) baseStart_3313797 baseEnd_3313797 := by
    simpa [prefixWord, tailWord_3313797, baseEnd_3313797] using wordTrace_append hprefix tailTrace_3313797
  have hstable : (prefixWord ++ tailWord_3313797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313797).length < 2 ^ (prefixWord ++ tailWord_3313797).sum := by decide
  have hdescent : baseEnd_3313797 < baseStart_3313797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313803 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 8]
def baseStart_3313803 : Nat := 118140960795 + 3313803 * 2 ^ 59
def prefixEnd_3313803 : Nat := 4983230072969 + 3 ^ 40 * 3313803 * 2
def baseEnd_3313803 : Nat := 1701573733311203464222603

theorem tailTrace_3313803 : CollatzResearch.WordTrace tailWord_3313803 prefixEnd_3313803 1701573733311203464222603 := by
  unfold tailWord_3313803
  simp only [CollatzResearch.WordTrace]
  refine ⟨120864324813665158339730063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80576216542443438893153375 120864324813665158339730063)
  ·
    refine ⟨181296487220497737509595095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120864324813665158339730063 181296487220497737509595095)
    ·
      refine ⟨271944730830746606264392643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181296487220497737509595095 271944730830746606264392643)
      ·
        refine ⟨407917096246119909396588965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271944730830746606264392643 407917096246119909396588965)
        ·
          refine ⟨76484455546147483011860431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407917096246119909396588965 76484455546147483011860431)
          ·
            refine ⟨114726683319221224517790647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76484455546147483011860431 114726683319221224517790647)
            ·
              refine ⟨172090024978831836776685971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114726683319221224517790647 172090024978831836776685971)
              ·
                refine ⟨258135037468247755165028957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172090024978831836776685971 258135037468247755165028957)
                ·
                  refine ⟨96800639050592908186885859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258135037468247755165028957 96800639050592908186885859)
                  ·
                    refine ⟨145200958575889362280328789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96800639050592908186885859 145200958575889362280328789)
                    ·
                      refine ⟨1701573733311203464222603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 145200958575889362280328789 1701573733311203464222603)
                      ·
                        rfl

theorem cell23_3313803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_3313803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313803 prefixEnd_3313803 := by exact prefixLift 3313803
  have htrace : WordTrace (prefixWord ++ tailWord_3313803) baseStart_3313803 baseEnd_3313803 := by
    simpa [prefixWord, tailWord_3313803, baseEnd_3313803] using wordTrace_append hprefix tailTrace_3313803
  have hstable : (prefixWord ++ tailWord_3313803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313803).length < 2 ^ (prefixWord ++ tailWord_3313803).sum := by decide
  have hdescent : baseEnd_3313803 < baseStart_3313803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313820 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3313820 : Nat := 118140960795 + 3313820 * 2 ^ 59
def prefixEnd_3313820 : Nat := 4983230072969 + 3 ^ 40 * 3313820 * 2
def baseEnd_3313820 : Nat := 1701582462482329897710025

theorem tailTrace_3313820 : CollatzResearch.WordTrace tailWord_3313820 prefixEnd_3313820 1701582462482329897710025 := by
  unfold tailWord_3313820
  simp only [CollatzResearch.WordTrace]
  refine ⟨60432472427301785121549457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80576629903069046828732609 60432472427301785121549457)
  ·
    refine ⟨45324354320476338841162093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60432472427301785121549457 45324354320476338841162093)
    ·
      refine ⟨16996632870178627065435785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45324354320476338841162093 16996632870178627065435785)
      ·
        refine ⟨12747474652633970299076839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16996632870178627065435785 12747474652633970299076839)
        ·
          refine ⟨19121211978950955448615259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12747474652633970299076839 19121211978950955448615259)
          ·
            refine ⟨28681817968426433172922889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19121211978950955448615259 28681817968426433172922889)
            ·
              refine ⟨21511363476319824879692167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28681817968426433172922889 21511363476319824879692167)
              ·
                refine ⟨32267045214479737319538251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21511363476319824879692167 32267045214479737319538251)
                ·
                  refine ⟨48400567821719605979307377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32267045214479737319538251 48400567821719605979307377)
                  ·
                    refine ⟨36300425866289704484480533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48400567821719605979307377 36300425866289704484480533)
                    ·
                      refine ⟨1701582462482329897710025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36300425866289704484480533 1701582462482329897710025)
                      ·
                        rfl

theorem cell23_3313820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3313820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313820 prefixEnd_3313820 := by exact prefixLift 3313820
  have htrace : WordTrace (prefixWord ++ tailWord_3313820) baseStart_3313820 baseEnd_3313820 := by
    simpa [prefixWord, tailWord_3313820, baseEnd_3313820] using wordTrace_append hprefix tailTrace_3313820
  have hstable : (prefixWord ++ tailWord_3313820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313820).length < 2 ^ (prefixWord ++ tailWord_3313820).sum := by decide
  have hdescent : baseEnd_3313820 < baseStart_3313820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313821 : List Nat := [1, 4, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_3313821 : Nat := 118140960795 + 3313821 * 2 ^ 59
def prefixEnd_3313821 : Nat := 4983230072969 + 3 ^ 40 * 3313821 * 2
def baseEnd_3313821 : Nat := 567194325320994797932507

theorem tailTrace_3313821 : CollatzResearch.WordTrace tailWord_3313821 prefixEnd_3313821 567194325320994797932507 := by
  unfold tailWord_3313821
  simp only [CollatzResearch.WordTrace]
  refine ⟨120864981327599947413885317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80576654218399964942590211 120864981327599947413885317)
  ·
    refine ⟨22662183998924990140103497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120864981327599947413885317 22662183998924990140103497)
    ·
      refine ⟨16996637999193742605077623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22662183998924990140103497 16996637999193742605077623)
      ·
        refine ⟨25494956998790613907616435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16996637999193742605077623 25494956998790613907616435)
        ·
          refine ⟨38242435498185920861424653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25494956998790613907616435 38242435498185920861424653)
          ·
            refine ⟨14340913311819720323034245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38242435498185920861424653 14340913311819720323034245)
            ·
              refine ⟨2688921245966197560568921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14340913311819720323034245 2688921245966197560568921)
              ·
                refine ⟨2016690934474648170426691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2688921245966197560568921 2016690934474648170426691)
                ·
                  refine ⟨3025036401711972255640037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016690934474648170426691 3025036401711972255640037)
                  ·
                    refine ⟨567194325320994797932507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3025036401711972255640037 567194325320994797932507)
                    ·
                      rfl

theorem cell23_3313821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_3313821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313821 prefixEnd_3313821 := by exact prefixLift 3313821
  have htrace : WordTrace (prefixWord ++ tailWord_3313821) baseStart_3313821 baseEnd_3313821 := by
    simpa [prefixWord, tailWord_3313821, baseEnd_3313821] using wordTrace_append hprefix tailTrace_3313821
  have hstable : (prefixWord ++ tailWord_3313821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313821).length < 2 ^ (prefixWord ++ tailWord_3313821).sum := by decide
  have hdescent : baseEnd_3313821 < baseStart_3313821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313867 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 4]
def baseStart_3313867 : Nat := 118140960795 + 3313867 * 2 ^ 59
def prefixEnd_3313867 : Nat := 4983230072969 + 3 ^ 40 * 3313867 * 2
def baseEnd_3313867 : Nat := 1701606596073091213822309

theorem tailTrace_3313867 : CollatzResearch.WordTrace tailWord_3313867 prefixEnd_3313867 1701606596073091213822309 := by
  unfold tailWord_3313867
  simp only [CollatzResearch.WordTrace]
  refine ⟨120866659085433297270059855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80577772723622198180039903 120866659085433297270059855)
  ·
    refine ⟨181299988628149945905089783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120866659085433297270059855 181299988628149945905089783)
    ·
      refine ⟨271949982942224918857634675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181299988628149945905089783 271949982942224918857634675)
      ·
        refine ⟨407924974413337378286452013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271949982942224918857634675 407924974413337378286452013)
        ·
          refine ⟨152971865405001516857419505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407924974413337378286452013 152971865405001516857419505)
          ·
            refine ⟨114728899053751137643064629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152971865405001516857419505 114728899053751137643064629)
            ·
              refine ⟨10755834286289169154037309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114728899053751137643064629 10755834286289169154037309)
              ·
                refine ⟨4033437857358438432763991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10755834286289169154037309 4033437857358438432763991)
                ·
                  refine ⟨6050156786037657649145987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033437857358438432763991 6050156786037657649145987)
                  ·
                    refine ⟨9075235179056486473718981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6050156786037657649145987 9075235179056486473718981)
                    ·
                      refine ⟨1701606596073091213822309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9075235179056486473718981 1701606596073091213822309)
                      ·
                        rfl

theorem cell23_3313867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 4].length) (baseStart_3313867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313867 prefixEnd_3313867 := by exact prefixLift 3313867
  have htrace : WordTrace (prefixWord ++ tailWord_3313867) baseStart_3313867 baseEnd_3313867 := by
    simpa [prefixWord, tailWord_3313867, baseEnd_3313867] using wordTrace_append hprefix tailTrace_3313867
  have hstable : (prefixWord ++ tailWord_3313867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313867).length < 2 ^ (prefixWord ++ tailWord_3313867).sum := by decide
  have hdescent : baseEnd_3313867 < baseStart_3313867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313878 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3313878 : Nat := 118140960795 + 3313878 * 2 ^ 59
def prefixEnd_3313878 : Nat := 4983230072969 + 3 ^ 40 * 3313878 * 2
def baseEnd_3313878 : Nat := 1701612244360290670784759

theorem tailTrace_3313878 : CollatzResearch.WordTrace tailWord_3313878 prefixEnd_3313878 1701612244360290670784759 := by
  unfold tailWord_3313878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7554191268024590384294393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80578040192262297432473525 7554191268024590384294393)
  ·
    refine ⟨5665643451018442788220795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7554191268024590384294393 5665643451018442788220795)
    ·
      refine ⟨8498465176527664182331193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5665643451018442788220795 8498465176527664182331193)
      ·
        refine ⟨6373848882395748136748395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8498465176527664182331193 6373848882395748136748395)
        ·
          refine ⟨9560773323593622205122593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6373848882395748136748395 9560773323593622205122593)
          ·
            refine ⟨7170579992695216653841945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9560773323593622205122593 7170579992695216653841945)
            ·
              refine ⟨5377934994521412490381459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7170579992695216653841945 5377934994521412490381459)
              ·
                refine ⟨8066902491782118735572189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5377934994521412490381459 8066902491782118735572189)
                ·
                  refine ⟨3025088434418294525839571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8066902491782118735572189 3025088434418294525839571)
                  ·
                    refine ⟨4537632651627441788759357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3025088434418294525839571 4537632651627441788759357)
                    ·
                      refine ⟨1701612244360290670784759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4537632651627441788759357 1701612244360290670784759)
                      ·
                        rfl

theorem cell23_3313878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3313878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313878 prefixEnd_3313878 := by exact prefixLift 3313878
  have htrace : WordTrace (prefixWord ++ tailWord_3313878) baseStart_3313878 baseEnd_3313878 := by
    simpa [prefixWord, tailWord_3313878, baseEnd_3313878] using wordTrace_append hprefix tailTrace_3313878
  have hstable : (prefixWord ++ tailWord_3313878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313878).length < 2 ^ (prefixWord ++ tailWord_3313878).sum := by decide
  have hdescent : baseEnd_3313878 < baseStart_3313878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313901 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3313901 : Nat := 118140960795 + 3313901 * 2 ^ 59
def prefixEnd_3313901 : Nat := 4983230072969 + 3 ^ 40 * 3313901 * 2
def baseEnd_3313901 : Nat := 1701624054415344080797153

theorem tailTrace_3313901 : CollatzResearch.WordTrace tailWord_3313901 prefixEnd_3313901 1701624054415344080797153 := by
  unfold tailWord_3313901
  simp only [CollatzResearch.WordTrace]
  refine ⟨120867899167310121076797557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80578599444873414051198371 120867899167310121076797557)
  ·
    refine ⟨11331365546935323850949771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120867899167310121076797557 11331365546935323850949771)
    ·
      refine ⟨16997048320402985776424657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11331365546935323850949771 16997048320402985776424657)
      ·
        refine ⟨12747786240302239332318493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16997048320402985776424657 12747786240302239332318493)
        ·
          refine ⟨4780419840113339749619435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12747786240302239332318493 4780419840113339749619435)
          ·
            refine ⟨7170629760170009624429153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4780419840113339749619435 7170629760170009624429153)
            ·
              refine ⟨5377972320127507218321865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7170629760170009624429153 5377972320127507218321865)
              ·
                refine ⟨4033479240095630413741399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5377972320127507218321865 4033479240095630413741399)
                ·
                  refine ⟨6050218860143445620612099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033479240095630413741399 6050218860143445620612099)
                  ·
                    refine ⟨9075328290215168430918149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6050218860143445620612099 9075328290215168430918149)
                    ·
                      refine ⟨1701624054415344080797153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9075328290215168430918149 1701624054415344080797153)
                      ·
                        rfl

theorem cell23_3313901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3313901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313901 prefixEnd_3313901 := by exact prefixLift 3313901
  have htrace : WordTrace (prefixWord ++ tailWord_3313901) baseStart_3313901 baseEnd_3313901 := by
    simpa [prefixWord, tailWord_3313901, baseEnd_3313901] using wordTrace_append hprefix tailTrace_3313901
  have hstable : (prefixWord ++ tailWord_3313901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313901).length < 2 ^ (prefixWord ++ tailWord_3313901).sum := by decide
  have hdescent : baseEnd_3313901 < baseStart_3313901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313917 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_3313917 : Nat := 118140960795 + 3313917 * 2 ^ 59
def prefixEnd_3313917 : Nat := 4983230072969 + 3 ^ 40 * 3313917 * 2
def baseEnd_3313917 : Nat := 1701632270105816018197079

theorem tailTrace_3313917 : CollatzResearch.WordTrace tailWord_3313917 prefixEnd_3313917 1701632270105816018197079 := by
  unfold tailWord_3313917
  simp only [CollatzResearch.WordTrace]
  refine ⟨120868482735252155809380005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80578988490168103872920003 120868482735252155809380005)
  ·
    refine ⟨22662840512859779214258751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120868482735252155809380005 22662840512859779214258751)
    ·
      refine ⟨33994260769289668821388127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22662840512859779214258751 33994260769289668821388127)
      ·
        refine ⟨50991391153934503232082191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33994260769289668821388127 50991391153934503232082191)
        ·
          refine ⟨76487086730901754848123287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50991391153934503232082191 76487086730901754848123287)
          ·
            refine ⟨114730630096352632272184931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76487086730901754848123287 114730630096352632272184931)
            ·
              refine ⟨172095945144528948408277397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114730630096352632272184931 172095945144528948408277397)
              ·
                refine ⟨8066997428649794456638003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172095945144528948408277397 8066997428649794456638003)
                ·
                  refine ⟨12100496142974691684957005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8066997428649794456638003 12100496142974691684957005)
                  ·
                    refine ⟨4537686053615509381858877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12100496142974691684957005 4537686053615509381858877)
                    ·
                      refine ⟨1701632270105816018197079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4537686053615509381858877 1701632270105816018197079)
                      ·
                        rfl

theorem cell23_3313917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_3313917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313917 prefixEnd_3313917 := by exact prefixLift 3313917
  have htrace : WordTrace (prefixWord ++ tailWord_3313917) baseStart_3313917 baseEnd_3313917 := by
    simpa [prefixWord, tailWord_3313917, baseEnd_3313917] using wordTrace_append hprefix tailTrace_3313917
  have hstable : (prefixWord ++ tailWord_3313917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313917).length < 2 ^ (prefixWord ++ tailWord_3313917).sum := by decide
  have hdescent : baseEnd_3313917 < baseStart_3313917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313924 : List Nat := [2, 3, 2, 2, 4, 1, 9]
def baseStart_3313924 : Nat := 118140960795 + 3313924 * 2 ^ 59
def prefixEnd_3313924 : Nat := 4983230072969 + 3 ^ 40 * 3313924 * 2
def baseEnd_3313924 : Nat := 21007850178646882602587

theorem tailTrace_3313924 : CollatzResearch.WordTrace tailWord_3313924 prefixEnd_3313924 21007850178646882602587 := by
  unfold tailWord_3313924
  simp only [CollatzResearch.WordTrace]
  refine ⟨60434369023113398002442413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80579158697484530669923217 60434369023113398002442413)
  ·
    refine ⟨22662888383667524250915905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60434369023113398002442413 22662888383667524250915905)
    ·
      refine ⟨16997166287750643188186929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22662888383667524250915905 16997166287750643188186929)
      ·
        refine ⟨12747874715812982391140197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16997166287750643188186929 12747874715812982391140197)
        ·
          refine ⟨2390226509214934198338787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12747874715812982391140197 2390226509214934198338787)
          ·
            refine ⟨3585339763822401297508181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390226509214934198338787 3585339763822401297508181)
            ·
              refine ⟨21007850178646882602587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3585339763822401297508181 21007850178646882602587)
              ·
                rfl

theorem cell23_3313924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 9].length) (baseStart_3313924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313924 prefixEnd_3313924 := by exact prefixLift 3313924
  have htrace : WordTrace (prefixWord ++ tailWord_3313924) baseStart_3313924 baseEnd_3313924 := by
    simpa [prefixWord, tailWord_3313924, baseEnd_3313924] using wordTrace_append hprefix tailTrace_3313924
  have hstable : (prefixWord ++ tailWord_3313924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313924).length < 2 ^ (prefixWord ++ tailWord_3313924).sum := by decide
  have hdescent : baseEnd_3313924 < baseStart_3313924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313934 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3313934 : Nat := 118140960795 + 3313934 * 2 ^ 59
def prefixEnd_3313934 : Nat := 4983230072969 + 3 ^ 40 * 3313934 * 2
def baseEnd_3313934 : Nat := 1701640999276942451684501

theorem tailTrace_3313934 : CollatzResearch.WordTrace tailWord_3313934 prefixEnd_3313934 1701640999276942451684501 := by
  unfold tailWord_3313934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15108637847023820964093607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80579401850793711808499237 15108637847023820964093607)
  ·
    refine ⟨22662956770535731446140411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15108637847023820964093607 22662956770535731446140411)
    ·
      refine ⟨33994435155803597169210617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22662956770535731446140411 33994435155803597169210617)
      ·
        refine ⟨25495826366852697876907963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33994435155803597169210617 25495826366852697876907963)
        ·
          refine ⟨38243739550279046815361945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25495826366852697876907963 38243739550279046815361945)
          ·
            refine ⟨28682804662709285111521459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38243739550279046815361945 28682804662709285111521459)
            ·
              refine ⟨43024206994063927667282189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28682804662709285111521459 43024206994063927667282189)
              ·
                refine ⟨16134077622773972875230821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43024206994063927667282189 16134077622773972875230821)
                ·
                  refine ⟨3025139554270119914105779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16134077622773972875230821 3025139554270119914105779)
                  ·
                    refine ⟨4537709331405179871158669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3025139554270119914105779 4537709331405179871158669)
                    ·
                      refine ⟨1701640999276942451684501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4537709331405179871158669 1701640999276942451684501)
                      ·
                        rfl

theorem cell23_3313934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3313934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313934 prefixEnd_3313934 := by exact prefixLift 3313934
  have htrace : WordTrace (prefixWord ++ tailWord_3313934) baseStart_3313934 baseEnd_3313934 := by
    simpa [prefixWord, tailWord_3313934, baseEnd_3313934] using wordTrace_append hprefix tailTrace_3313934
  have hstable : (prefixWord ++ tailWord_3313934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313934).length < 2 ^ (prefixWord ++ tailWord_3313934).sum := by decide
  have hdescent : baseEnd_3313934 < baseStart_3313934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313944 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 3, 3, 2]
def baseStart_3313944 : Nat := 118140960795 + 3313944 * 2 ^ 59
def prefixEnd_3313944 : Nat := 4983230072969 + 3 ^ 40 * 3313944 * 2
def baseEnd_3313944 : Nat := 1701646134083487412559455

theorem tailTrace_3313944 : CollatzResearch.WordTrace tailWord_3313944 prefixEnd_3313944 1701646134083487412559455 := by
  unfold tailWord_3313944
  simp only [CollatzResearch.WordTrace]
  refine ⟨60434733753077169710306443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80579645004102892947075257 60434733753077169710306443)
  ·
    refine ⟨90652100629615754565459665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60434733753077169710306443 90652100629615754565459665)
    ·
      refine ⟨67989075472211815924094749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90652100629615754565459665 67989075472211815924094749)
      ·
        refine ⟨25495903302079430971535531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67989075472211815924094749 25495903302079430971535531)
        ·
          refine ⟨38243854953119146457303297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25495903302079430971535531 38243854953119146457303297)
          ·
            refine ⟨28682891214839359842977473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38243854953119146457303297 28682891214839359842977473)
            ·
              refine ⟨21512168411129519882233105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28682891214839359842977473 21512168411129519882233105)
              ·
                refine ⟨16134126308347139911674829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21512168411129519882233105 16134126308347139911674829)
                ·
                  refine ⟨6050297365630177466878061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16134126308347139911674829 6050297365630177466878061)
                  ·
                    refine ⟨2268861512111316550079273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6050297365630177466878061 2268861512111316550079273)
                    ·
                      refine ⟨1701646134083487412559455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2268861512111316550079273 1701646134083487412559455)
                      ·
                        rfl

theorem cell23_3313944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_3313944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313944 prefixEnd_3313944 := by exact prefixLift 3313944
  have htrace : WordTrace (prefixWord ++ tailWord_3313944) baseStart_3313944 baseEnd_3313944 := by
    simpa [prefixWord, tailWord_3313944, baseEnd_3313944] using wordTrace_append hprefix tailTrace_3313944
  have hstable : (prefixWord ++ tailWord_3313944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313944).length < 2 ^ (prefixWord ++ tailWord_3313944).sum := by decide
  have hdescent : baseEnd_3313944 < baseStart_3313944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313951 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 2, 1, 3]
def baseStart_3313951 : Nat := 118140960795 + 3313951 * 2 ^ 59
def prefixEnd_3313951 : Nat := 4983230072969 + 3 ^ 40 * 3313951 * 2
def baseEnd_3313951 : Nat := 1701649728448068885171923

theorem tailTrace_3313951 : CollatzResearch.WordTrace tailWord_3313951 prefixEnd_3313951 1701649728448068885171923 := by
  unfold tailWord_3313951
  simp only [CollatzResearch.WordTrace]
  refine ⟨120869722817128979616117707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80579815211419319744078471 120869722817128979616117707)
  ·
    refine ⟨181304584225693469424176561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120869722817128979616117707 181304584225693469424176561)
    ·
      refine ⟨135978438169270102068132421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181304584225693469424176561 135978438169270102068132421)
      ·
        refine ⟨25495957156738144137774829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135978438169270102068132421 25495957156738144137774829)
        ·
          refine ⟨9560983933776804051665561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25495957156738144137774829 9560983933776804051665561)
          ·
            refine ⟨7170737950332603038749171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9560983933776804051665561 7170737950332603038749171)
            ·
              refine ⟨10756106925498904558123757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7170737950332603038749171 10756106925498904558123757)
              ·
                refine ⟨4033540097062089209296409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10756106925498904558123757 4033540097062089209296409)
                ·
                  refine ⟨3025155072796566906972307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4033540097062089209296409 3025155072796566906972307)
                  ·
                    refine ⟨4537732609194850360458461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3025155072796566906972307 4537732609194850360458461)
                    ·
                      refine ⟨1701649728448068885171923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4537732609194850360458461 1701649728448068885171923)
                      ·
                        rfl

theorem cell23_3313951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_3313951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313951 prefixEnd_3313951 := by exact prefixLift 3313951
  have htrace : WordTrace (prefixWord ++ tailWord_3313951) baseStart_3313951 baseEnd_3313951 := by
    simpa [prefixWord, tailWord_3313951, baseEnd_3313951] using wordTrace_append hprefix tailTrace_3313951
  have hstable : (prefixWord ++ tailWord_3313951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313951).length < 2 ^ (prefixWord ++ tailWord_3313951).sum := by decide
  have hdescent : baseEnd_3313951 < baseStart_3313951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313978 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2]
def baseStart_3313978 : Nat := 118140960795 + 3313978 * 2 ^ 59
def prefixEnd_3313978 : Nat := 4983230072969 + 3 ^ 40 * 3313978 * 2
def baseEnd_3313978 : Nat := 1701663592425740279534299

theorem tailTrace_3313978 : CollatzResearch.WordTrace tailWord_3313978 prefixEnd_3313978 1701663592425740279534299 := by
  unfold tailWord_3313978
  simp only [CollatzResearch.WordTrace]
  refine ⟨30217676897007790806837647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80580471725354108818233725 30217676897007790806837647)
  ·
    refine ⟨45326515345511686210256471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30217676897007790806837647 45326515345511686210256471)
    ·
      refine ⟨67989773018267529315384707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45326515345511686210256471 67989773018267529315384707)
      ·
        refine ⟨101984659527401293973077061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67989773018267529315384707 101984659527401293973077061)
        ·
          refine ⟨19122123661387742619951949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101984659527401293973077061 19122123661387742619951949)
          ·
            refine ⟨7170796373020403482481981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19122123661387742619951949 7170796373020403482481981)
            ·
              refine ⟨2689048639882651305930743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7170796373020403482481981 2689048639882651305930743)
              ·
                refine ⟨4033572959823976958896115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689048639882651305930743 4033572959823976958896115)
                ·
                  refine ⟨6050359439735965438344173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033572959823976958896115 6050359439735965438344173)
                  ·
                    refine ⟨2268884789900987039379065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6050359439735965438344173 2268884789900987039379065)
                    ·
                      refine ⟨1701663592425740279534299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2268884789900987039379065 1701663592425740279534299)
                      ·
                        rfl

theorem cell23_3313978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2].length) (baseStart_3313978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3313978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3313978 prefixEnd_3313978 := by exact prefixLift 3313978
  have htrace : WordTrace (prefixWord ++ tailWord_3313978) baseStart_3313978 baseEnd_3313978 := by
    simpa [prefixWord, tailWord_3313978, baseEnd_3313978] using wordTrace_append hprefix tailTrace_3313978
  have hstable : (prefixWord ++ tailWord_3313978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313978).length < 2 ^ (prefixWord ++ tailWord_3313978).sum := by decide
  have hdescent : baseEnd_3313978 < baseStart_3313978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314004 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_3314004 : Nat := 118140960795 + 3314004 * 2 ^ 59
def prefixEnd_3314004 : Nat := 4983230072969 + 3 ^ 40 * 3314004 * 2
def baseEnd_3314004 : Nat := 1701676942922757177809179

theorem tailTrace_3314004 : CollatzResearch.WordTrace tailWord_3314004 prefixEnd_3314004 1701676942922757177809179 := by
  unfold tailWord_3314004
  simp only [CollatzResearch.WordTrace]
  refine ⟨60435827942968484833898533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80581103923957979778531377 60435827942968484833898533)
  ·
    refine ⟨11331717739306590906355975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60435827942968484833898533 11331717739306590906355975)
    ·
      refine ⟨16997576608959886359533963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11331717739306590906355975 16997576608959886359533963)
      ·
        refine ⟨25496364913439829539300945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16997576608959886359533963 25496364913439829539300945)
        ·
          refine ⟨19122273685079872154475709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25496364913439829539300945 19122273685079872154475709)
          ·
            refine ⟨7170852631904952057928391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19122273685079872154475709 7170852631904952057928391)
            ·
              refine ⟨10756278947857428086892587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7170852631904952057928391 10756278947857428086892587)
              ·
                refine ⟨16134418421786142130338881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10756278947857428086892587 16134418421786142130338881)
                ·
                  refine ⟨12100813816339606597754161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16134418421786142130338881 12100813816339606597754161)
                  ·
                    refine ⟨9075610362254704948315621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12100813816339606597754161 9075610362254704948315621)
                    ·
                      refine ⟨1701676942922757177809179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9075610362254704948315621 1701676942922757177809179)
                      ·
                        rfl

theorem cell23_3314004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_3314004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314004 prefixEnd_3314004 := by exact prefixLift 3314004
  have htrace : WordTrace (prefixWord ++ tailWord_3314004) baseStart_3314004 baseEnd_3314004 := by
    simpa [prefixWord, tailWord_3314004, baseEnd_3314004] using wordTrace_append hprefix tailTrace_3314004
  have hstable : (prefixWord ++ tailWord_3314004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314004).length < 2 ^ (prefixWord ++ tailWord_3314004).sum := by decide
  have hdescent : baseEnd_3314004 < baseStart_3314004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314084 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_3314084 : Nat := 118140960795 + 3314084 * 2 ^ 59
def prefixEnd_3314084 : Nat := 4983230072969 + 3 ^ 40 * 3314084 * 2
def baseEnd_3314084 : Nat := 1701718021375116864808811

theorem tailTrace_3314084 : CollatzResearch.WordTrace tailWord_3314084 prefixEnd_3314084 1701718021375116864808811 := by
  unfold tailWord_3314084
  simp only [CollatzResearch.WordTrace]
  refine ⟨60437286862823571665354653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80583049150431428887139537 60437286862823571665354653)
  ·
    refine ⟨22663982573558839374507995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60437286862823571665354653 22663982573558839374507995)
    ·
      refine ⟨33995973860338259061761993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22663982573558839374507995 33995973860338259061761993)
      ·
        refine ⟨25496980395253694296321495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33995973860338259061761993 25496980395253694296321495)
        ·
          refine ⟨38245470592880541444482243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25496980395253694296321495 38245470592880541444482243)
          ·
            refine ⟨57368205889320812166723365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38245470592880541444482243 57368205889320812166723365)
            ·
              refine ⟨10756538604247652281260631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57368205889320812166723365 10756538604247652281260631)
              ·
                refine ⟨16134807906371478421890947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10756538604247652281260631 16134807906371478421890947)
                ·
                  refine ⟨24202211859557217632836421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16134807906371478421890947 24202211859557217632836421)
                  ·
                    refine ⟨4537914723666978306156829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24202211859557217632836421 4537914723666978306156829)
                    ·
                      refine ⟨1701718021375116864808811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4537914723666978306156829 1701718021375116864808811)
                      ·
                        rfl

theorem cell23_3314084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_3314084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314084 prefixEnd_3314084 := by exact prefixLift 3314084
  have htrace : WordTrace (prefixWord ++ tailWord_3314084) baseStart_3314084 baseEnd_3314084 := by
    simpa [prefixWord, tailWord_3314084, baseEnd_3314084] using wordTrace_append hprefix tailTrace_3314084
  have hstable : (prefixWord ++ tailWord_3314084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314084).length < 2 ^ (prefixWord ++ tailWord_3314084).sum := by decide
  have hdescent : baseEnd_3314084 < baseStart_3314084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314108 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 3, 4]
def baseStart_3314108 : Nat := 118140960795 + 3314108 * 2 ^ 59
def prefixEnd_3314108 : Nat := 4983230072969 + 3 ^ 40 * 3314108 * 2
def baseEnd_3314108 : Nat := 567243448303608256969567

theorem tailTrace_3314108 : CollatzResearch.WordTrace tailWord_3314108 prefixEnd_3314108 567243448303608256969567 := by
  unfold tailWord_3314108
  simp only [CollatzResearch.WordTrace]
  refine ⟨60437724538780097714791489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80583632718373463619721985 60437724538780097714791489)
  ·
    refine ⟨45328293404085073286093617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60437724538780097714791489 45328293404085073286093617)
    ·
      refine ⟨33996220053063804964570213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45328293404085073286093617 33996220053063804964570213)
      ·
        refine ⟨6374291259949463430856915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33996220053063804964570213 6374291259949463430856915)
        ·
          refine ⟨9561436889924195146285373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6374291259949463430856915 9561436889924195146285373)
          ·
            refine ⟨3585538833721573179857015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9561436889924195146285373 3585538833721573179857015)
            ·
              refine ⟨5378308250582359769785523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585538833721573179857015 5378308250582359769785523)
              ·
                refine ⟨8067462375873539654678285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5378308250582359769785523 8067462375873539654678285)
                ·
                  refine ⟨3025298390952577370504357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8067462375873539654678285 3025298390952577370504357)
                  ·
                    refine ⟨567243448303608256969567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3025298390952577370504357 567243448303608256969567)
                    ·
                      rfl

theorem cell23_3314108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_3314108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314108 prefixEnd_3314108 := by exact prefixLift 3314108
  have htrace : WordTrace (prefixWord ++ tailWord_3314108) baseStart_3314108 baseEnd_3314108 := by
    simpa [prefixWord, tailWord_3314108, baseEnd_3314108] using wordTrace_append hprefix tailTrace_3314108
  have hstable : (prefixWord ++ tailWord_3314108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314108).length < 2 ^ (prefixWord ++ tailWord_3314108).sum := by decide
  have hdescent : baseEnd_3314108 < baseStart_3314108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314158 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_3314158 : Nat := 118140960795 + 3314158 * 2 ^ 59
def prefixEnd_3314158 : Nat := 4983230072969 + 3 ^ 40 * 3314158 * 2
def baseEnd_3314158 : Nat := 1701756018943549575283471

theorem tailTrace_3314158 : CollatzResearch.WordTrace tailWord_3314158 prefixEnd_3314158 1701756018943549575283471 := by
  unfold tailWord_3314158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109659090922381746112891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80584848484919369312602085 15109659090922381746112891)
  ·
    refine ⟨22664488636383572619169337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15109659090922381746112891 22664488636383572619169337)
    ·
      refine ⟨16998366477287679464377003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22664488636383572619169337 16998366477287679464377003)
      ·
        refine ⟨25497549715931519196565505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16998366477287679464377003 25497549715931519196565505)
        ·
          refine ⟨19123162286948639397424129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25497549715931519196565505 19123162286948639397424129)
          ·
            refine ⟨14342371715211479548068097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19123162286948639397424129 14342371715211479548068097)
            ·
              refine ⟨10756778786408609661051073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14342371715211479548068097 10756778786408609661051073)
              ·
                refine ⟨8067584089806457245788305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10756778786408609661051073 8067584089806457245788305)
                ·
                  refine ⟨6050688067354842934341229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8067584089806457245788305 6050688067354842934341229)
                  ·
                    refine ⟨2269008025258066100377961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6050688067354842934341229 2269008025258066100377961)
                    ·
                      refine ⟨1701756018943549575283471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269008025258066100377961 1701756018943549575283471)
                      ·
                        rfl

theorem cell23_3314158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_3314158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314158 prefixEnd_3314158 := by exact prefixLift 3314158
  have htrace : WordTrace (prefixWord ++ tailWord_3314158) baseStart_3314158 baseEnd_3314158 := by
    simpa [prefixWord, tailWord_3314158, baseEnd_3314158] using wordTrace_append hprefix tailTrace_3314158
  have hstable : (prefixWord ++ tailWord_3314158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314158).length < 2 ^ (prefixWord ++ tailWord_3314158).sum := by decide
  have hdescent : baseEnd_3314158 < baseStart_3314158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314181 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 2, 4]
def baseStart_3314181 : Nat := 118140960795 + 3314181 * 2 ^ 59
def prefixEnd_3314181 : Nat := 4983230072969 + 3 ^ 40 * 3314181 * 2
def baseEnd_3314181 : Nat := 567255942999534328431955

theorem tailTrace_3314181 : CollatzResearch.WordTrace tailWord_3314181 prefixEnd_3314181 567255942999534328431955 := by
  unfold tailWord_3314181
  simp only [CollatzResearch.WordTrace]
  refine ⟨120878111606295728896990397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80585407737530485931326931 120878111606295728896990397)
  ·
    refine ⟨45329291852360898336371399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120878111606295728896990397 45329291852360898336371399)
    ·
      refine ⟨67993937778541347504557099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45329291852360898336371399 67993937778541347504557099)
      ·
        refine ⟨101990906667812021256835649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67993937778541347504557099 101990906667812021256835649)
        ·
          refine ⟨76493180000859015942626737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101990906667812021256835649 76493180000859015942626737)
          ·
            refine ⟨57369885000644261956970053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76493180000859015942626737 57369885000644261956970053)
            ·
              refine ⟨10756853437620799116931885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57369885000644261956970053 10756853437620799116931885)
              ·
                refine ⟨4033820039107799668849457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10756853437620799116931885 4033820039107799668849457)
                ·
                  refine ⟨3025365029330849751637093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4033820039107799668849457 3025365029330849751637093)
                  ·
                    refine ⟨567255942999534328431955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3025365029330849751637093 567255942999534328431955)
                    ·
                      rfl

theorem cell23_3314181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_3314181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314181 prefixEnd_3314181 := by exact prefixLift 3314181
  have htrace : WordTrace (prefixWord ++ tailWord_3314181) baseStart_3314181 baseEnd_3314181 := by
    simpa [prefixWord, tailWord_3314181, baseEnd_3314181] using wordTrace_append hprefix tailTrace_3314181
  have hstable : (prefixWord ++ tailWord_3314181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314181).length < 2 ^ (prefixWord ++ tailWord_3314181).sum := by decide
  have hdescent : baseEnd_3314181 < baseStart_3314181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314182 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3314182 : Nat := 118140960795 + 3314182 * 2 ^ 59
def prefixEnd_3314182 : Nat := 4983230072969 + 3 ^ 40 * 3314182 * 2
def baseEnd_3314182 : Nat := 1701768342479257481383361

theorem tailTrace_3314182 : CollatzResearch.WordTrace tailWord_3314182 prefixEnd_3314182 1701768342479257481383361 := by
  unfold tailWord_3314182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3777442127477878314618025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80585432052861404045184533 3777442127477878314618025)
  ·
    refine ⟨2833081595608408735963519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3777442127477878314618025 2833081595608408735963519)
    ·
      refine ⟨4249622393412613103945279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2833081595608408735963519 4249622393412613103945279)
      ·
        refine ⟨6374433590118919655917919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4249622393412613103945279 6374433590118919655917919)
        ·
          refine ⟨9561650385178379483876879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6374433590118919655917919 9561650385178379483876879)
          ·
            refine ⟨14342475577767569225815319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9561650385178379483876879 14342475577767569225815319)
            ·
              refine ⟨21513713366651353838722979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14342475577767569225815319 21513713366651353838722979)
              ·
                refine ⟨32270570049977030758084469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21513713366651353838722979 32270570049977030758084469)
                ·
                  refine ⟨3025365942185346633570419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32270570049977030758084469 3025365942185346633570419)
                  ·
                    refine ⟨4538048913278019950355629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3025365942185346633570419 4538048913278019950355629)
                    ·
                      refine ⟨1701768342479257481383361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4538048913278019950355629 1701768342479257481383361)
                      ·
                        rfl

theorem cell23_3314182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3314182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314182 prefixEnd_3314182 := by exact prefixLift 3314182
  have htrace : WordTrace (prefixWord ++ tailWord_3314182) baseStart_3314182 baseEnd_3314182 := by
    simpa [prefixWord, tailWord_3314182, baseEnd_3314182] using wordTrace_append hprefix tailTrace_3314182
  have hstable : (prefixWord ++ tailWord_3314182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314182).length < 2 ^ (prefixWord ++ tailWord_3314182).sum := by decide
  have hdescent : baseEnd_3314182 < baseStart_3314182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314188 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 5, 2, 2]
def baseStart_3314188 : Nat := 118140960795 + 3314188 * 2 ^ 59
def prefixEnd_3314188 : Nat := 4983230072969 + 3 ^ 40 * 3314188 * 2
def baseEnd_3314188 : Nat := 1701771423363184457908333

theorem tailTrace_3314188 : CollatzResearch.WordTrace tailWord_3314188 prefixEnd_3314188 1701771423363184457908333 := by
  unfold tailWord_3314188
  simp only [CollatzResearch.WordTrace]
  refine ⟨60439183458635184546247609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80585577944846912728330145 60439183458635184546247609)
  ·
    refine ⟨45329387593976388409685707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60439183458635184546247609 45329387593976388409685707)
    ·
      refine ⟨67994081390964582614528561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45329387593976388409685707 67994081390964582614528561)
      ·
        refine ⟨50995561043223436960896421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67994081390964582614528561 50995561043223436960896421)
        ·
          refine ⟨9561667695604394430168079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50995561043223436960896421 9561667695604394430168079)
          ·
            refine ⟨14342501543406591645252119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9561667695604394430168079 14342501543406591645252119)
            ·
              refine ⟨21513752315109887467878179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14342501543406591645252119 21513752315109887467878179)
              ·
                refine ⟨32270628472664831201817269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21513752315109887467878179 32270628472664831201817269)
                ·
                  refine ⟨3025371419312327925170369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32270628472664831201817269 3025371419312327925170369)
                  ·
                    refine ⟨2269028564484245943877777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3025371419312327925170369 2269028564484245943877777)
                    ·
                      refine ⟨1701771423363184457908333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269028564484245943877777 1701771423363184457908333)
                      ·
                        rfl

theorem cell23_3314188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_3314188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314188 prefixEnd_3314188 := by exact prefixLift 3314188
  have htrace : WordTrace (prefixWord ++ tailWord_3314188) baseStart_3314188 baseEnd_3314188 := by
    simpa [prefixWord, tailWord_3314188, baseEnd_3314188] using wordTrace_append hprefix tailTrace_3314188
  have hstable : (prefixWord ++ tailWord_3314188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314188).length < 2 ^ (prefixWord ++ tailWord_3314188).sum := by decide
  have hdescent : baseEnd_3314188 < baseStart_3314188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314205 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_3314205 : Nat := 118140960795 + 3314205 * 2 ^ 59
def prefixEnd_3314205 : Nat := 4983230072969 + 3 ^ 40 * 3314205 * 2
def baseEnd_3314205 : Nat := 1701780152534310891395755

theorem tailTrace_3314205 : CollatzResearch.WordTrace tailWord_3314205 prefixEnd_3314205 1701780152534310891395755 := by
  unfold tailWord_3314205
  simp only [CollatzResearch.WordTrace]
  refine ⟨120878986958208780995864069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80585991305472520663909379 120878986958208780995864069)
  ·
    refine ⟨22664810054664146436724513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120878986958208780995864069 22664810054664146436724513)
    ·
      refine ⟨16998607540998109827543385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22664810054664146436724513 16998607540998109827543385)
      ·
        refine ⟨12748955655748582370657539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16998607540998109827543385 12748955655748582370657539)
        ·
          refine ⟨19123433483622873555986309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12748955655748582370657539 19123433483622873555986309)
          ·
            refine ⟨3585643778179288791747433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19123433483622873555986309 3585643778179288791747433)
            ·
              refine ⟨2689232833634466593810575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3585643778179288791747433 2689232833634466593810575)
              ·
                refine ⟨4033849250451699890715863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689232833634466593810575 4033849250451699890715863)
                ·
                  refine ⟨6050773875677549836073795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033849250451699890715863 6050773875677549836073795)
                  ·
                    refine ⟨9076160813516324754110693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6050773875677549836073795 9076160813516324754110693)
                    ·
                      refine ⟨1701780152534310891395755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9076160813516324754110693 1701780152534310891395755)
                      ·
                        rfl

theorem cell23_3314205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_3314205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314205 prefixEnd_3314205 := by exact prefixLift 3314205
  have htrace : WordTrace (prefixWord ++ tailWord_3314205) baseStart_3314205 baseEnd_3314205 := by
    simpa [prefixWord, tailWord_3314205, baseEnd_3314205] using wordTrace_append hprefix tailTrace_3314205
  have hstable : (prefixWord ++ tailWord_3314205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314205).length < 2 ^ (prefixWord ++ tailWord_3314205).sum := by decide
  have hdescent : baseEnd_3314205 < baseStart_3314205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314215 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3314215 : Nat := 118140960795 + 3314215 * 2 ^ 59
def prefixEnd_3314215 : Nat := 4983230072969 + 3 ^ 40 * 3314215 * 2
def baseEnd_3314215 : Nat := 567261762446951950756903

theorem tailTrace_3314215 : CollatzResearch.WordTrace tailWord_3314215 prefixEnd_3314215 567261762446951950756903 := by
  unfold tailWord_3314215
  simp only [CollatzResearch.WordTrace]
  refine ⟨120879351688172552703728099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80586234458781701802485399 120879351688172552703728099)
  ·
    refine ⟨181319027532258829055592149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120879351688172552703728099 181319027532258829055592149)
    ·
      refine ⟨4249664707787316305990441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 181319027532258829055592149 4249664707787316305990441)
      ·
        refine ⟨3187248530840487229492831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4249664707787316305990441 3187248530840487229492831)
        ·
          refine ⟨4780872796260730844239247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187248530840487229492831 4780872796260730844239247)
          ·
            refine ⟨7171309194391096266358871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4780872796260730844239247 7171309194391096266358871)
            ·
              refine ⟨10756963791586644399538307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7171309194391096266358871 10756963791586644399538307)
              ·
                refine ⟨16135445687379966599307461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10756963791586644399538307 16135445687379966599307461)
                ·
                  refine ⟨3025396066383743737370149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16135445687379966599307461 3025396066383743737370149)
                  ·
                    refine ⟨567261762446951950756903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3025396066383743737370149 567261762446951950756903)
                    ·
                      rfl

theorem cell23_3314215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3314215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314215 prefixEnd_3314215 := by exact prefixLift 3314215
  have htrace : WordTrace (prefixWord ++ tailWord_3314215) baseStart_3314215 baseEnd_3314215 := by
    simpa [prefixWord, tailWord_3314215, baseEnd_3314215] using wordTrace_append hprefix tailTrace_3314215
  have hstable : (prefixWord ++ tailWord_3314215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314215).length < 2 ^ (prefixWord ++ tailWord_3314215).sum := by decide
  have hdescent : baseEnd_3314215 < baseStart_3314215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314222 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_3314222 : Nat := 118140960795 + 3314222 * 2 ^ 59
def prefixEnd_3314222 : Nat := 4983230072969 + 3 ^ 40 * 3314222 * 2
def baseEnd_3314222 : Nat := 1701788881705437324883177

theorem tailTrace_3314222 : CollatzResearch.WordTrace tailWord_3314222 prefixEnd_3314222 1701788881705437324883177 := by
  unfold tailWord_3314222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109950874893399112404115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80586404666098128599488613 15109950874893399112404115)
  ·
    refine ⟨22664926312340098668606173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15109950874893399112404115 22664926312340098668606173)
    ·
      refine ⟨8499347367127537000727315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22664926312340098668606173 8499347367127537000727315)
      ·
        refine ⟨12749021050691305501090973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8499347367127537000727315 12749021050691305501090973)
        ·
          refine ⟨4780882894009239562909115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12749021050691305501090973 4780882894009239562909115)
          ·
            refine ⟨7171324341013859344363673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4780882894009239562909115 7171324341013859344363673)
            ·
              refine ⟨5378493255760394508272755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7171324341013859344363673 5378493255760394508272755)
              ·
                refine ⟨8067739883640591762409133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5378493255760394508272755 8067739883640591762409133)
                ·
                  refine ⟨3025402456365221910903425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8067739883640591762409133 3025402456365221910903425)
                  ·
                    refine ⟨2269051842273916433177569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3025402456365221910903425 2269051842273916433177569)
                    ·
                      refine ⟨1701788881705437324883177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269051842273916433177569 1701788881705437324883177)
                      ·
                        rfl

theorem cell23_3314222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_3314222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314222 prefixEnd_3314222 := by exact prefixLift 3314222
  have htrace : WordTrace (prefixWord ++ tailWord_3314222) baseStart_3314222 baseEnd_3314222 := by
    simpa [prefixWord, tailWord_3314222, baseEnd_3314222] using wordTrace_append hprefix tailTrace_3314222
  have hstable : (prefixWord ++ tailWord_3314222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314222).length < 2 ^ (prefixWord ++ tailWord_3314222).sum := by decide
  have hdescent : baseEnd_3314222 < baseStart_3314222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314254 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_3314254 : Nat := 118140960795 + 3314254 * 2 ^ 59
def prefixEnd_3314254 : Nat := 4983230072969 + 3 ^ 40 * 3314254 * 2
def baseEnd_3314254 : Nat := 567268437695460399894343

theorem tailTrace_3314254 : CollatzResearch.WordTrace tailWord_3314254 prefixEnd_3314254 567268437695460399894343 := by
  unfold tailWord_3314254
  simp only [CollatzResearch.WordTrace]
  refine ⟨15110096766878907795549727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80587182756687508242931877 15110096766878907795549727)
  ·
    refine ⟨22665145150318361693324591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15110096766878907795549727 22665145150318361693324591)
    ·
      refine ⟨33997717725477542539986887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22665145150318361693324591 33997717725477542539986887)
      ·
        refine ⟨50996576588216313809980331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33997717725477542539986887 50996576588216313809980331)
        ·
          refine ⟨76494864882324470714970497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50996576588216313809980331 76494864882324470714970497)
          ·
            refine ⟨57371148661743353036227873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76494864882324470714970497 57371148661743353036227873)
            ·
              refine ⟨43028361496307514777170905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57371148661743353036227873 43028361496307514777170905)
              ·
                refine ⟨32271271122230636082878179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43028361496307514777170905 32271271122230636082878179)
                ·
                  refine ⟨48406906683345954124317269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32271271122230636082878179 48406906683345954124317269)
                  ·
                    refine ⟨567268437695460399894343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48406906683345954124317269 567268437695460399894343)
                    ·
                      rfl

theorem cell23_3314254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_3314254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314254 prefixEnd_3314254 := by exact prefixLift 3314254
  have htrace : WordTrace (prefixWord ++ tailWord_3314254) baseStart_3314254 baseEnd_3314254 := by
    simpa [prefixWord, tailWord_3314254, baseEnd_3314254] using wordTrace_append hprefix tailTrace_3314254
  have hstable : (prefixWord ++ tailWord_3314254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314254).length < 2 ^ (prefixWord ++ tailWord_3314254).sum := by decide
  have hdescent : baseEnd_3314254 < baseStart_3314254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314264 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_3314264 : Nat := 118140960795 + 3314264 * 2 ^ 59
def prefixEnd_3314264 : Nat := 4983230072969 + 3 ^ 40 * 3314264 * 2
def baseEnd_3314264 : Nat := 1701810447892926160557983

theorem tailTrace_3314264 : CollatzResearch.WordTrace tailWord_3314264 prefixEnd_3314264 1701810447892926160557983 := by
  unfold tailWord_3314264
  simp only [CollatzResearch.WordTrace]
  refine ⟨60440569432497517036130923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80587425909996689381507897 60440569432497517036130923)
  ·
    refine ⟨90660854148746275554196385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60440569432497517036130923 90660854148746275554196385)
    ·
      refine ⟨67995640611559706665647289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90660854148746275554196385 67995640611559706665647289)
      ·
        refine ⟨50996730458669779999235467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67995640611559706665647289 50996730458669779999235467)
        ·
          refine ⟨76495095688004669998853201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50996730458669779999235467 76495095688004669998853201)
          ·
            refine ⟨57371321766003502499139901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76495095688004669998853201 57371321766003502499139901)
            ·
              refine ⟨21514245662251313437177463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57371321766003502499139901 21514245662251313437177463)
              ·
                refine ⟨32271368493376970155766195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21514245662251313437177463 32271368493376970155766195)
                ·
                  refine ⟨48407052740065455233649293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32271368493376970155766195 48407052740065455233649293)
                  ·
                    refine ⟨18152644777524545712618485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48407052740065455233649293 18152644777524545712618485)
                    ·
                      refine ⟨1701810447892926160557983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18152644777524545712618485 1701810447892926160557983)
                      ·
                        rfl

theorem cell23_3314264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_3314264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314264 prefixEnd_3314264 := by exact prefixLift 3314264
  have htrace : WordTrace (prefixWord ++ tailWord_3314264) baseStart_3314264 baseEnd_3314264 := by
    simpa [prefixWord, tailWord_3314264, baseEnd_3314264] using wordTrace_append hprefix tailTrace_3314264
  have hstable : (prefixWord ++ tailWord_3314264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314264).length < 2 ^ (prefixWord ++ tailWord_3314264).sum := by decide
  have hdescent : baseEnd_3314264 < baseStart_3314264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314318 : List Nat := [4, 1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_3314318 : Nat := 118140960795 + 3314318 * 2 ^ 59
def prefixEnd_3314318 : Nat := 4983230072969 + 3 ^ 40 * 3314318 * 2
def baseEnd_3314318 : Nat := 189093130649807661031415

theorem tailTrace_3314318 : CollatzResearch.WordTrace tailWord_3314318 prefixEnd_3314318 189093130649807661031415 := by
  unfold tailWord_3314318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15110388550849925161840951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80588738937866267529818405 15110388550849925161840951)
  ·
    refine ⟨22665582826274887742761427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15110388550849925161840951 22665582826274887742761427)
    ·
      refine ⟨33998374239412331614142141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22665582826274887742761427 33998374239412331614142141)
      ·
        refine ⟨12749390339779624355303303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33998374239412331614142141 12749390339779624355303303)
        ·
          refine ⟨19124085509669436532954955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12749390339779624355303303 19124085509669436532954955)
          ·
            refine ⟨28686128264504154799432433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19124085509669436532954955 28686128264504154799432433)
            ·
              refine ⟨21514596198378116099574325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28686128264504154799432433 21514596198378116099574325)
              ·
                refine ⟨2016993393597948384335093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21514596198378116099574325 2016993393597948384335093)
                ·
                  refine ⟨189093130649807661031415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2016993393597948384335093 189093130649807661031415)
                  ·
                    rfl

theorem cell23_3314318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_3314318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314318 prefixEnd_3314318 := by exact prefixLift 3314318
  have htrace : WordTrace (prefixWord ++ tailWord_3314318) baseStart_3314318 baseEnd_3314318 := by
    simpa [prefixWord, tailWord_3314318, baseEnd_3314318] using wordTrace_append hprefix tailTrace_3314318
  have hstable : (prefixWord ++ tailWord_3314318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314318).length < 2 ^ (prefixWord ++ tailWord_3314318).sum := by decide
  have hdescent : baseEnd_3314318 < baseStart_3314318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314368 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 4]
def baseStart_3314368 : Nat := 118140960795 + 3314368 * 2 ^ 59
def prefixEnd_3314368 : Nat := 4983230072969 + 3 ^ 40 * 3314368 * 2
def baseEnd_3314368 : Nat := 1701863849880993753657505

theorem tailTrace_3314368 : CollatzResearch.WordTrace tailWord_3314368 prefixEnd_3314368 1701863849880993753657505 := by
  unfold tailWord_3314368
  simp only [CollatzResearch.WordTrace]
  refine ⟨60442466028309129917023879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80589954704412173222698505 60442466028309129917023879)
  ·
    refine ⟨90663699042463694875535819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60442466028309129917023879 90663699042463694875535819)
    ·
      refine ⟨135995548563695542313303729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90663699042463694875535819 135995548563695542313303729)
      ·
        refine ⟨101996661422771656734977797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135995548563695542313303729 101996661422771656734977797)
        ·
          refine ⟨19124374016769685637808337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101996661422771656734977797 19124374016769685637808337)
          ·
            refine ⟨14343280512577264228356253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19124374016769685637808337 14343280512577264228356253)
            ·
              refine ⟨5378730192216474085633595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14343280512577264228356253 5378730192216474085633595)
              ·
                refine ⟨8068095288324711128450393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5378730192216474085633595 8068095288324711128450393)
                ·
                  refine ⟨6051071466243533346337795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8068095288324711128450393 6051071466243533346337795)
                  ·
                    refine ⟨9076607199365300019506693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6051071466243533346337795 9076607199365300019506693)
                    ·
                      refine ⟨1701863849880993753657505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9076607199365300019506693 1701863849880993753657505)
                      ·
                        rfl

theorem cell23_3314368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_3314368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314368 prefixEnd_3314368 := by exact prefixLift 3314368
  have htrace : WordTrace (prefixWord ++ tailWord_3314368) baseStart_3314368 baseEnd_3314368 := by
    simpa [prefixWord, tailWord_3314368, baseEnd_3314368] using wordTrace_append hprefix tailTrace_3314368
  have hstable : (prefixWord ++ tailWord_3314368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314368).length < 2 ^ (prefixWord ++ tailWord_3314368).sum := by decide
  have hdescent : baseEnd_3314368 < baseStart_3314368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314391 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 8]
def baseStart_3314391 : Nat := 118140960795 + 3314391 * 2 ^ 59
def prefixEnd_3314391 : Nat := 4983230072969 + 3 ^ 40 * 3314391 * 2
def baseEnd_3314391 : Nat := 189097295548449684852211

theorem tailTrace_3314391 : CollatzResearch.WordTrace tailWord_3314391 prefixEnd_3314391 189097295548449684852211 := by
  unfold tailWord_3314391
  simp only [CollatzResearch.WordTrace]
  refine ⟨120885770935534934762135027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80590513957023289841423351 120885770935534934762135027)
  ·
    refine ⟨181328656403302402143202541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120885770935534934762135027 181328656403302402143202541)
    ·
      refine ⟨67998246151238400803700953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181328656403302402143202541 67998246151238400803700953)
      ·
        refine ⟨50998684613428800602775715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67998246151238400803700953 50998684613428800602775715)
        ·
          refine ⟨76498026920143200904163573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50998684613428800602775715 76498026920143200904163573)
          ·
            refine ⟨7171690023763425084765335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76498026920143200904163573 7171690023763425084765335)
            ·
              refine ⟨10757535035645137627148003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7171690023763425084765335 10757535035645137627148003)
              ·
                refine ⟨16136302553467706440722005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10757535035645137627148003 16136302553467706440722005)
                ·
                  refine ⟨189097295548449684852211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16136302553467706440722005 189097295548449684852211)
                  ·
                    rfl

theorem cell23_3314391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 8].length) (baseStart_3314391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314391 prefixEnd_3314391 := by exact prefixLift 3314391
  have htrace : WordTrace (prefixWord ++ tailWord_3314391) baseStart_3314391 baseEnd_3314391 := by
    simpa [prefixWord, tailWord_3314391, baseEnd_3314391] using wordTrace_append hprefix tailTrace_3314391
  have hstable : (prefixWord ++ tailWord_3314391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314391).length < 2 ^ (prefixWord ++ tailWord_3314391).sum := by decide
  have hdescent : baseEnd_3314391 < baseStart_3314391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314458 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_3314458 : Nat := 118140960795 + 3314458 * 2 ^ 59
def prefixEnd_3314458 : Nat := 4983230072969 + 3 ^ 40 * 3314458 * 2
def baseEnd_3314458 : Nat := 1701910063139898401532091

theorem tailTrace_3314458 : CollatzResearch.WordTrace tailWord_3314458 prefixEnd_3314458 1701910063139898401532091 := by
  unfold tailWord_3314458
  simp only [CollatzResearch.WordTrace]
  refine ⟨30222053656573051301206007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80592143084194803469882685 30222053656573051301206007)
  ·
    refine ⟨45333080484859576951809011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30222053656573051301206007 45333080484859576951809011)
    ·
      refine ⟨67999620727289365427713517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45333080484859576951809011 67999620727289365427713517)
      ·
        refine ⟨25499857772733512035392569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67999620727289365427713517 25499857772733512035392569)
        ·
          refine ⟨19124893329550134026544427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25499857772733512035392569 19124893329550134026544427)
          ·
            refine ⟨28687339994325201039816641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19124893329550134026544427 28687339994325201039816641)
            ·
              refine ⟨21515504995743900779862481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28687339994325201039816641 21515504995743900779862481)
              ·
                refine ⟨16136628746807925584896861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21515504995743900779862481 16136628746807925584896861)
                ·
                  refine ⟨6051235780052972094336323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16136628746807925584896861 6051235780052972094336323)
                  ·
                    refine ⟨9076853670079458141504485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6051235780052972094336323 9076853670079458141504485)
                    ·
                      refine ⟨1701910063139898401532091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9076853670079458141504485 1701910063139898401532091)
                      ·
                        rfl

theorem cell23_3314458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_3314458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314458 prefixEnd_3314458 := by exact prefixLift 3314458
  have htrace : WordTrace (prefixWord ++ tailWord_3314458) baseStart_3314458 baseEnd_3314458 := by
    simpa [prefixWord, tailWord_3314458, baseEnd_3314458] using wordTrace_append hprefix tailTrace_3314458
  have hstable : (prefixWord ++ tailWord_3314458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314458).length < 2 ^ (prefixWord ++ tailWord_3314458).sum := by decide
  have hdescent : baseEnd_3314458 < baseStart_3314458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314481 : List Nat := [1, 2, 2, 3, 2, 1, 1, 11]
def baseStart_3314481 : Nat := 118140960795 + 3314481 * 2 ^ 59
def prefixEnd_3314481 : Nat := 4983230072969 + 3 ^ 40 * 3314481 * 2
def baseEnd_3314481 : Nat := 63034143451664881909055

theorem tailTrace_3314481 : CollatzResearch.WordTrace tailWord_3314481 prefixEnd_3314481 63034143451664881909055 := by
  unfold tailWord_3314481
  simp only [CollatzResearch.WordTrace]
  refine ⟨120889053505208880132911297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80592702336805920088607531 120889053505208880132911297)
  ·
    refine ⟨90666790128906660099683473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120889053505208880132911297 90666790128906660099683473)
    ·
      refine ⟨68000092596679995074762605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90666790128906660099683473 68000092596679995074762605)
      ·
        refine ⟨25500034723754998153035977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68000092596679995074762605 25500034723754998153035977)
        ·
          refine ⟨19125026042816248614776983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25500034723754998153035977 19125026042816248614776983)
          ·
            refine ⟨28687539064224372922165475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19125026042816248614776983 28687539064224372922165475)
            ·
              refine ⟨43031308596336559383248213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28687539064224372922165475 43031308596336559383248213)
              ·
                refine ⟨63034143451664881909055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 43031308596336559383248213 63034143451664881909055)
                ·
                  rfl

theorem cell23_3314481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 11].length) (baseStart_3314481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314481 prefixEnd_3314481 := by exact prefixLift 3314481
  have htrace : WordTrace (prefixWord ++ tailWord_3314481) baseStart_3314481 baseEnd_3314481 := by
    simpa [prefixWord, tailWord_3314481, baseEnd_3314481] using wordTrace_append hprefix tailTrace_3314481
  have hstable : (prefixWord ++ tailWord_3314481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314481).length < 2 ^ (prefixWord ++ tailWord_3314481).sum := by decide
  have hdescent : baseEnd_3314481 < baseStart_3314481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314488 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_3314488 : Nat := 118140960795 + 3314488 * 2 ^ 59
def prefixEnd_3314488 : Nat := 4983230072969 + 3 ^ 40 * 3314488 * 2
def baseEnd_3314488 : Nat := 1701925467559533284156953

theorem tailTrace_3314488 : CollatzResearch.WordTrace tailWord_3314488 prefixEnd_3314488 1701925467559533284156953 := by
  unfold tailWord_3314488
  simp only [CollatzResearch.WordTrace]
  refine ⟨60444654408091760164208059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80592872544122346885610745 60444654408091760164208059)
  ·
    refine ⟨90666981612137640246312089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60444654408091760164208059 90666981612137640246312089)
    ·
      refine ⟨68000236209103230184734067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90666981612137640246312089 68000236209103230184734067)
      ·
        refine ⟨102000354313654845277101101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68000236209103230184734067 102000354313654845277101101)
        ·
          refine ⟨38250132867620566978912913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102000354313654845277101101 38250132867620566978912913)
          ·
            refine ⟨28687599650715425234184685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38250132867620566978912913 28687599650715425234184685)
            ·
              refine ⟨10757849869018284462819257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28687599650715425234184685 10757849869018284462819257)
              ·
                refine ⟨8068387401763713347114443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10757849869018284462819257 8068387401763713347114443)
                ·
                  refine ⟨12102581102645570020671665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8068387401763713347114443 12102581102645570020671665)
                  ·
                    refine ⟨9076935826984177515503749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12102581102645570020671665 9076935826984177515503749)
                    ·
                      refine ⟨1701925467559533284156953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9076935826984177515503749 1701925467559533284156953)
                      ·
                        rfl

theorem cell23_3314488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_3314488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314488 prefixEnd_3314488 := by exact prefixLift 3314488
  have htrace : WordTrace (prefixWord ++ tailWord_3314488) baseStart_3314488 baseEnd_3314488 := by
    simpa [prefixWord, tailWord_3314488, baseEnd_3314488] using wordTrace_append hprefix tailTrace_3314488
  have hstable : (prefixWord ++ tailWord_3314488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314488).length < 2 ^ (prefixWord ++ tailWord_3314488).sum := by decide
  have hdescent : baseEnd_3314488 < baseStart_3314488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314495 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 5]
def baseStart_3314495 : Nat := 118140960795 + 3314495 * 2 ^ 59
def prefixEnd_3314495 : Nat := 4983230072969 + 3 ^ 40 * 3314495 * 2
def baseEnd_3314495 : Nat := 1701929061924114756769421

theorem tailTrace_3314495 : CollatzResearch.WordTrace tailWord_3314495 prefixEnd_3314495 1701929061924114756769421 := by
  unfold tailWord_3314495
  simp only [CollatzResearch.WordTrace]
  refine ⟨120889564127158160523920939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80593042751438773682613959 120889564127158160523920939)
  ·
    refine ⟨181334346190737240785881409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120889564127158160523920939 181334346190737240785881409)
    ·
      refine ⟨136000759643052930589411057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181334346190737240785881409 136000759643052930589411057)
      ·
        refine ⟨102000569732289697942058293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136000759643052930589411057 102000569732289697942058293)
        ·
          refine ⟨9562553412402159182067965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102000569732289697942058293 9562553412402159182067965)
          ·
            refine ⟨3585957529650809693275487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9562553412402159182067965 3585957529650809693275487)
            ·
              refine ⟨5378936294476214539913231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585957529650809693275487 5378936294476214539913231)
              ·
                refine ⟨8068404441714321809869847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5378936294476214539913231 8068404441714321809869847)
                ·
                  refine ⟨12102606662571482714804771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8068404441714321809869847 12102606662571482714804771)
                  ·
                    refine ⟨18153909993857224072207157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12102606662571482714804771 18153909993857224072207157)
                    ·
                      refine ⟨1701929061924114756769421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18153909993857224072207157 1701929061924114756769421)
                      ·
                        rfl

theorem cell23_3314495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_3314495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314495 prefixEnd_3314495 := by exact prefixLift 3314495
  have htrace : WordTrace (prefixWord ++ tailWord_3314495) baseStart_3314495 baseEnd_3314495 := by
    simpa [prefixWord, tailWord_3314495, baseEnd_3314495] using wordTrace_append hprefix tailTrace_3314495
  have hstable : (prefixWord ++ tailWord_3314495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314495).length < 2 ^ (prefixWord ++ tailWord_3314495).sum := by decide
  have hdescent : baseEnd_3314495 < baseStart_3314495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314501 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_3314501 : Nat := 118140960795 + 3314501 * 2 ^ 59
def prefixEnd_3314501 : Nat := 4983230072969 + 3 ^ 40 * 3314501 * 2
def baseEnd_3314501 : Nat := 1701932142808041733294393

theorem tailTrace_3314501 : CollatzResearch.WordTrace tailWord_3314501 prefixEnd_3314501 1701932142808041733294393 := by
  unfold tailWord_3314501
  simp only [CollatzResearch.WordTrace]
  refine ⟨120889782965136423548639357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80593188643424282365759571 120889782965136423548639357)
  ·
    refine ⟨45333668611926158830739759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120889782965136423548639357 45333668611926158830739759)
    ·
      refine ⟨68000502917889238246109639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45333668611926158830739759 68000502917889238246109639)
      ·
        refine ⟨102000754376833857369164459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68000502917889238246109639 102000754376833857369164459)
        ·
          refine ⟨153001131565250786053746689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102000754376833857369164459 153001131565250786053746689)
          ·
            refine ⟨114750848673938089540310017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153001131565250786053746689 114750848673938089540310017)
            ·
              refine ⟨86063136505453567155232513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114750848673938089540310017 86063136505453567155232513)
              ·
                refine ⟨64547352379090175366424385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86063136505453567155232513 64547352379090175366424385)
                ·
                  refine ⟨48410514284317631524818289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64547352379090175366424385 48410514284317631524818289)
                  ·
                    refine ⟨36307885713238223643613717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48410514284317631524818289 36307885713238223643613717)
                    ·
                      refine ⟨1701932142808041733294393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36307885713238223643613717 1701932142808041733294393)
                      ·
                        rfl

theorem cell23_3314501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_3314501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314501 prefixEnd_3314501 := by exact prefixLift 3314501
  have htrace : WordTrace (prefixWord ++ tailWord_3314501) baseStart_3314501 baseEnd_3314501 := by
    simpa [prefixWord, tailWord_3314501, baseEnd_3314501] using wordTrace_append hprefix tailTrace_3314501
  have hstable : (prefixWord ++ tailWord_3314501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314501).length < 2 ^ (prefixWord ++ tailWord_3314501).sum := by decide
  have hdescent : baseEnd_3314501 < baseStart_3314501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314637 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3314637 : Nat := 118140960795 + 3314637 * 2 ^ 59
def prefixEnd_3314637 : Nat := 4983230072969 + 3 ^ 40 * 3314637 * 2
def baseEnd_3314637 : Nat := 1702001976177053201193769

theorem tailTrace_3314637 : CollatzResearch.WordTrace tailWord_3314637 prefixEnd_3314637 1702001976177053201193769 := by
  unfold tailWord_3314637
  simp only [CollatzResearch.WordTrace]
  refine ⟨120894743292643718775590165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80596495528429145850393443 120894743292643718775590165)
  ·
    refine ⟨5666941091842674317605789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120894743292643718775590165 5666941091842674317605789)
    ·
      refine ⟨2125102909441002869102171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5666941091842674317605789 2125102909441002869102171)
      ·
        refine ⟨3187654364161504303653257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2125102909441002869102171 3187654364161504303653257)
        ·
          refine ⟨2390740773121128227739943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3187654364161504303653257 2390740773121128227739943)
          ·
            refine ⟨3586111159681692341609915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390740773121128227739943 3586111159681692341609915)
            ·
              refine ⟨5379166739522538512414873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586111159681692341609915 5379166739522538512414873)
              ·
                refine ⟨4034375054641903884311155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5379166739522538512414873 4034375054641903884311155)
                ·
                  refine ⟨6051562581962855826466733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4034375054641903884311155 6051562581962855826466733)
                  ·
                    refine ⟨2269335968236070934925025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6051562581962855826466733 2269335968236070934925025)
                    ·
                      refine ⟨1702001976177053201193769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269335968236070934925025 1702001976177053201193769)
                      ·
                        rfl

theorem cell23_3314637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3314637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314637 prefixEnd_3314637 := by exact prefixLift 3314637
  have htrace : WordTrace (prefixWord ++ tailWord_3314637) baseStart_3314637 baseEnd_3314637 := by
    simpa [prefixWord, tailWord_3314637, baseEnd_3314637] using wordTrace_append hprefix tailTrace_3314637
  have hstable : (prefixWord ++ tailWord_3314637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314637).length < 2 ^ (prefixWord ++ tailWord_3314637).sum := by decide
  have hdescent : baseEnd_3314637 < baseStart_3314637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314695 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 6]
def baseStart_3314695 : Nat := 118140960795 + 3314695 * 2 ^ 59
def prefixEnd_3314695 : Nat := 4983230072969 + 3 ^ 40 * 3314695 * 2
def baseEnd_3314695 : Nat := 189114639783890441585389

theorem tailTrace_3314695 : CollatzResearch.WordTrace tailWord_3314695 prefixEnd_3314695 189114639783890441585389 := by
  unfold tailWord_3314695
  simp only [CollatzResearch.WordTrace]
  refine ⟨120896858726433594681201539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80597905817622396454134359 120896858726433594681201539)
  ·
    refine ⟨181345288089650392021802309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120896858726433594681201539 181345288089650392021802309)
    ·
      refine ⟨34002241516809448504087933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181345288089650392021802309 34002241516809448504087933)
      ·
        refine ⟨12750840568803543189032975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34002241516809448504087933 12750840568803543189032975)
        ·
          refine ⟨19126260853205314783549463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12750840568803543189032975 19126260853205314783549463)
          ·
            refine ⟨28689391279807972175324195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19126260853205314783549463 28689391279807972175324195)
            ·
              refine ⟨43034086919711958262986293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28689391279807972175324195 43034086919711958262986293)
              ·
                refine ⟨4034445648722996087154965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43034086919711958262986293 4034445648722996087154965)
                ·
                  refine ⟨189114639783890441585389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4034445648722996087154965 189114639783890441585389)
                  ·
                    rfl

theorem cell23_3314695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 6].length) (baseStart_3314695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314695 prefixEnd_3314695 := by exact prefixLift 3314695
  have htrace : WordTrace (prefixWord ++ tailWord_3314695) baseStart_3314695 baseEnd_3314695 := by
    simpa [prefixWord, tailWord_3314695, baseEnd_3314695] using wordTrace_append hprefix tailTrace_3314695
  have hstable : (prefixWord ++ tailWord_3314695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314695).length < 2 ^ (prefixWord ++ tailWord_3314695).sum := by decide
  have hdescent : baseEnd_3314695 < baseStart_3314695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314706 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3314706 : Nat := 118140960795 + 3314706 * 2 ^ 59
def prefixEnd_3314706 : Nat := 4983230072969 + 3 ^ 40 * 3314706 * 2
def baseEnd_3314706 : Nat := 1702037406342213431230951

theorem tailTrace_3314706 : CollatzResearch.WordTrace tailWord_3314706 prefixEnd_3314706 1702037406342213431230951 := by
  unfold tailWord_3314706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30224314982348435889962993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80598173286262495706567981 30224314982348435889962993)
  ·
    refine ⟨22668236236761326917472245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30224314982348435889962993 22668236236761326917472245)
    ·
      refine ⟨2125147147196374398513023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22668236236761326917472245 2125147147196374398513023)
      ·
        refine ⟨3187720720794561597769535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2125147147196374398513023 3187720720794561597769535)
        ·
          refine ⟨4781581081191842396654303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187720720794561597769535 4781581081191842396654303)
          ·
            refine ⟨7172371621787763594981455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781581081191842396654303 7172371621787763594981455)
            ·
              refine ⟨10758557432681645392472183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7172371621787763594981455 10758557432681645392472183)
              ·
                refine ⟨16137836149022468088708275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10758557432681645392472183 16137836149022468088708275)
                ·
                  refine ⟨24206754223533702133062413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16137836149022468088708275 24206754223533702133062413)
                  ·
                    refine ⟨9077532833825138299898405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24206754223533702133062413 9077532833825138299898405)
                    ·
                      refine ⟨1702037406342213431230951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9077532833825138299898405 1702037406342213431230951)
                      ·
                        rfl

theorem cell23_3314706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3314706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314706 prefixEnd_3314706 := by exact prefixLift 3314706
  have htrace : WordTrace (prefixWord ++ tailWord_3314706) baseStart_3314706 baseEnd_3314706 := by
    simpa [prefixWord, tailWord_3314706, baseEnd_3314706] using wordTrace_append hprefix tailTrace_3314706
  have hstable : (prefixWord ++ tailWord_3314706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314706).length < 2 ^ (prefixWord ++ tailWord_3314706).sum := by decide
  have hdescent : baseEnd_3314706 < baseStart_3314706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314709 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_3314709 : Nat := 118140960795 + 3314709 * 2 ^ 59
def prefixEnd_3314709 : Nat := 4983230072969 + 3 ^ 40 * 3314709 * 2
def baseEnd_3314709 : Nat := 1702038946784176919493437

theorem tailTrace_3314709 : CollatzResearch.WordTrace tailWord_3314709 prefixEnd_3314709 1702038946784176919493437 := by
  unfold tailWord_3314709
  simp only [CollatzResearch.WordTrace]
  refine ⟨120897369348382875072211181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80598246232255250048140787 120897369348382875072211181)
  ·
    refine ⟨45336513505643578152079193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120897369348382875072211181 45336513505643578152079193)
    ·
      refine ⟨34002385129232683614059395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45336513505643578152079193 34002385129232683614059395)
      ·
        refine ⟨51003577693849025421089093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34002385129232683614059395 51003577693849025421089093)
        ·
          refine ⟨9563170817596692266454205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51003577693849025421089093 9563170817596692266454205)
          ·
            refine ⟨3586189056598759599920327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9563170817596692266454205 3586189056598759599920327)
            ·
              refine ⟨5379283584898139399880491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586189056598759599920327 5379283584898139399880491)
              ·
                refine ⟨8068925377347209099820737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5379283584898139399880491 8068925377347209099820737)
                ·
                  refine ⟨6051694033010406824865553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8068925377347209099820737 6051694033010406824865553)
                  ·
                    refine ⟨4538770524757805118649165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6051694033010406824865553 4538770524757805118649165)
                    ·
                      refine ⟨1702038946784176919493437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4538770524757805118649165 1702038946784176919493437)
                      ·
                        rfl

theorem cell23_3314709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_3314709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314709 prefixEnd_3314709 := by exact prefixLift 3314709
  have htrace : WordTrace (prefixWord ++ tailWord_3314709) baseStart_3314709 baseEnd_3314709 := by
    simpa [prefixWord, tailWord_3314709, baseEnd_3314709] using wordTrace_append hprefix tailTrace_3314709
  have hstable : (prefixWord ++ tailWord_3314709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314709).length < 2 ^ (prefixWord ++ tailWord_3314709).sum := by decide
  have hdescent : baseEnd_3314709 < baseStart_3314709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314716 : List Nat := [2, 2, 3, 1, 4, 1, 2, 3, 1, 4]
def baseStart_3314716 : Nat := 118140960795 + 3314716 * 2 ^ 59
def prefixEnd_3314716 : Nat := 4983230072969 + 3 ^ 40 * 3314716 * 2
def baseEnd_3314716 : Nat := 567347513716252797368635

theorem tailTrace_3314716 : CollatzResearch.WordTrace tailWord_3314716 prefixEnd_3314716 567347513716252797368635 := by
  unfold tailWord_3314716
  simp only [CollatzResearch.WordTrace]
  refine ⟨60448812329678757633858001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80598416439571676845144001 60448812329678757633858001)
  ·
    refine ⟨45336609247259068225393501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60448812329678757633858001 45336609247259068225393501)
    ·
      refine ⟨17001228467722150584522563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45336609247259068225393501 17001228467722150584522563)
      ·
        refine ⟨25501842701583225876783845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17001228467722150584522563 25501842701583225876783845)
        ·
          refine ⟨4781595506546854851896971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25501842701583225876783845 4781595506546854851896971)
          ·
            refine ⟨7172393259820282277845457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781595506546854851896971 7172393259820282277845457)
            ·
              refine ⟨5379294944865211708384093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7172393259820282277845457 5379294944865211708384093)
              ·
                refine ⟨2017235604324454390644035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5379294944865211708384093 2017235604324454390644035)
                ·
                  refine ⟨3025853406486681585966053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017235604324454390644035 3025853406486681585966053)
                  ·
                    refine ⟨567347513716252797368635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3025853406486681585966053 567347513716252797368635)
                    ·
                      rfl

theorem cell23_3314716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_3314716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314716 prefixEnd_3314716 := by exact prefixLift 3314716
  have htrace : WordTrace (prefixWord ++ tailWord_3314716) baseStart_3314716 baseEnd_3314716 := by
    simpa [prefixWord, tailWord_3314716, baseEnd_3314716] using wordTrace_append hprefix tailTrace_3314716
  have hstable : (prefixWord ++ tailWord_3314716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314716).length < 2 ^ (prefixWord ++ tailWord_3314716).sum := by decide
  have hdescent : baseEnd_3314716 < baseStart_3314716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314732 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 4, 3, 2]
def baseStart_3314732 : Nat := 118140960795 + 3314732 * 2 ^ 59
def prefixEnd_3314732 : Nat := 4983230072969 + 3 ^ 40 * 3314732 * 2
def baseEnd_3314732 : Nat := 1702050756839230329505831

theorem tailTrace_3314732 : CollatzResearch.WordTrace tailWord_3314732 prefixEnd_3314732 1702050756839230329505831 := by
  unfold tailWord_3314732
  simp only [CollatzResearch.WordTrace]
  refine ⟨60449104113649775000149225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80598805484866366666865633 60449104113649775000149225)
  ·
    refine ⟨45336828085237331250111919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60449104113649775000149225 45336828085237331250111919)
    ·
      refine ⟨68005242127855996875167879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45336828085237331250111919 68005242127855996875167879)
      ·
        refine ⟨102007863191783995312751819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68005242127855996875167879 102007863191783995312751819)
        ·
          refine ⟨153011794787675992969127729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102007863191783995312751819 153011794787675992969127729)
          ·
            refine ⟨114758846090756994726845797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153011794787675992969127729 114758846090756994726845797)
            ·
              refine ⟨21517283642016936511283587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114758846090756994726845797 21517283642016936511283587)
              ·
                refine ⟨32275925463025404766925381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21517283642016936511283587 32275925463025404766925381)
                ·
                  refine ⟨6051736024317263393798509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32275925463025404766925381 6051736024317263393798509)
                  ·
                    refine ⟨2269401009118973772674441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6051736024317263393798509 2269401009118973772674441)
                    ·
                      refine ⟨1702050756839230329505831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269401009118973772674441 1702050756839230329505831)
                      ·
                        rfl

theorem cell23_3314732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 3, 2].length) (baseStart_3314732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314732 prefixEnd_3314732 := by exact prefixLift 3314732
  have htrace : WordTrace (prefixWord ++ tailWord_3314732) baseStart_3314732 baseEnd_3314732 := by
    simpa [prefixWord, tailWord_3314732, baseEnd_3314732] using wordTrace_append hprefix tailTrace_3314732
  have hstable : (prefixWord ++ tailWord_3314732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314732).length < 2 ^ (prefixWord ++ tailWord_3314732).sum := by decide
  have hdescent : baseEnd_3314732 < baseStart_3314732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314762 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_3314762 : Nat := 118140960795 + 3314762 * 2 ^ 59
def prefixEnd_3314762 : Nat := 4983230072969 + 3 ^ 40 * 3314762 * 2
def baseEnd_3314762 : Nat := 1702066161258865212130693

theorem tailTrace_3314762 : CollatzResearch.WordTrace tailWord_3314762 prefixEnd_3314762 1702066161258865212130693 := by
  unfold tailWord_3314762
  simp only [CollatzResearch.WordTrace]
  refine ⟨30224825604297716280972635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80599534944793910082593693 30224825604297716280972635)
  ·
    refine ⟨45337238406446574421458953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30224825604297716280972635 45337238406446574421458953)
    ·
      refine ⟨34002928804834930816094215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45337238406446574421458953 34002928804834930816094215)
      ·
        refine ⟨51004393207252396224141323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34002928804834930816094215 51004393207252396224141323)
        ·
          refine ⟨76506589810878594336211985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51004393207252396224141323 76506589810878594336211985)
          ·
            refine ⟨57379942358158945752158989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76506589810878594336211985 57379942358158945752158989)
            ·
              refine ⟨21517478384309604657059621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57379942358158945752158989 21517478384309604657059621)
              ·
                refine ⟨4034527197058050873198679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21517478384309604657059621 4034527197058050873198679)
                ·
                  refine ⟨6051790795587076309798019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4034527197058050873198679 6051790795587076309798019)
                  ·
                    refine ⟨9077686193380614464697029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6051790795587076309798019 9077686193380614464697029)
                    ·
                      refine ⟨1702066161258865212130693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9077686193380614464697029 1702066161258865212130693)
                      ·
                        rfl

theorem cell23_3314762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_3314762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314762 prefixEnd_3314762 := by exact prefixLift 3314762
  have htrace : WordTrace (prefixWord ++ tailWord_3314762) baseStart_3314762 baseEnd_3314762 := by
    simpa [prefixWord, tailWord_3314762, baseEnd_3314762] using wordTrace_append hprefix tailTrace_3314762
  have hstable : (prefixWord ++ tailWord_3314762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314762).length < 2 ^ (prefixWord ++ tailWord_3314762).sum := by decide
  have hdescent : baseEnd_3314762 < baseStart_3314762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314772 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_3314772 : Nat := 118140960795 + 3314772 * 2 ^ 59
def prefixEnd_3314772 : Nat := 4983230072969 + 3 ^ 40 * 3314772 * 2
def baseEnd_3314772 : Nat := 567357098688470057668549

theorem tailTrace_3314772 : CollatzResearch.WordTrace tailWord_3314772 prefixEnd_3314772 567357098688470057668549 := by
  unfold tailWord_3314772
  simp only [CollatzResearch.WordTrace]
  refine ⟨60449833573577318415877285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80599778098103091221169713 60449833573577318415877285)
  ·
    refine ⟨11334343795045747202976991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60449833573577318415877285 11334343795045747202976991)
    ·
      refine ⟨17001515692568620804465487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11334343795045747202976991 17001515692568620804465487)
      ·
        refine ⟨25502273538852931206698231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17001515692568620804465487 25502273538852931206698231)
        ·
          refine ⟨38253410308279396810047347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25502273538852931206698231 38253410308279396810047347)
          ·
            refine ⟨57380115462419095215071021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38253410308279396810047347 57380115462419095215071021)
            ·
              refine ⟨21517543298407160705651633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57380115462419095215071021 21517543298407160705651633)
              ·
                refine ⟨16138157473805370529238725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21517543298407160705651633 16138157473805370529238725)
                ·
                  refine ⟨3025904526338506974232261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16138157473805370529238725 3025904526338506974232261)
                  ·
                    refine ⟨567357098688470057668549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3025904526338506974232261 567357098688470057668549)
                    ·
                      rfl

theorem cell23_3314772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_3314772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314772 prefixEnd_3314772 := by exact prefixLift 3314772
  have htrace : WordTrace (prefixWord ++ tailWord_3314772) baseStart_3314772 baseEnd_3314772 := by
    simpa [prefixWord, tailWord_3314772, baseEnd_3314772] using wordTrace_append hprefix tailTrace_3314772
  have hstable : (prefixWord ++ tailWord_3314772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314772).length < 2 ^ (prefixWord ++ tailWord_3314772).sum := by decide
  have hdescent : baseEnd_3314772 < baseStart_3314772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314775 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_3314775 : Nat := 118140960795 + 3314775 * 2 ^ 59
def prefixEnd_3314775 : Nat := 4983230072969 + 3 ^ 40 * 3314775 * 2
def baseEnd_3314775 : Nat := 1702072836507373661268133

theorem tailTrace_3314775 : CollatzResearch.WordTrace tailWord_3314775 prefixEnd_3314775 1702072836507373661268133 := by
  unfold tailWord_3314775
  simp only [CollatzResearch.WordTrace]
  refine ⟨120899776566143768344113779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80599851044095845562742519 120899776566143768344113779)
  ·
    refine ⟨181349664849215652516170669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120899776566143768344113779 181349664849215652516170669)
    ·
      refine ⟨68006124318455869693564001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181349664849215652516170669 68006124318455869693564001)
      ·
        refine ⟨51004593238841902270173001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68006124318455869693564001 51004593238841902270173001)
        ·
          refine ⟨38253444929131426702629751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51004593238841902270173001 38253444929131426702629751)
          ·
            refine ⟨57380167393697140053944627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38253444929131426702629751 57380167393697140053944627)
            ·
              refine ⟨86070251090545710080916941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57380167393697140053944627 86070251090545710080916941)
              ·
                refine ⟨32276344158954641280343853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86070251090545710080916941 32276344158954641280343853)
                ·
                  refine ⟨12103629059607990480128945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32276344158954641280343853 12103629059607990480128945)
                  ·
                    refine ⟨9077721794705992860096709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12103629059607990480128945 9077721794705992860096709)
                    ·
                      refine ⟨1702072836507373661268133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9077721794705992860096709 1702072836507373661268133)
                      ·
                        rfl

theorem cell23_3314775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_3314775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314775 prefixEnd_3314775 := by exact prefixLift 3314775
  have htrace : WordTrace (prefixWord ++ tailWord_3314775) baseStart_3314775 baseEnd_3314775 := by
    simpa [prefixWord, tailWord_3314775, baseEnd_3314775] using wordTrace_append hprefix tailTrace_3314775
  have hstable : (prefixWord ++ tailWord_3314775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314775).length < 2 ^ (prefixWord ++ tailWord_3314775).sum := by decide
  have hdescent : baseEnd_3314775 < baseStart_3314775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314812 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_3314812 : Nat := 118140960795 + 3314812 * 2 ^ 59
def prefixEnd_3314812 : Nat := 4983230072969 + 3 ^ 40 * 3314812 * 2
def baseEnd_3314812 : Nat := 1702091835291590016505463

theorem tailTrace_3314812 : CollatzResearch.WordTrace tailWord_3314812 prefixEnd_3314812 1702091835291590016505463 := by
  unfold tailWord_3314812
  simp only [CollatzResearch.WordTrace]
  refine ⟨60450563033504861831605345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80600750711339815775473793 60450563033504861831605345)
  ·
    refine ⟨45337922275128646373704009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60450563033504861831605345 45337922275128646373704009)
    ·
      refine ⟨34003441706346484780278007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45337922275128646373704009 34003441706346484780278007)
      ·
        refine ⟨51005162559519727170417011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34003441706346484780278007 51005162559519727170417011)
        ·
          refine ⟨76507743839279590755625517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51005162559519727170417011 76507743839279590755625517)
          ·
            refine ⟨28690403939729846533359569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76507743839279590755625517 28690403939729846533359569)
            ·
              refine ⟨21517802954797384900019677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28690403939729846533359569 21517802954797384900019677)
              ·
                refine ⟨8069176108049019337507379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21517802954797384900019677 8069176108049019337507379)
                ·
                  refine ⟨12103764162073529006261069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8069176108049019337507379 12103764162073529006261069)
                  ·
                    refine ⟨4538911560777573377347901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12103764162073529006261069 4538911560777573377347901)
                    ·
                      refine ⟨1702091835291590016505463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4538911560777573377347901 1702091835291590016505463)
                      ·
                        rfl

theorem cell23_3314812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_3314812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314812 prefixEnd_3314812 := by exact prefixLift 3314812
  have htrace : WordTrace (prefixWord ++ tailWord_3314812) baseStart_3314812 baseEnd_3314812 := by
    simpa [prefixWord, tailWord_3314812, baseEnd_3314812] using wordTrace_append hprefix tailTrace_3314812
  have hstable : (prefixWord ++ tailWord_3314812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314812).length < 2 ^ (prefixWord ++ tailWord_3314812).sum := by decide
  have hdescent : baseEnd_3314812 < baseStart_3314812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314847 : List Nat := [1, 1, 2, 6, 2, 2, 2, 2, 1, 2, 2]
def baseStart_3314847 : Nat := 118140960795 + 3314847 * 2 ^ 59
def prefixEnd_3314847 : Nat := 4983230072969 + 3 ^ 40 * 3314847 * 2
def baseEnd_3314847 : Nat := 1702109807114497379567803

theorem tailTrace_3314847 : CollatzResearch.WordTrace tailWord_3314847 prefixEnd_3314847 1702109807114497379567803 := by
  unfold tailWord_3314847
  simp only [CollatzResearch.WordTrace]
  refine ⟨120902402621882924640734795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80601601747921949760489863 120902402621882924640734795)
  ·
    refine ⟨181353603932824386961102193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120902402621882924640734795 181353603932824386961102193)
    ·
      refine ⟨136015202949618290220826645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181353603932824386961102193 136015202949618290220826645)
      ·
        refine ⟨6375712638263357354101249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136015202949618290220826645 6375712638263357354101249)
        ·
          refine ⟨4781784478697518015575937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6375712638263357354101249 4781784478697518015575937)
          ·
            refine ⟨3586338359023138511681953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4781784478697518015575937 3586338359023138511681953)
            ·
              refine ⟨2689753769267353883761465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586338359023138511681953 2689753769267353883761465)
              ·
                refine ⟨2017315326950515412821099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689753769267353883761465 2017315326950515412821099)
                ·
                  refine ⟨3025972990425773119231649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017315326950515412821099 3025972990425773119231649)
                  ·
                    refine ⟨2269479742819329839423737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3025972990425773119231649 2269479742819329839423737)
                    ·
                      refine ⟨1702109807114497379567803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269479742819329839423737 1702109807114497379567803)
                      ·
                        rfl

theorem cell23_3314847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_3314847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314847 prefixEnd_3314847 := by exact prefixLift 3314847
  have htrace : WordTrace (prefixWord ++ tailWord_3314847) baseStart_3314847 baseEnd_3314847 := by
    simpa [prefixWord, tailWord_3314847, baseEnd_3314847] using wordTrace_append hprefix tailTrace_3314847
  have hstable : (prefixWord ++ tailWord_3314847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314847).length < 2 ^ (prefixWord ++ tailWord_3314847).sum := by decide
  have hdescent : baseEnd_3314847 < baseStart_3314847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314852 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_3314852 : Nat := 118140960795 + 3314852 * 2 ^ 59
def prefixEnd_3314852 : Nat := 4983230072969 + 3 ^ 40 * 3314852 * 2
def baseEnd_3314852 : Nat := 1702112374517769860005279

theorem tailTrace_3314852 : CollatzResearch.WordTrace tailWord_3314852 prefixEnd_3314852 1702112374517769860005279 := by
  unfold tailWord_3314852
  simp only [CollatzResearch.WordTrace]
  refine ⟨60451292493432405247333405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80601723324576540329777873 60451292493432405247333405)
  ·
    refine ⟨22669234685037151967750027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60451292493432405247333405 22669234685037151967750027)
    ·
      refine ⟨34003852027555727951625041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22669234685037151967750027 34003852027555727951625041)
      ·
        refine ⟨25502889020666795963718781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34003852027555727951625041 25502889020666795963718781)
        ·
          refine ⟨9563583382750048486394543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25502889020666795963718781 9563583382750048486394543)
          ·
            refine ⟨14345375074125072729591815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9563583382750048486394543 14345375074125072729591815)
            ·
              refine ⟨21518062611187609094387723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14345375074125072729591815 21518062611187609094387723)
              ·
                refine ⟨32277093916781413641581585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21518062611187609094387723 32277093916781413641581585)
                ·
                  refine ⟨24207820437586060231186189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32277093916781413641581585 24207820437586060231186189)
                  ·
                    refine ⟨9077932664094772586694821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24207820437586060231186189 9077932664094772586694821)
                    ·
                      refine ⟨1702112374517769860005279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9077932664094772586694821 1702112374517769860005279)
                      ·
                        rfl

theorem cell23_3314852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_3314852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314852 prefixEnd_3314852 := by exact prefixLift 3314852
  have htrace : WordTrace (prefixWord ++ tailWord_3314852) baseStart_3314852 baseEnd_3314852 := by
    simpa [prefixWord, tailWord_3314852, baseEnd_3314852] using wordTrace_append hprefix tailTrace_3314852
  have hstable : (prefixWord ++ tailWord_3314852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314852).length < 2 ^ (prefixWord ++ tailWord_3314852).sum := by decide
  have hdescent : baseEnd_3314852 < baseStart_3314852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314885 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_3314885 : Nat := 118140960795 + 3314885 * 2 ^ 59
def prefixEnd_3314885 : Nat := 4983230072969 + 3 ^ 40 * 3314885 * 2
def baseEnd_3314885 : Nat := 1702129319379368230892627

theorem tailTrace_3314885 : CollatzResearch.WordTrace tailWord_3314885 prefixEnd_3314885 1702129319379368230892627 := by
  unfold tailWord_3314885
  simp only [CollatzResearch.WordTrace]
  refine ⟨120903788595745257130618109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80602525730496838087078739 120903788595745257130618109)
  ·
    refine ⟨45338920723404471423981791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120903788595745257130618109 45338920723404471423981791)
    ·
      refine ⟨68008381085106707135972687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45338920723404471423981791 68008381085106707135972687)
      ·
        refine ⟨102012571627660060703959031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68008381085106707135972687 102012571627660060703959031)
        ·
          refine ⟨153018857441490091055938547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102012571627660060703959031 153018857441490091055938547)
          ·
            refine ⟨229528286162235136583907821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153018857441490091055938547 229528286162235136583907821)
            ·
              refine ⟨86073107310838176218965433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229528286162235136583907821 86073107310838176218965433)
              ·
                refine ⟨64554830483128632164224075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86073107310838176218965433 64554830483128632164224075)
                ·
                  refine ⟨96832245724692948246336113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64554830483128632164224075 96832245724692948246336113)
                  ·
                    refine ⟨72624184293519711184752085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96832245724692948246336113 72624184293519711184752085)
                    ·
                      refine ⟨1702129319379368230892627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72624184293519711184752085 1702129319379368230892627)
                      ·
                        rfl

theorem cell23_3314885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_3314885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314885 prefixEnd_3314885 := by exact prefixLift 3314885
  have htrace : WordTrace (prefixWord ++ tailWord_3314885) baseStart_3314885 baseEnd_3314885 := by
    simpa [prefixWord, tailWord_3314885, baseEnd_3314885] using wordTrace_append hprefix tailTrace_3314885
  have hstable : (prefixWord ++ tailWord_3314885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314885).length < 2 ^ (prefixWord ++ tailWord_3314885).sum := by decide
  have hdescent : baseEnd_3314885 < baseStart_3314885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314922 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_3314922 : Nat := 118140960795 + 3314922 * 2 ^ 59
def prefixEnd_3314922 : Nat := 4983230072969 + 3 ^ 40 * 3314922 * 2
def baseEnd_3314922 : Nat := 567382772721194862043319

theorem tailTrace_3314922 : CollatzResearch.WordTrace tailWord_3314922 prefixEnd_3314922 567382772721194862043319 := by
  unfold tailWord_3314922
  simp only [CollatzResearch.WordTrace]
  refine ⟨30226284524152803112428755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80603425397740808299810013 30226284524152803112428755)
  ·
    refine ⟨45339426786229204668643133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30226284524152803112428755 45339426786229204668643133)
    ·
      refine ⟨17002285044835951750741175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45339426786229204668643133 17002285044835951750741175)
      ·
        refine ⟨25503427567253927626111763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17002285044835951750741175 25503427567253927626111763)
        ·
          refine ⟨38255141350880891439167645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25503427567253927626111763 38255141350880891439167645)
          ·
            refine ⟨14345678006580334289687867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38255141350880891439167645 14345678006580334289687867)
            ·
              refine ⟨21518517009870501434531801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14345678006580334289687867 21518517009870501434531801)
              ·
                refine ⟨16138887757402876075898851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21518517009870501434531801 16138887757402876075898851)
                ·
                  refine ⟨24208331636104314113848277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16138887757402876075898851 24208331636104314113848277)
                  ·
                    refine ⟨567382772721194862043319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24208331636104314113848277 567382772721194862043319)
                    ·
                      rfl

theorem cell23_3314922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_3314922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314922 prefixEnd_3314922 := by exact prefixLift 3314922
  have htrace : WordTrace (prefixWord ++ tailWord_3314922) baseStart_3314922 baseEnd_3314922 := by
    simpa [prefixWord, tailWord_3314922, baseEnd_3314922] using wordTrace_append hprefix tailTrace_3314922
  have hstable : (prefixWord ++ tailWord_3314922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314922).length < 2 ^ (prefixWord ++ tailWord_3314922).sum := by decide
  have hdescent : baseEnd_3314922 < baseStart_3314922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314972 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3314972 : Nat := 118140960795 + 3314972 * 2 ^ 59
def prefixEnd_3314972 : Nat := 4983230072969 + 3 ^ 40 * 3314972 * 2
def baseEnd_3314972 : Nat := 1702173992196309390504727

theorem tailTrace_3314972 : CollatzResearch.WordTrace tailWord_3314972 prefixEnd_3314972 1702173992196309390504727 := by
  unfold tailWord_3314972
  simp only [CollatzResearch.WordTrace]
  refine ⟨60453480873215035494517585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80604641164286713992690113 60453480873215035494517585)
  ·
    refine ⟨45340110654911276620888189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60453480873215035494517585 45340110654911276620888189)
    ·
      refine ⟨17002541495591728732833071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45340110654911276620888189 17002541495591728732833071)
      ·
        refine ⟨25503812243387593099249607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17002541495591728732833071 25503812243387593099249607)
        ·
          refine ⟨38255718365081389648874411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25503812243387593099249607 38255718365081389648874411)
          ·
            refine ⟨57383577547622084473311617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38255718365081389648874411 57383577547622084473311617)
            ·
              refine ⟨43037683160716563354983713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57383577547622084473311617 43037683160716563354983713)
              ·
                refine ⟨32278262370537422516237785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43037683160716563354983713 32278262370537422516237785)
                ·
                  refine ⟨24208696777903066887178339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32278262370537422516237785 24208696777903066887178339)
                  ·
                    refine ⟨36313045166854600330767509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24208696777903066887178339 36313045166854600330767509)
                    ·
                      refine ⟨1702173992196309390504727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36313045166854600330767509 1702173992196309390504727)
                      ·
                        rfl

theorem cell23_3314972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3314972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3314972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3314972 prefixEnd_3314972 := by exact prefixLift 3314972
  have htrace : WordTrace (prefixWord ++ tailWord_3314972) baseStart_3314972 baseEnd_3314972 := by
    simpa [prefixWord, tailWord_3314972, baseEnd_3314972] using wordTrace_append hprefix tailTrace_3314972
  have hstable : (prefixWord ++ tailWord_3314972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314972).length < 2 ^ (prefixWord ++ tailWord_3314972).sum := by decide
  have hdescent : baseEnd_3314972 < baseStart_3314972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315020 : List Nat := [2, 2, 1, 3, 2, 4, 2, 2, 1, 4]
def baseStart_3315020 : Nat := 118140960795 + 3315020 * 2 ^ 59
def prefixEnd_3315020 : Nat := 4983230072969 + 3 ^ 40 * 3315020 * 2
def baseEnd_3315020 : Nat := 567399546422575067568169

theorem tailTrace_3315020 : CollatzResearch.WordTrace tailWord_3315020 prefixEnd_3315020 567399546422575067568169 := by
  unfold tailWord_3315020
  simp only [CollatzResearch.WordTrace]
  refine ⟨60454356225128087593391257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80605808300170783457855009 60454356225128087593391257)
  ·
    refine ⟨45340767168846065695043443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60454356225128087593391257 45340767168846065695043443)
    ·
      refine ⟨68011150753269098542565165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45340767168846065695043443 68011150753269098542565165)
      ·
        refine ⟨25504181532475911953461937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68011150753269098542565165 25504181532475911953461937)
        ·
          refine ⟨19128136149356933965096453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25504181532475911953461937 19128136149356933965096453)
          ·
            refine ⟨3586525528004425118455585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19128136149356933965096453 3586525528004425118455585)
            ·
              refine ⟨2689894146003318838841689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586525528004425118455585 2689894146003318838841689)
              ·
                refine ⟨2017420609502489129131267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689894146003318838841689 2017420609502489129131267)
                ·
                  refine ⟨3026130914253733693696901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017420609502489129131267 3026130914253733693696901)
                  ·
                    refine ⟨567399546422575067568169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3026130914253733693696901 567399546422575067568169)
                    ·
                      rfl

theorem cell23_3315020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_3315020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315020 prefixEnd_3315020 := by exact prefixLift 3315020
  have htrace : WordTrace (prefixWord ++ tailWord_3315020) baseStart_3315020 baseEnd_3315020 := by
    simpa [prefixWord, tailWord_3315020, baseEnd_3315020] using wordTrace_append hprefix tailTrace_3315020
  have hstable : (prefixWord ++ tailWord_3315020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315020).length < 2 ^ (prefixWord ++ tailWord_3315020).sum := by decide
  have hdescent : baseEnd_3315020 < baseStart_3315020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315026 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_3315026 : Nat := 118140960795 + 3315026 * 2 ^ 59
def prefixEnd_3315026 : Nat := 4983230072969 + 3 ^ 40 * 3315026 * 2
def baseEnd_3315026 : Nat := 1702201720151652179229479

theorem tailTrace_3315026 : CollatzResearch.WordTrace tailWord_3315026 prefixEnd_3315026 1702201720151652179229479 := by
  unfold tailWord_3315026
  simp only [CollatzResearch.WordTrace]
  refine ⟨30227232822058609552875233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80605954192156292141000621 30227232822058609552875233)
  ·
    refine ⟨22670424616543957164656425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30227232822058609552875233 22670424616543957164656425)
    ·
      refine ⟨17002818462407967873492319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22670424616543957164656425 17002818462407967873492319)
      ·
        refine ⟨25504227693611951810238479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17002818462407967873492319 25504227693611951810238479)
        ·
          refine ⟨38256341540417927715357719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25504227693611951810238479 38256341540417927715357719)
          ·
            refine ⟨57384512310626891573036579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38256341540417927715357719 57384512310626891573036579)
            ·
              refine ⟨86076768465940337359554869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57384512310626891573036579 86076768465940337359554869)
              ·
                refine ⟨8069697043681906627458269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86076768465940337359554869 8069697043681906627458269)
                ·
                  refine ⟨3026136391380714985296851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8069697043681906627458269 3026136391380714985296851)
                  ·
                    refine ⟨4539204587071072477945277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3026136391380714985296851 4539204587071072477945277)
                    ·
                      refine ⟨1702201720151652179229479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4539204587071072477945277 1702201720151652179229479)
                      ·
                        rfl

theorem cell23_3315026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_3315026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315026 prefixEnd_3315026 := by exact prefixLift 3315026
  have htrace : WordTrace (prefixWord ++ tailWord_3315026) baseStart_3315026 baseEnd_3315026 := by
    simpa [prefixWord, tailWord_3315026, baseEnd_3315026] using wordTrace_append hprefix tailTrace_3315026
  have hstable : (prefixWord ++ tailWord_3315026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315026).length < 2 ^ (prefixWord ++ tailWord_3315026).sum := by decide
  have hdescent : baseEnd_3315026 < baseStart_3315026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315029 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_3315029 : Nat := 118140960795 + 3315029 * 2 ^ 59
def prefixEnd_3315029 : Nat := 4983230072969 + 3 ^ 40 * 3315029 * 2
def baseEnd_3315029 : Nat := 567401086864538555830655

theorem tailTrace_3315029 : CollatzResearch.WordTrace tailWord_3315029 prefixEnd_3315029 567401086864538555830655 := by
  unfold tailWord_3315029
  simp only [CollatzResearch.WordTrace]
  refine ⟨120909040707223569723860141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80606027138149046482573427 120909040707223569723860141)
  ·
    refine ⟨45340890265208838646447553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120909040707223569723860141 45340890265208838646447553)
    ·
      refine ⟨34005667698906628984835665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45340890265208838646447553 34005667698906628984835665)
      ·
        refine ⟨25504250774179971738626749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34005667698906628984835665 25504250774179971738626749)
        ·
          refine ⟨9564094040317489401985031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25504250774179971738626749 9564094040317489401985031)
          ·
            refine ⟨14346141060476234102977547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564094040317489401985031 14346141060476234102977547)
            ·
              refine ⟨21519211590714351154466321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14346141060476234102977547 21519211590714351154466321)
              ·
                refine ⟨16139408693035763365849741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21519211590714351154466321 16139408693035763365849741)
                ·
                  refine ⟨6052278259888411262193653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16139408693035763365849741 6052278259888411262193653)
                  ·
                    refine ⟨567401086864538555830655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6052278259888411262193653 567401086864538555830655)
                    ·
                      rfl

theorem cell23_3315029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_3315029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315029 prefixEnd_3315029 := by exact prefixLift 3315029
  have htrace : WordTrace (prefixWord ++ tailWord_3315029) baseStart_3315029 baseEnd_3315029 := by
    simpa [prefixWord, tailWord_3315029, baseEnd_3315029] using wordTrace_append hprefix tailTrace_3315029
  have hstable : (prefixWord ++ tailWord_3315029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315029).length < 2 ^ (prefixWord ++ tailWord_3315029).sum := by decide
  have hdescent : baseEnd_3315029 < baseStart_3315029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315049 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 1, 8, 2]
def baseStart_3315049 : Nat := 118140960795 + 3315049 * 2 ^ 59
def prefixEnd_3315049 : Nat := 4983230072969 + 3 ^ 40 * 3315049 * 2
def baseEnd_3315049 : Nat := 1702213530206705589241873

theorem tailTrace_3315049 : CollatzResearch.WordTrace tailWord_3315049 prefixEnd_3315049 1702213530206705589241873 := by
  unfold tailWord_3315049
  simp only [CollatzResearch.WordTrace]
  refine ⟨120909770167151113139588201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80606513444767408759725467 120909770167151113139588201)
  ·
    refine ⟨90682327625363334854691151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120909770167151113139588201 90682327625363334854691151)
    ·
      refine ⟨136023491438045002282036727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90682327625363334854691151 136023491438045002282036727)
      ·
        refine ⟨204035237157067503423055091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136023491438045002282036727 204035237157067503423055091)
        ·
          refine ⟨306052855735601255134582637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204035237157067503423055091 306052855735601255134582637)
          ·
            refine ⟨114769820900850470675468489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306052855735601255134582637 114769820900850470675468489)
            ·
              refine ⟨86077365675637853006601367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114769820900850470675468489 86077365675637853006601367)
              ·
                refine ⟨129116048513456779509902051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86077365675637853006601367 129116048513456779509902051)
                ·
                  refine ⟨193674072770185169264853077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129116048513456779509902051 193674072770185169264853077)
                  ·
                    refine ⟨2269618040275607452322497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 193674072770185169264853077 2269618040275607452322497)
                    ·
                      refine ⟨1702213530206705589241873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269618040275607452322497 1702213530206705589241873)
                      ·
                        rfl

theorem cell23_3315049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 8, 2].length) (baseStart_3315049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315049 prefixEnd_3315049 := by exact prefixLift 3315049
  have htrace : WordTrace (prefixWord ++ tailWord_3315049) baseStart_3315049 baseEnd_3315049 := by
    simpa [prefixWord, tailWord_3315049, baseEnd_3315049] using wordTrace_append hprefix tailTrace_3315049
  have hstable : (prefixWord ++ tailWord_3315049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315049).length < 2 ^ (prefixWord ++ tailWord_3315049).sum := by decide
  have hdescent : baseEnd_3315049 < baseStart_3315049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315053 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_3315053 : Nat := 118140960795 + 3315053 * 2 ^ 59
def prefixEnd_3315053 : Nat := 4983230072969 + 3 ^ 40 * 3315053 * 2
def baseEnd_3315053 : Nat := 1702215584129323573591855

theorem tailTrace_3315053 : CollatzResearch.WordTrace tailWord_3315053 prefixEnd_3315053 1702215584129323573591855 := by
  unfold tailWord_3315053
  simp only [CollatzResearch.WordTrace]
  refine ⟨120909916059136621822733813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80606610706091081215155875 120909916059136621822733813)
  ·
    refine ⟨11335304630544058295881295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120909916059136621822733813 11335304630544058295881295)
    ·
      refine ⟨17002956945816087443821943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11335304630544058295881295 17002956945816087443821943)
      ·
        refine ⟨25504435418724131165732915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17002956945816087443821943 25504435418724131165732915)
        ·
          refine ⟨38256653128086196748599373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25504435418724131165732915 38256653128086196748599373)
          ·
            refine ⟨14346244923032323780724765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38256653128086196748599373 14346244923032323780724765)
            ·
              refine ⟨5379841846137121417771787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14346244923032323780724765 5379841846137121417771787)
              ·
                refine ⟨8069762769205682126657681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5379841846137121417771787 8069762769205682126657681)
                ·
                  refine ⟨6052322076904261594993261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8069762769205682126657681 6052322076904261594993261)
                  ·
                    refine ⟨2269620778839098098122473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6052322076904261594993261 2269620778839098098122473)
                    ·
                      refine ⟨1702215584129323573591855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269620778839098098122473 1702215584129323573591855)
                      ·
                        rfl

theorem cell23_3315053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_3315053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315053 prefixEnd_3315053 := by exact prefixLift 3315053
  have htrace : WordTrace (prefixWord ++ tailWord_3315053) baseStart_3315053 baseEnd_3315053 := by
    simpa [prefixWord, tailWord_3315053, baseEnd_3315053] using wordTrace_append hprefix tailTrace_3315053
  have hstable : (prefixWord ++ tailWord_3315053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315053).length < 2 ^ (prefixWord ++ tailWord_3315053).sum := by decide
  have hdescent : baseEnd_3315053 < baseStart_3315053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315069 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_3315069 : Nat := 118140960795 + 3315069 * 2 ^ 59
def prefixEnd_3315069 : Nat := 4983230072969 + 3 ^ 40 * 3315069 * 2
def baseEnd_3315069 : Nat := 1702223799819795510991781

theorem tailTrace_3315069 : CollatzResearch.WordTrace tailWord_3315069 prefixEnd_3315069 1702223799819795510991781 := by
  unfold tailWord_3315069
  simp only [CollatzResearch.WordTrace]
  refine ⟨120910499627078656555316261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80606999751385771036877507 120910499627078656555316261)
  ·
    refine ⟨22670718680077248104121799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120910499627078656555316261 22670718680077248104121799)
    ·
      refine ⟨34006078020115872156182699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22670718680077248104121799 34006078020115872156182699)
      ·
        refine ⟨51009117030173808234274049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34006078020115872156182699 51009117030173808234274049)
        ·
          refine ⟨38256837772630356175705537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51009117030173808234274049 38256837772630356175705537)
          ·
            refine ⟨28692628329472767131779153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38256837772630356175705537 28692628329472767131779153)
            ·
              refine ⟨21519471247104575348834365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28692628329472767131779153 21519471247104575348834365)
              ·
                refine ⟨8069801717664215755812887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21519471247104575348834365 8069801717664215755812887)
                ·
                  refine ⟨12104702576496323633719331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8069801717664215755812887 12104702576496323633719331)
                  ·
                    refine ⟨18157053864744485450578997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12104702576496323633719331 18157053864744485450578997)
                    ·
                      refine ⟨1702223799819795510991781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18157053864744485450578997 1702223799819795510991781)
                      ·
                        rfl

theorem cell23_3315069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_3315069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315069 prefixEnd_3315069 := by exact prefixLift 3315069
  have htrace : WordTrace (prefixWord ++ tailWord_3315069) baseStart_3315069 baseEnd_3315069 := by
    simpa [prefixWord, tailWord_3315069, baseEnd_3315069] using wordTrace_append hprefix tailTrace_3315069
  have hstable : (prefixWord ++ tailWord_3315069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315069).length < 2 ^ (prefixWord ++ tailWord_3315069).sum := by decide
  have hdescent : baseEnd_3315069 < baseStart_3315069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315076 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_3315076 : Nat := 118140960795 + 3315076 * 2 ^ 59
def prefixEnd_3315076 : Nat := 4983230072969 + 3 ^ 40 * 3315076 * 2
def baseEnd_3315076 : Nat := 567409131394792327868083

theorem tailTrace_3315076 : CollatzResearch.WordTrace tailWord_3315076 prefixEnd_3315076 567409131394792327868083 := by
  unfold tailWord_3315076
  simp only [CollatzResearch.WordTrace]
  refine ⟨60455377469026648375410541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80607169958702197833880721 60455377469026648375410541)
  ·
    refine ⟨22670766550884993140778953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60455377469026648375410541 22670766550884993140778953)
    ·
      refine ⟨17003074913163744855584215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22670766550884993140778953 17003074913163744855584215)
      ·
        refine ⟨25504612369745617283376323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17003074913163744855584215 25504612369745617283376323)
        ·
          refine ⟨38256918554618425925064485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25504612369745617283376323 38256918554618425925064485)
          ·
            refine ⟨7173172228990954860949591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38256918554618425925064485 7173172228990954860949591)
            ·
              refine ⟨10759758343486432291424387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173172228990954860949591 10759758343486432291424387)
              ·
                refine ⟨16139637515229648437136581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10759758343486432291424387 16139637515229648437136581)
                ·
                  refine ⟨3026182034105559081963109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16139637515229648437136581 3026182034105559081963109)
                  ·
                    refine ⟨567409131394792327868083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3026182034105559081963109 567409131394792327868083)
                    ·
                      rfl

theorem cell23_3315076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_3315076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315076 prefixEnd_3315076 := by exact prefixLift 3315076
  have htrace : WordTrace (prefixWord ++ tailWord_3315076) baseStart_3315076 baseEnd_3315076 := by
    simpa [prefixWord, tailWord_3315076, baseEnd_3315076] using wordTrace_append hprefix tailTrace_3315076
  have hstable : (prefixWord ++ tailWord_3315076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315076).length < 2 ^ (prefixWord ++ tailWord_3315076).sum := by decide
  have hdescent : baseEnd_3315076 < baseStart_3315076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315083 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 3, 2, 2]
def baseStart_3315083 : Nat := 118140960795 + 3315083 * 2 ^ 59
def prefixEnd_3315083 : Nat := 4983230072969 + 3 ^ 40 * 3315083 * 2
def baseEnd_3315083 : Nat := 1702230988548958456216717

theorem tailTrace_3315083 : CollatzResearch.WordTrace tailWord_3315083 prefixEnd_3315083 1702230988548958456216717 := by
  unfold tailWord_3315083
  simp only [CollatzResearch.WordTrace]
  refine ⟨120911010249027936946325903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80607340166018624630883935 120911010249027936946325903)
  ·
    refine ⟨181366515373541905419488855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120911010249027936946325903 181366515373541905419488855)
    ·
      refine ⟨272049773060312858129233283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181366515373541905419488855 272049773060312858129233283)
      ·
        refine ⟨408074659590469287193849925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272049773060312858129233283 408074659590469287193849925)
        ·
          refine ⟨76513998673212991348846861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 408074659590469287193849925 76513998673212991348846861)
          ·
            refine ⟨28692749502454871755817573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76513998673212991348846861 28692749502454871755817573)
            ·
              refine ⟨5379890531710288454215795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28692749502454871755817573 5379890531710288454215795)
              ·
                refine ⟨8069835797565432681323693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5379890531710288454215795 8069835797565432681323693)
                ·
                  refine ⟨3026188424087037255496385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8069835797565432681323693 3026188424087037255496385)
                  ·
                    refine ⟨2269641318065277941622289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3026188424087037255496385 2269641318065277941622289)
                    ·
                      refine ⟨1702230988548958456216717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269641318065277941622289 1702230988548958456216717)
                      ·
                        rfl

theorem cell23_3315083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 2, 2].length) (baseStart_3315083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315083 prefixEnd_3315083 := by exact prefixLift 3315083
  have htrace : WordTrace (prefixWord ++ tailWord_3315083) baseStart_3315083 baseEnd_3315083 := by
    simpa [prefixWord, tailWord_3315083, baseEnd_3315083] using wordTrace_append hprefix tailTrace_3315083
  have hstable : (prefixWord ++ tailWord_3315083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315083).length < 2 ^ (prefixWord ++ tailWord_3315083).sum := by decide
  have hdescent : baseEnd_3315083 < baseStart_3315083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315096 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3315096 : Nat := 118140960795 + 3315096 * 2 ^ 59
def prefixEnd_3315096 : Nat := 4983230072969 + 3 ^ 40 * 3315096 * 2
def baseEnd_3315096 : Nat := 1702237663797466905354157

theorem tailTrace_3315096 : CollatzResearch.WordTrace tailWord_3315096 prefixEnd_3315096 1702237663797466905354157 := by
  unfold tailWord_3315096
  simp only [CollatzResearch.WordTrace]
  refine ⟨60455742198990420083274571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80607656265320560111032761 60455742198990420083274571)
  ·
    refine ⟨90683613298485630124911857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60455742198990420083274571 90683613298485630124911857)
    ·
      refine ⟨68012709973864222593683893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90683613298485630124911857 68012709973864222593683893)
      ·
        refine ⟨6376191560049770868157865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68012709973864222593683893 6376191560049770868157865)
        ·
          refine ⟨4782143670037328151118399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6376191560049770868157865 4782143670037328151118399)
          ·
            refine ⟨7173215505055992226677599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782143670037328151118399 7173215505055992226677599)
            ·
              refine ⟨10759823257583988340016399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173215505055992226677599 10759823257583988340016399)
              ·
                refine ⟨16139734886375982510024599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10759823257583988340016399 16139734886375982510024599)
                ·
                  refine ⟨24209602329563973765036899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16139734886375982510024599 24209602329563973765036899)
                  ·
                    refine ⟨36314403494345960647555349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24209602329563973765036899 36314403494345960647555349)
                    ·
                      refine ⟨1702237663797466905354157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36314403494345960647555349 1702237663797466905354157)
                      ·
                        rfl

theorem cell23_3315096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3315096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315096 prefixEnd_3315096 := by exact prefixLift 3315096
  have htrace : WordTrace (prefixWord ++ tailWord_3315096) baseStart_3315096 baseEnd_3315096 := by
    simpa [prefixWord, tailWord_3315096, baseEnd_3315096] using wordTrace_append hprefix tailTrace_3315096
  have hstable : (prefixWord ++ tailWord_3315096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315096).length < 2 ^ (prefixWord ++ tailWord_3315096).sum := by decide
  have hdescent : baseEnd_3315096 < baseStart_3315096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315100 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3315100 : Nat := 118140960795 + 3315100 * 2 ^ 59
def prefixEnd_3315100 : Nat := 4983230072969 + 3 ^ 40 * 3315100 * 2
def baseEnd_3315100 : Nat := 1702239717720084889704139

theorem tailTrace_3315100 : CollatzResearch.WordTrace tailWord_3315100 prefixEnd_3315100 1702239717720084889704139 := by
  unfold tailWord_3315100
  simp only [CollatzResearch.WordTrace]
  refine ⟨60455815144983174424847377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80607753526644232566463169 60455815144983174424847377)
  ·
    refine ⟨45341861358737380818635533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60455815144983174424847377 45341861358737380818635533)
    ·
      refine ⟨17003198009526517806988325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45341861358737380818635533 17003198009526517806988325)
      ·
        refine ⟨3188099626786222088810311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17003198009526517806988325 3188099626786222088810311)
        ·
          refine ⟨4782149440179333133215467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188099626786222088810311 4782149440179333133215467)
          ·
            refine ⟨7173224160268999699823201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782149440179333133215467 7173224160268999699823201)
            ·
              refine ⟨5379918120201749774867401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7173224160268999699823201 5379918120201749774867401)
              ·
                refine ⟨4034938590151312331150551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5379918120201749774867401 4034938590151312331150551)
                ·
                  refine ⟨6052407885226968496725827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4034938590151312331150551 6052407885226968496725827)
                  ·
                    refine ⟨9078611827840452745088741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6052407885226968496725827 9078611827840452745088741)
                    ·
                      refine ⟨1702239717720084889704139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9078611827840452745088741 1702239717720084889704139)
                      ·
                        rfl

theorem cell23_3315100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3315100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315100 prefixEnd_3315100 := by exact prefixLift 3315100
  have htrace : WordTrace (prefixWord ++ tailWord_3315100) baseStart_3315100 baseEnd_3315100 := by
    simpa [prefixWord, tailWord_3315100, baseEnd_3315100] using wordTrace_append hprefix tailTrace_3315100
  have hstable : (prefixWord ++ tailWord_3315100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315100).length < 2 ^ (prefixWord ++ tailWord_3315100).sum := by decide
  have hdescent : baseEnd_3315100 < baseStart_3315100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315103 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3315103 : Nat := 118140960795 + 3315103 * 2 ^ 59
def prefixEnd_3315103 : Nat := 4983230072969 + 3 ^ 40 * 3315103 * 2
def baseEnd_3315103 : Nat := 1702241258162048377966625

theorem tailTrace_3315103 : CollatzResearch.WordTrace tailWord_3315103 prefixEnd_3315103 1702241258162048377966625 := by
  unfold tailWord_3315103
  simp only [CollatzResearch.WordTrace]
  refine ⟨120911739708955480362053963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80607826472636986908035975 120911739708955480362053963)
  ·
    refine ⟨181367609563433220543080945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120911739708955480362053963 181367609563433220543080945)
    ·
      refine ⟨136025707172574915407310709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181367609563433220543080945 136025707172574915407310709)
      ·
        refine ⟨12752410047428898319435379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136025707172574915407310709 12752410047428898319435379)
        ·
          refine ⟨19128615071143347479153069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12752410047428898319435379 19128615071143347479153069)
          ·
            refine ⟨7173230651678755304682401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19128615071143347479153069 7173230651678755304682401)
            ·
              refine ⟨5379922988759066478511801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7173230651678755304682401 5379922988759066478511801)
              ·
                refine ⟨4034942241569299858883851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5379922988759066478511801 4034942241569299858883851)
                ·
                  refine ⟨6052413362353949788325777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4034942241569299858883851 6052413362353949788325777)
                  ·
                    refine ⟨4539310021765462341244333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6052413362353949788325777 4539310021765462341244333)
                    ·
                      refine ⟨1702241258162048377966625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4539310021765462341244333 1702241258162048377966625)
                      ·
                        rfl

theorem cell23_3315103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3315103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315103 prefixEnd_3315103 := by exact prefixLift 3315103
  have htrace : WordTrace (prefixWord ++ tailWord_3315103) baseStart_3315103 baseEnd_3315103 := by
    simpa [prefixWord, tailWord_3315103, baseEnd_3315103] using wordTrace_append hprefix tailTrace_3315103
  have hstable : (prefixWord ++ tailWord_3315103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315103).length < 2 ^ (prefixWord ++ tailWord_3315103).sum := by decide
  have hdescent : baseEnd_3315103 < baseStart_3315103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315106 : List Nat := [3, 3, 1, 2, 1, 2, 4, 7]
def baseStart_3315106 : Nat := 118140960795 + 3315106 * 2 ^ 59
def prefixEnd_3315106 : Nat := 4983230072969 + 3 ^ 40 * 3315106 * 2
def baseEnd_3315106 : Nat := 63046029577926365415893

theorem tailTrace_3315106 : CollatzResearch.WordTrace tailWord_3315106 prefixEnd_3315106 63046029577926365415893 := by
  unfold tailWord_3315106
  simp only [CollatzResearch.WordTrace]
  refine ⟨30227962281986152968603293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80607899418629741249608781 30227962281986152968603293)
  ·
    refine ⟨11335485855744807363226235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30227962281986152968603293 11335485855744807363226235)
    ·
      refine ⟨17003228783617211044839353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11335485855744807363226235 17003228783617211044839353)
      ·
        refine ⟨12752421587712908283629515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17003228783617211044839353 12752421587712908283629515)
        ·
          refine ⟨19128632381569362425444273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12752421587712908283629515 19128632381569362425444273)
          ·
            refine ⟨14346474286177021819083205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19128632381569362425444273 14346474286177021819083205)
            ·
              refine ⟨2689963928658191591078101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14346474286177021819083205 2689963928658191591078101)
              ·
                refine ⟨63046029577926365415893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2689963928658191591078101 63046029577926365415893)
                ·
                  rfl

theorem cell23_3315106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 7].length) (baseStart_3315106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315106 prefixEnd_3315106 := by exact prefixLift 3315106
  have htrace : WordTrace (prefixWord ++ tailWord_3315106) baseStart_3315106 baseEnd_3315106 := by
    simpa [prefixWord, tailWord_3315106, baseEnd_3315106] using wordTrace_append hprefix tailTrace_3315106
  have hstable : (prefixWord ++ tailWord_3315106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315106).length < 2 ^ (prefixWord ++ tailWord_3315106).sum := by decide
  have hdescent : baseEnd_3315106 < baseStart_3315106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315116 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 3]
def baseStart_3315116 : Nat := 118140960795 + 3315116 * 2 ^ 59
def prefixEnd_3315116 : Nat := 4983230072969 + 3 ^ 40 * 3315116 * 2
def baseEnd_3315116 : Nat := 1702247933410556827104065

theorem tailTrace_3315116 : CollatzResearch.WordTrace tailWord_3315116 prefixEnd_3315116 1702247933410556827104065 := by
  unfold tailWord_3315116
  simp only [CollatzResearch.WordTrace]
  refine ⟨60456106928954191791138601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80608142571938922388184801 60456106928954191791138601)
  ·
    refine ⟨45342080196715643843353951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60456106928954191791138601 45342080196715643843353951)
    ·
      refine ⟨68013120295073465765030927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45342080196715643843353951 68013120295073465765030927)
      ·
        refine ⟨102019680442610198647546391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68013120295073465765030927 102019680442610198647546391)
        ·
          refine ⟨153029520663915297971319587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102019680442610198647546391 153029520663915297971319587)
          ·
            refine ⟨229544280995872946956979381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153029520663915297971319587 229544280995872946956979381)
            ·
              refine ⟨21519776343363088777216817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229544280995872946956979381 21519776343363088777216817)
              ·
                refine ⟨16139832257522316582912613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21519776343363088777216817 16139832257522316582912613)
                ·
                  refine ⟨3026218548285434359296115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16139832257522316582912613 3026218548285434359296115)
                  ·
                    refine ⟨4539327822428151538944173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3026218548285434359296115 4539327822428151538944173)
                    ·
                      refine ⟨1702247933410556827104065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4539327822428151538944173 1702247933410556827104065)
                      ·
                        rfl

theorem cell23_3315116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_3315116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315116 prefixEnd_3315116 := by exact prefixLift 3315116
  have htrace : WordTrace (prefixWord ++ tailWord_3315116) baseStart_3315116 baseEnd_3315116 := by
    simpa [prefixWord, tailWord_3315116, baseEnd_3315116] using wordTrace_append hprefix tailTrace_3315116
  have hstable : (prefixWord ++ tailWord_3315116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315116).length < 2 ^ (prefixWord ++ tailWord_3315116).sum := by decide
  have hdescent : baseEnd_3315116 < baseStart_3315116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315133 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_3315133 : Nat := 118140960795 + 3315133 * 2 ^ 59
def prefixEnd_3315133 : Nat := 4983230072969 + 3 ^ 40 * 3315133 * 2
def baseEnd_3315133 : Nat := 1702256662581683260591487

theorem tailTrace_3315133 : CollatzResearch.WordTrace tailWord_3315133 prefixEnd_3315133 1702256662581683260591487 := by
  unfold tailWord_3315133
  simp only [CollatzResearch.WordTrace]
  refine ⟨120912833898846795485646053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80608555932564530323764035 120912833898846795485646053)
  ·
    refine ⟨22671156356033774153558635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120912833898846795485646053 22671156356033774153558635)
    ·
      refine ⟨34006734534050661230337953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22671156356033774153558635 34006734534050661230337953)
      ·
        refine ⟨25505050900537995922753465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34006734534050661230337953 25505050900537995922753465)
        ·
          refine ⟨19128788175403496942065099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25505050900537995922753465 19128788175403496942065099)
          ·
            refine ⟨28693182263105245413097649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19128788175403496942065099 28693182263105245413097649)
            ·
              refine ⟨21519886697328934059823237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28693182263105245413097649 21519886697328934059823237)
              ·
                refine ⟨4034978755749175136216857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21519886697328934059823237 4034978755749175136216857)
                ·
                  refine ⟨3026234066811881352162643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4034978755749175136216857 3026234066811881352162643)
                  ·
                    refine ⟨4539351100217822028243965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3026234066811881352162643 4539351100217822028243965)
                    ·
                      refine ⟨1702256662581683260591487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4539351100217822028243965 1702256662581683260591487)
                      ·
                        rfl

theorem cell23_3315133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_3315133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315133 prefixEnd_3315133 := by exact prefixLift 3315133
  have htrace : WordTrace (prefixWord ++ tailWord_3315133) baseStart_3315133 baseEnd_3315133 := by
    simpa [prefixWord, tailWord_3315133, baseEnd_3315133] using wordTrace_append hprefix tailTrace_3315133
  have hstable : (prefixWord ++ tailWord_3315133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315133).length < 2 ^ (prefixWord ++ tailWord_3315133).sum := by decide
  have hdescent : baseEnd_3315133 < baseStart_3315133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315150 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3]
def baseStart_3315150 : Nat := 118140960795 + 3315150 * 2 ^ 59
def prefixEnd_3315150 : Nat := 4983230072969 + 3 ^ 40 * 3315150 * 2
def baseEnd_3315150 : Nat := 1702265391752809694078909

theorem tailTrace_3315150 : CollatzResearch.WordTrace tailWord_3315150 prefixEnd_3315150 1702265391752809694078909 := by
  unfold tailWord_3315150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15114181742473150923626863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80608969293190138259343269 15114181742473150923626863)
  ·
    refine ⟨22671272613709726385440295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15114181742473150923626863 22671272613709726385440295)
    ·
      refine ⟨34006908920564589578160443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22671272613709726385440295 34006908920564589578160443)
      ·
        refine ⟨51010363380846884367240665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34006908920564589578160443 51010363380846884367240665)
        ·
          refine ⟨38257772535635163275430499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51010363380846884367240665 38257772535635163275430499)
          ·
            refine ⟨57386658803452744913145749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38257772535635163275430499 57386658803452744913145749)
            ·
              refine ⟨2689999631411847417803707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57386658803452744913145749 2689999631411847417803707)
              ·
                refine ⟨4034999447117771126705561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689999631411847417803707 4034999447117771126705561)
                ·
                  refine ⟨3026249585338328345029171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4034999447117771126705561 3026249585338328345029171)
                  ·
                    refine ⟨4539374378007492517543757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3026249585338328345029171 4539374378007492517543757)
                    ·
                      refine ⟨1702265391752809694078909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4539374378007492517543757 1702265391752809694078909)
                      ·
                        rfl

theorem cell23_3315150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_3315150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315150 prefixEnd_3315150 := by exact prefixLift 3315150
  have htrace : WordTrace (prefixWord ++ tailWord_3315150) baseStart_3315150 baseEnd_3315150 := by
    simpa [prefixWord, tailWord_3315150, baseEnd_3315150] using wordTrace_append hprefix tailTrace_3315150
  have hstable : (prefixWord ++ tailWord_3315150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315150).length < 2 ^ (prefixWord ++ tailWord_3315150).sum := by decide
  have hdescent : baseEnd_3315150 < baseStart_3315150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315173 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 3, 4, 2]
def baseStart_3315173 : Nat := 118140960795 + 3315173 * 2 ^ 59
def prefixEnd_3315173 : Nat := 4983230072969 + 3 ^ 40 * 3315173 * 2
def baseEnd_3315173 : Nat := 1702277201807863104091303

theorem tailTrace_3315173 : CollatzResearch.WordTrace tailWord_3315173 prefixEnd_3315173 1702277201807863104091303 := by
  unfold tailWord_3315173
  simp only [CollatzResearch.WordTrace]
  refine ⟨120914292818701882317102173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80609528545801254878068115 120914292818701882317102173)
  ·
    refine ⟨45342859807013205868913315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120914292818701882317102173 45342859807013205868913315)
    ·
      refine ⟨68014289710519808803369973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45342859807013205868913315 68014289710519808803369973)
      ·
        refine ⟨6376339660361232075315935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68014289710519808803369973 6376339660361232075315935)
        ·
          refine ⟨9564509490541848112973903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6376339660361232075315935 9564509490541848112973903)
          ·
            refine ⟨14346764235812772169460855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564509490541848112973903 14346764235812772169460855)
            ·
              refine ⟨21520146353719158254191283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14346764235812772169460855 21520146353719158254191283)
              ·
                refine ⟨32280219530578737381286925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21520146353719158254191283 32280219530578737381286925)
                ·
                  refine ⟨12105082323967026517982597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32280219530578737381286925 12105082323967026517982597)
                  ·
                    refine ⟨2269702935743817472121737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12105082323967026517982597 2269702935743817472121737)
                    ·
                      refine ⟨1702277201807863104091303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269702935743817472121737 1702277201807863104091303)
                      ·
                        rfl

theorem cell23_3315173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_3315173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315173 prefixEnd_3315173 := by exact prefixLift 3315173
  have htrace : WordTrace (prefixWord ++ tailWord_3315173) baseStart_3315173 baseEnd_3315173 := by
    simpa [prefixWord, tailWord_3315173, baseEnd_3315173] using wordTrace_append hprefix tailTrace_3315173
  have hstable : (prefixWord ++ tailWord_3315173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315173).length < 2 ^ (prefixWord ++ tailWord_3315173).sum := by decide
  have hdescent : baseEnd_3315173 < baseStart_3315173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315209 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 1, 7]
def baseStart_3315209 : Nat := 118140960795 + 3315209 * 2 ^ 59
def prefixEnd_3315209 : Nat := 4983230072969 + 3 ^ 40 * 3315209 * 2
def baseEnd_3315209 : Nat := 567431895703808321080379

theorem tailTrace_3315209 : CollatzResearch.WordTrace tailWord_3315209 prefixEnd_3315209 567431895703808321080379 := by
  unfold tailWord_3315209
  simp only [CollatzResearch.WordTrace]
  refine ⟨120915605846571460465412681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80610403897714306976941787 120915605846571460465412681)
  ·
    refine ⟨90686704384928595349059511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120915605846571460465412681 90686704384928595349059511)
    ·
      refine ⟨136030056577392893023589267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90686704384928595349059511 136030056577392893023589267)
      ·
        refine ⟨204045084866089339535383901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136030056577392893023589267 204045084866089339535383901)
        ·
          refine ⟨76516906824783502325768963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204045084866089339535383901 76516906824783502325768963)
          ·
            refine ⟨114775360237175253488653445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76516906824783502325768963 114775360237175253488653445)
            ·
              refine ⟨21520380044470360029122521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114775360237175253488653445 21520380044470360029122521)
              ·
                refine ⟨16140285033352770021841891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21520380044470360029122521 16140285033352770021841891)
                ·
                  refine ⟨24210427550029155032762837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16140285033352770021841891 24210427550029155032762837)
                  ·
                    refine ⟨567431895703808321080379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24210427550029155032762837 567431895703808321080379)
                    ·
                      rfl

theorem cell23_3315209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_3315209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315209 prefixEnd_3315209 := by exact prefixLift 3315209
  have htrace : WordTrace (prefixWord ++ tailWord_3315209) baseStart_3315209 baseEnd_3315209 := by
    simpa [prefixWord, tailWord_3315209, baseEnd_3315209] using wordTrace_append hprefix tailTrace_3315209
  have hstable : (prefixWord ++ tailWord_3315209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315209).length < 2 ^ (prefixWord ++ tailWord_3315209).sum := by decide
  have hdescent : baseEnd_3315209 < baseStart_3315209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315263 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 2, 4, 2]
def baseStart_3315263 : Nat := 118140960795 + 3315263 * 2 ^ 59
def prefixEnd_3315263 : Nat := 4983230072969 + 3 ^ 40 * 3315263 * 2
def baseEnd_3315263 : Nat := 1702323415066767751965889

theorem tailTrace_3315263 : CollatzResearch.WordTrace tailWord_3315263 prefixEnd_3315263 1702323415066767751965889 := by
  unfold tailWord_3315263
  simp only [CollatzResearch.WordTrace]
  refine ⟨120917575388375827687878443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80611716925583885125252295 120917575388375827687878443)
  ·
    refine ⟨181376363082563741531817665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120917575388375827687878443 181376363082563741531817665)
    ·
      refine ⟨136032272311922806148863249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181376363082563741531817665 136032272311922806148863249)
      ·
        refine ⟨102024204233942104611647437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136032272311922806148863249 102024204233942104611647437)
        ·
          refine ⟨38259076587728289229367789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102024204233942104611647437 38259076587728289229367789)
          ·
            refine ⟨14347153720398108461012921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38259076587728289229367789 14347153720398108461012921)
            ·
              refine ⟨10760365290298581345759691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14347153720398108461012921 10760365290298581345759691)
              ·
                refine ⟨16140547935447872018639537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10760365290298581345759691 16140547935447872018639537)
                ·
                  refine ⟨12105410951585904013979653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16140547935447872018639537 12105410951585904013979653)
                  ·
                    refine ⟨2269764553422357002621185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12105410951585904013979653 2269764553422357002621185)
                    ·
                      refine ⟨1702323415066767751965889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269764553422357002621185 1702323415066767751965889)
                      ·
                        rfl

theorem cell23_3315263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 4, 2].length) (baseStart_3315263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315263 prefixEnd_3315263 := by exact prefixLift 3315263
  have htrace : WordTrace (prefixWord ++ tailWord_3315263) baseStart_3315263 baseEnd_3315263 := by
    simpa [prefixWord, tailWord_3315263, baseEnd_3315263] using wordTrace_append hprefix tailTrace_3315263
  have hstable : (prefixWord ++ tailWord_3315263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315263).length < 2 ^ (prefixWord ++ tailWord_3315263).sum := by decide
  have hdescent : baseEnd_3315263 < baseStart_3315263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315323 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 4, 3, 2]
def baseStart_3315323 : Nat := 118140960795 + 3315323 * 2 ^ 59
def prefixEnd_3315323 : Nat := 4983230072969 + 3 ^ 40 * 3315323 * 2
def baseEnd_3315323 : Nat := 1702354223906037517215613

theorem tailTrace_3315323 : CollatzResearch.WordTrace tailWord_3315323 prefixEnd_3315323 1702354223906037517215613 := by
  unfold tailWord_3315323
  simp only [CollatzResearch.WordTrace]
  refine ⟨120919763768158457935062623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80613175845438971956708415 120919763768158457935062623)
  ·
    refine ⟨181379645652237686902593935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120919763768158457935062623 181379645652237686902593935)
    ·
      refine ⟨272069468478356530353890903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181379645652237686902593935 272069468478356530353890903)
      ·
        refine ⟨408104202717534795530836355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272069468478356530353890903 408104202717534795530836355)
        ·
          refine ⟨612156304076302193296254533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408104202717534795530836355 612156304076302193296254533)
          ·
            refine ⟨114779307014306661243047725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 612156304076302193296254533 114779307014306661243047725)
            ·
              refine ⟨43042240130364997966142897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114779307014306661243047725 43042240130364997966142897)
              ·
                refine ⟨32281680097773748474607173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43042240130364997966142897 32281680097773748474607173)
                ·
                  refine ⟨6052815018332577838988845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32281680097773748474607173 6052815018332577838988845)
                  ·
                    refine ⟨2269805631874716689620817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6052815018332577838988845 2269805631874716689620817)
                    ·
                      refine ⟨1702354223906037517215613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269805631874716689620817 1702354223906037517215613)
                      ·
                        rfl

theorem cell23_3315323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 3, 2].length) (baseStart_3315323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315323 prefixEnd_3315323 := by exact prefixLift 3315323
  have htrace : WordTrace (prefixWord ++ tailWord_3315323) baseStart_3315323 baseEnd_3315323 := by
    simpa [prefixWord, tailWord_3315323, baseEnd_3315323] using wordTrace_append hprefix tailTrace_3315323
  have hstable : (prefixWord ++ tailWord_3315323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315323).length < 2 ^ (prefixWord ++ tailWord_3315323).sum := by decide
  have hdescent : baseEnd_3315323 < baseStart_3315323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315340 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 2, 3, 2]
def baseStart_3315340 : Nat := 118140960795 + 3315340 * 2 ^ 59
def prefixEnd_3315340 : Nat := 4983230072969 + 3 ^ 40 * 3315340 * 2
def baseEnd_3315340 : Nat := 1702362953077163950703035

theorem tailTrace_3315340 : CollatzResearch.WordTrace tailWord_3315340 prefixEnd_3315340 1702362953077163950703035 := by
  unfold tailWord_3315340
  simp only [CollatzResearch.WordTrace]
  refine ⟨60460191904548434919215737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80613589206064579892287649 60460191904548434919215737)
  ·
    refine ⟨45345143928411326189411803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60460191904548434919215737 45345143928411326189411803)
    ·
      refine ⟨68017715892616989284117705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45345143928411326189411803 68017715892616989284117705)
      ·
        refine ⟨51013286919462741963088279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68017715892616989284117705 51013286919462741963088279)
        ·
          refine ⟨76519930379194112944632419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51013286919462741963088279 76519930379194112944632419)
          ·
            refine ⟨114779895568791169416948629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76519930379194112944632419 114779895568791169416948629)
            ·
              refine ⟨5380307604787086066419467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114779895568791169416948629 5380307604787086066419467)
              ·
                refine ⟨8070461407180629099629201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5380307604787086066419467 8070461407180629099629201)
                ·
                  refine ⟨6052846055385471824721901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8070461407180629099629201 6052846055385471824721901)
                  ·
                    refine ⟨2269817270769551934270713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6052846055385471824721901 2269817270769551934270713)
                    ·
                      refine ⟨1702362953077163950703035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269817270769551934270713 1702362953077163950703035)
                      ·
                        rfl

theorem cell23_3315340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_3315340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315340 prefixEnd_3315340 := by exact prefixLift 3315340
  have htrace : WordTrace (prefixWord ++ tailWord_3315340) baseStart_3315340 baseEnd_3315340 := by
    simpa [prefixWord, tailWord_3315340, baseEnd_3315340] using wordTrace_append hprefix tailTrace_3315340
  have hstable : (prefixWord ++ tailWord_3315340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315340).length < 2 ^ (prefixWord ++ tailWord_3315340).sum := by decide
  have hdescent : baseEnd_3315340 < baseStart_3315340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315364 : List Nat := [2, 3, 1, 2, 2, 2, 4, 2, 1, 1, 3]
def baseStart_3315364 : Nat := 118140960795 + 3315364 * 2 ^ 59
def prefixEnd_3315364 : Nat := 4983230072969 + 3 ^ 40 * 3315364 * 2
def baseEnd_3315364 : Nat := 1702375276612871856802925

theorem tailTrace_3315364 : CollatzResearch.WordTrace tailWord_3315364 prefixEnd_3315364 1702375276612871856802925 := by
  unfold tailWord_3315364
  simp only [CollatzResearch.WordTrace]
  refine ⟨60460629580504960968652573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80614172774006614624870097 60460629580504960968652573)
  ·
    refine ⟨22672736092689360363244715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60460629580504960968652573 22672736092689360363244715)
    ·
      refine ⟨34009104139034040544867073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22672736092689360363244715 34009104139034040544867073)
      ·
        refine ⟨25506828104275530408650305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34009104139034040544867073 25506828104275530408650305)
        ·
          refine ⟨19130121078206647806487729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25506828104275530408650305 19130121078206647806487729)
          ·
            refine ⟨14347590808654985854865797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19130121078206647806487729 14347590808654985854865797)
            ·
              refine ⟨2690173276622809847787337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14347590808654985854865797 2690173276622809847787337)
              ·
                refine ⟨2017629957467107385840503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690173276622809847787337 2017629957467107385840503)
                ·
                  refine ⟨3026444936200661078760755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017629957467107385840503 3026444936200661078760755)
                  ·
                    refine ⟨4539667404300991618141133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3026444936200661078760755 4539667404300991618141133)
                    ·
                      refine ⟨1702375276612871856802925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4539667404300991618141133 1702375276612871856802925)
                      ·
                        rfl

theorem cell23_3315364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_3315364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315364 prefixEnd_3315364 := by exact prefixLift 3315364
  have htrace : WordTrace (prefixWord ++ tailWord_3315364) baseStart_3315364 baseEnd_3315364 := by
    simpa [prefixWord, tailWord_3315364, baseEnd_3315364] using wordTrace_append hprefix tailTrace_3315364
  have hstable : (prefixWord ++ tailWord_3315364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315364).length < 2 ^ (prefixWord ++ tailWord_3315364).sum := by decide
  have hdescent : baseEnd_3315364 < baseStart_3315364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315373 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3315373 : Nat := 118140960795 + 3315373 * 2 ^ 59
def prefixEnd_3315373 : Nat := 4983230072969 + 3 ^ 40 * 3315373 * 2
def baseEnd_3315373 : Nat := 1702379897938762321590383

theorem tailTrace_3315373 : CollatzResearch.WordTrace tailWord_3315373 prefixEnd_3315373 1702379897938762321590383 := by
  unfold tailWord_3315373
  simp only [CollatzResearch.WordTrace]
  refine ⟨120921587417977316474382773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80614391611984877649588515 120921587417977316474382773)
  ·
    refine ⟨11336398820435373419473385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120921587417977316474382773 11336398820435373419473385)
    ·
      refine ⟨8502299115326530064605039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11336398820435373419473385 8502299115326530064605039)
      ·
        refine ⟨12753448672989795096907559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8502299115326530064605039 12753448672989795096907559)
        ·
          refine ⟨19130173009484692645361339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12753448672989795096907559 19130173009484692645361339)
          ·
            refine ⟨28695259514227038968042009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19130173009484692645361339 28695259514227038968042009)
            ·
              refine ⟨21521444635670279226031507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28695259514227038968042009 21521444635670279226031507)
              ·
                refine ⟨32282166953505418839047261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21521444635670279226031507 32282166953505418839047261)
                ·
                  refine ⟨12105812607564532064642723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32282166953505418839047261 12105812607564532064642723)
                  ·
                    refine ⟨18158718911346798096964085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12105812607564532064642723 18158718911346798096964085)
                    ·
                      refine ⟨1702379897938762321590383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18158718911346798096964085 1702379897938762321590383)
                      ·
                        rfl

theorem cell23_3315373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3315373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315373 prefixEnd_3315373 := by exact prefixLift 3315373
  have htrace : WordTrace (prefixWord ++ tailWord_3315373) baseStart_3315373 baseEnd_3315373 := by
    simpa [prefixWord, tailWord_3315373, baseEnd_3315373] using wordTrace_append hprefix tailTrace_3315373
  have hstable : (prefixWord ++ tailWord_3315373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315373).length < 2 ^ (prefixWord ++ tailWord_3315373).sum := by decide
  have hdescent : baseEnd_3315373 < baseStart_3315373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315376 : List Nat := [2, 1, 1, 1, 2, 1, 7, 8]
def baseStart_3315376 : Nat := 118140960795 + 3315376 * 2 ^ 59
def prefixEnd_3315376 : Nat := 4983230072969 + 3 ^ 40 * 3315376 * 2
def baseEnd_3315376 : Nat := 63051164384471326290847

theorem tailTrace_3315376 : CollatzResearch.WordTrace tailWord_3315376 prefixEnd_3315376 63051164384471326290847 := by
  unfold tailWord_3315376
  simp only [CollatzResearch.WordTrace]
  refine ⟨60460848418483223993370991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80614464557977631991161321 60460848418483223993370991)
  ·
    refine ⟨90691272627724835990056487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60460848418483223993370991 90691272627724835990056487)
    ·
      refine ⟨136036908941587253985084731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90691272627724835990056487 136036908941587253985084731)
      ·
        refine ⟨204055363412380880977627097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136036908941587253985084731 204055363412380880977627097)
        ·
          refine ⟨153041522559285660733220323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204055363412380880977627097 153041522559285660733220323)
          ·
            refine ⟨229562283838928491099830485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153041522559285660733220323 229562283838928491099830485)
            ·
              refine ⟨5380366027474886510152277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 229562283838928491099830485 5380366027474886510152277)
              ·
                refine ⟨63051164384471326290847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5380366027474886510152277 63051164384471326290847)
                ·
                  rfl

theorem cell23_3315376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 8].length) (baseStart_3315376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315376 prefixEnd_3315376 := by exact prefixLift 3315376
  have htrace : WordTrace (prefixWord ++ tailWord_3315376) baseStart_3315376 baseEnd_3315376 := by
    simpa [prefixWord, tailWord_3315376, baseEnd_3315376] using wordTrace_append hprefix tailTrace_3315376
  have hstable : (prefixWord ++ tailWord_3315376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315376).length < 2 ^ (prefixWord ++ tailWord_3315376).sum := by decide
  have hdescent : baseEnd_3315376 < baseStart_3315376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315383 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_3315383 : Nat := 118140960795 + 3315383 * 2 ^ 59
def prefixEnd_3315383 : Nat := 4983230072969 + 3 ^ 40 * 3315383 * 2
def baseEnd_3315383 : Nat := 1702385032745307282465337

theorem tailTrace_3315383 : CollatzResearch.WordTrace tailWord_3315383 prefixEnd_3315383 1702385032745307282465337 := by
  unfold tailWord_3315383
  simp only [CollatzResearch.WordTrace]
  refine ⟨120921952147941088182246803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80614634765294058788164535 120921952147941088182246803)
  ·
    refine ⟨181382928221911632273370205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120921952147941088182246803 181382928221911632273370205)
    ·
      refine ⟨68018598083216862102513827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181382928221911632273370205 68018598083216862102513827)
      ·
        refine ⟨102027897124825293153770741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68018598083216862102513827 102027897124825293153770741)
        ·
          refine ⟨9565115355452371233166007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102027897124825293153770741 9565115355452371233166007)
          ·
            refine ⟨14347673033178556849749011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9565115355452371233166007 14347673033178556849749011)
            ·
              refine ⟨21521509549767835274623517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14347673033178556849749011 21521509549767835274623517)
              ·
                refine ⟨8070566081162938227983819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21521509549767835274623517 8070566081162938227983819)
                ·
                  refine ⟨12105849121744407341975729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8070566081162938227983819 12105849121744407341975729)
                  ·
                    refine ⟨9079386841308305506481797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12105849121744407341975729 9079386841308305506481797)
                    ·
                      refine ⟨1702385032745307282465337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9079386841308305506481797 1702385032745307282465337)
                      ·
                        rfl

theorem cell23_3315383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_3315383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315383 prefixEnd_3315383 := by exact prefixLift 3315383
  have htrace : WordTrace (prefixWord ++ tailWord_3315383) baseStart_3315383 baseEnd_3315383 := by
    simpa [prefixWord, tailWord_3315383, baseEnd_3315383] using wordTrace_append hprefix tailTrace_3315383
  have hstable : (prefixWord ++ tailWord_3315383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315383).length < 2 ^ (prefixWord ++ tailWord_3315383).sum := by decide
  have hdescent : baseEnd_3315383 < baseStart_3315383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315390 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_3315390 : Nat := 118140960795 + 3315390 * 2 ^ 59
def prefixEnd_3315390 : Nat := 4983230072969 + 3 ^ 40 * 3315390 * 2
def baseEnd_3315390 : Nat := 1702388627109888755077805

theorem tailTrace_3315390 : CollatzResearch.WordTrace tailWord_3315390 prefixEnd_3315390 1702388627109888755077805 := by
  unfold tailWord_3315390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15115275932364466047218953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80614804972610485585167749 15115275932364466047218953)
  ·
    refine ⟨11336456949273349535414215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15115275932364466047218953 11336456949273349535414215)
    ·
      refine ⟨17004685423910024303121323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11336456949273349535414215 17004685423910024303121323)
      ·
        refine ⟨25507028135865036454681985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17004685423910024303121323 25507028135865036454681985)
        ·
          refine ⟨19130271101898777341011489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25507028135865036454681985 19130271101898777341011489)
          ·
            refine ⟨14347703326424083005758617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19130271101898777341011489 14347703326424083005758617)
            ·
              refine ⟨10760777494818062254318963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14347703326424083005758617 10760777494818062254318963)
              ·
                refine ⟨16141166242227093381478445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10760777494818062254318963 16141166242227093381478445)
                ·
                  refine ⟨6052937340835160018054417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16141166242227093381478445 6052937340835160018054417)
                  ·
                    refine ⟨4539703005626370013540813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6052937340835160018054417 4539703005626370013540813)
                    ·
                      refine ⟨1702388627109888755077805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4539703005626370013540813 1702388627109888755077805)
                      ·
                        rfl

theorem cell23_3315390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_3315390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315390 prefixEnd_3315390 := by exact prefixLift 3315390
  have htrace : WordTrace (prefixWord ++ tailWord_3315390) baseStart_3315390 baseEnd_3315390 := by
    simpa [prefixWord, tailWord_3315390, baseEnd_3315390] using wordTrace_append hprefix tailTrace_3315390
  have hstable : (prefixWord ++ tailWord_3315390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315390).length < 2 ^ (prefixWord ++ tailWord_3315390).sum := by decide
  have hdescent : baseEnd_3315390 < baseStart_3315390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315398 : List Nat := [6, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_3315398 : Nat := 118140960795 + 3315398 * 2 ^ 59
def prefixEnd_3315398 : Nat := 4983230072969 + 3 ^ 40 * 3315398 * 2
def baseEnd_3315398 : Nat := 1702392734955124723777769

theorem tailTrace_3315398 : CollatzResearch.WordTrace tailWord_3315398 prefixEnd_3315398 1702392734955124723777769 := by
  unfold tailWord_3315398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778828101340210804501339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80614999495257830496028565 3778828101340210804501339)
  ·
    refine ⟨5668242152010316206752009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3778828101340210804501339 5668242152010316206752009)
    ·
      refine ⟨4251181614007737155064007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5668242152010316206752009 4251181614007737155064007)
      ·
        refine ⟨6376772421011605732596011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4251181614007737155064007 6376772421011605732596011)
        ·
          refine ⟨9565158631517408598894017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6376772421011605732596011 9565158631517408598894017)
          ·
            refine ⟨7173868973638056449170513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9565158631517408598894017 7173868973638056449170513)
            ·
              refine ⟨5380401730228542336877885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7173868973638056449170513 5380401730228542336877885)
              ·
                refine ⟨2017650648835703376329207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5380401730228542336877885 2017650648835703376329207)
                ·
                  refine ⟨3026475973253555064493811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017650648835703376329207 3026475973253555064493811)
                  ·
                    refine ⟨4539713959880332596740717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3026475973253555064493811 4539713959880332596740717)
                    ·
                      refine ⟨1702392734955124723777769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4539713959880332596740717 1702392734955124723777769)
                      ·
                        rfl

theorem cell23_3315398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_3315398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315398 prefixEnd_3315398 := by exact prefixLift 3315398
  have htrace : WordTrace (prefixWord ++ tailWord_3315398) baseStart_3315398 baseEnd_3315398 := by
    simpa [prefixWord, tailWord_3315398, baseEnd_3315398] using wordTrace_append hprefix tailTrace_3315398
  have hstable : (prefixWord ++ tailWord_3315398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315398).length < 2 ^ (prefixWord ++ tailWord_3315398).sum := by decide
  have hdescent : baseEnd_3315398 < baseStart_3315398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315404 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3315404 : Nat := 118140960795 + 3315404 * 2 ^ 59
def prefixEnd_3315404 : Nat := 4983230072969 + 3 ^ 40 * 3315404 * 2
def baseEnd_3315404 : Nat := 1702395815839051700302741

theorem tailTrace_3315404 : CollatzResearch.WordTrace tailWord_3315404 prefixEnd_3315404 1702395815839051700302741 := by
  unfold tailWord_3315404
  simp only [CollatzResearch.WordTrace]
  refine ⟨60461359040432504384380633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80615145387243339179174177 60461359040432504384380633)
  ·
    refine ⟨45346019280324378288285475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60461359040432504384380633 45346019280324378288285475)
    ·
      refine ⟨68019028920486567432428213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45346019280324378288285475 68019028920486567432428213)
      ·
        refine ⟨6376783961295615696790145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68019028920486567432428213 6376783961295615696790145)
        ·
          refine ⟨4782587970971711772592609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6376783961295615696790145 4782587970971711772592609)
          ·
            refine ⟨3586940978228783829444457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4782587970971711772592609 3586940978228783829444457)
            ·
              refine ⟨2690205733671587872083343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586940978228783829444457 2690205733671587872083343)
              ·
                refine ⟨4035308600507381808125015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2690205733671587872083343 4035308600507381808125015)
                ·
                  refine ⟨6052962900761072712187523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035308600507381808125015 6052962900761072712187523)
                  ·
                    refine ⟨9079444351141609068281285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6052962900761072712187523 9079444351141609068281285)
                    ·
                      refine ⟨1702395815839051700302741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9079444351141609068281285 1702395815839051700302741)
                      ·
                        rfl

theorem cell23_3315404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3315404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315404 prefixEnd_3315404 := by exact prefixLift 3315404
  have htrace : WordTrace (prefixWord ++ tailWord_3315404) baseStart_3315404 baseEnd_3315404 := by
    simpa [prefixWord, tailWord_3315404, baseEnd_3315404] using wordTrace_append hprefix tailTrace_3315404
  have hstable : (prefixWord ++ tailWord_3315404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315404).length < 2 ^ (prefixWord ++ tailWord_3315404).sum := by decide
  have hdescent : baseEnd_3315404 < baseStart_3315404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315414 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_3315414 : Nat := 118140960795 + 3315414 * 2 ^ 59
def prefixEnd_3315414 : Nat := 4983230072969 + 3 ^ 40 * 3315414 * 2
def baseEnd_3315414 : Nat := 567466983548532220392565

theorem tailTrace_3315414 : CollatzResearch.WordTrace tailWord_3315414 prefixEnd_3315414 567466983548532220392565 := by
  unfold tailWord_3315414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7557692675676798779789081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80615388540552520317750197 7557692675676798779789081)
  ·
    refine ⟨5668269506757599084841811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7557692675676798779789081 5668269506757599084841811)
    ·
      refine ⟨8502404260136398627262717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5668269506757599084841811 8502404260136398627262717)
      ·
        refine ⟨3188401597551149485223519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8502404260136398627262717 3188401597551149485223519)
        ·
          refine ⟨4782602396326724227835279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188401597551149485223519 4782602396326724227835279)
          ·
            refine ⟨7173903594490086341752919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782602396326724227835279 7173903594490086341752919)
            ·
              refine ⟨10760855391735129512629379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173903594490086341752919 10760855391735129512629379)
              ·
                refine ⟨16141283087602694268944069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10760855391735129512629379 16141283087602694268944069)
                ·
                  refine ⟨3026490578925505175427013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16141283087602694268944069 3026490578925505175427013)
                  ·
                    refine ⟨567466983548532220392565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3026490578925505175427013 567466983548532220392565)
                    ·
                      rfl

theorem cell23_3315414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_3315414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315414 prefixEnd_3315414 := by exact prefixLift 3315414
  have htrace : WordTrace (prefixWord ++ tailWord_3315414) baseStart_3315414 baseEnd_3315414 := by
    simpa [prefixWord, tailWord_3315414, baseEnd_3315414] using wordTrace_append hprefix tailTrace_3315414
  have hstable : (prefixWord ++ tailWord_3315414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315414).length < 2 ^ (prefixWord ++ tailWord_3315414).sum := by decide
  have hdescent : baseEnd_3315414 < baseStart_3315414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315421 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_3315421 : Nat := 118140960795 + 3315421 * 2 ^ 59
def prefixEnd_3315421 : Nat := 4983230072969 + 3 ^ 40 * 3315421 * 2
def baseEnd_3315421 : Nat := 1702404545010178133790163

theorem tailTrace_3315421 : CollatzResearch.WordTrace tailWord_3315421 prefixEnd_3315421 1702404545010178133790163 := by
  unfold tailWord_3315421
  simp only [CollatzResearch.WordTrace]
  refine ⟨120923338121803420672130117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80615558747868947114753411 120923338121803420672130117)
  ·
    refine ⟨22673125897838141376024397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120923338121803420672130117 22673125897838141376024397)
    ·
      refine ⟨8502422211689303016009149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22673125897838141376024397 8502422211689303016009149)
      ·
        refine ⟨3188408329383488631003431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8502422211689303016009149 3188408329383488631003431)
        ·
          refine ⟨4782612494075232946505147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188408329383488631003431 4782612494075232946505147)
          ·
            refine ⟨7173918741112849419757721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782612494075232946505147 7173918741112849419757721)
            ·
              refine ⟨5380439055834637064818291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7173918741112849419757721 5380439055834637064818291)
              ·
                refine ⟨8070658583751955597227437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5380439055834637064818291 8070658583751955597227437)
                ·
                  refine ⟨3026496968906983348960289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8070658583751955597227437 3026496968906983348960289)
                  ·
                    refine ⟨2269872726680237511720217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3026496968906983348960289 2269872726680237511720217)
                    ·
                      refine ⟨1702404545010178133790163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269872726680237511720217 1702404545010178133790163)
                      ·
                        rfl

theorem cell23_3315421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_3315421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315421 prefixEnd_3315421 := by exact prefixLift 3315421
  have htrace : WordTrace (prefixWord ++ tailWord_3315421) baseStart_3315421 baseEnd_3315421 := by
    simpa [prefixWord, tailWord_3315421, baseEnd_3315421] using wordTrace_append hprefix tailTrace_3315421
  have hstable : (prefixWord ++ tailWord_3315421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315421).length < 2 ^ (prefixWord ++ tailWord_3315421).sum := by decide
  have hdescent : baseEnd_3315421 < baseStart_3315421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315437 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3315437 : Nat := 118140960795 + 3315437 * 2 ^ 59
def prefixEnd_3315437 : Nat := 4983230072969 + 3 ^ 40 * 3315437 * 2
def baseEnd_3315437 : Nat := 1702412760700650071190089

theorem tailTrace_3315437 : CollatzResearch.WordTrace tailWord_3315437 prefixEnd_3315437 1702412760700650071190089 := by
  unfold tailWord_3315437
  simp only [CollatzResearch.WordTrace]
  refine ⟨120923921689745455404712565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80615947793163636936475043 120923921689745455404712565)
  ·
    refine ⟨11336617658413636444191803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120923921689745455404712565 11336617658413636444191803)
    ·
      refine ⟨17004926487620454666287705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11336617658413636444191803 17004926487620454666287705)
      ·
        refine ⟨12753694865715340999715779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17004926487620454666287705 12753694865715340999715779)
        ·
          refine ⟨19130542298573011499573669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12753694865715340999715779 19130542298573011499573669)
          ·
            refine ⟨3586976680982439656170063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19130542298573011499573669 3586976680982439656170063)
            ·
              refine ⟨5380465021473659484255095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586976680982439656170063 5380465021473659484255095)
              ·
                refine ⟨8070697532210489226382643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5380465021473659484255095 8070697532210489226382643)
                ·
                  refine ⟨12106046298315733839573965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8070697532210489226382643 12106046298315733839573965)
                  ·
                    refine ⟨4539767361868400189840237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12106046298315733839573965 4539767361868400189840237)
                    ·
                      refine ⟨1702412760700650071190089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4539767361868400189840237 1702412760700650071190089)
                      ·
                        rfl

theorem cell23_3315437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3315437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315437 prefixEnd_3315437 := by exact prefixLift 3315437
  have htrace : WordTrace (prefixWord ++ tailWord_3315437) baseStart_3315437 baseEnd_3315437 := by
    simpa [prefixWord, tailWord_3315437, baseEnd_3315437] using wordTrace_append hprefix tailTrace_3315437
  have hstable : (prefixWord ++ tailWord_3315437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315437).length < 2 ^ (prefixWord ++ tailWord_3315437).sum := by decide
  have hdescent : baseEnd_3315437 < baseStart_3315437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315444 : List Nat := [2, 6, 1, 1, 1, 3, 2, 7]
def baseStart_3315444 : Nat := 118140960795 + 3315444 * 2 ^ 59
def prefixEnd_3315444 : Nat := 4983230072969 + 3 ^ 40 * 3315444 * 2
def baseEnd_3315444 : Nat := 63052457595008575696391

theorem tailTrace_3315444 : CollatzResearch.WordTrace tailWord_3315444 prefixEnd_3315444 63052457595008575696391 := by
  unfold tailWord_3315444
  simp only [CollatzResearch.WordTrace]
  refine ⟨60462088500360047800108693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80616118000480063733478257 60462088500360047800108693)
  ·
    refine ⟨2834160398454377240630095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60462088500360047800108693 2834160398454377240630095)
    ·
      refine ⟨4251240597681565860945143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2834160398454377240630095 4251240597681565860945143)
      ·
        refine ⟨6376860896522348791417715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4251240597681565860945143 6376860896522348791417715)
        ·
          refine ⟨9565291344783523187126573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6376860896522348791417715 9565291344783523187126573)
          ·
            refine ⟨3586984254293821195172465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9565291344783523187126573 3586984254293821195172465)
            ·
              refine ⟨2690238190720365896379349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586984254293821195172465 2690238190720365896379349)
              ·
                refine ⟨63052457595008575696391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2690238190720365896379349 63052457595008575696391)
                ·
                  rfl

theorem cell23_3315444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 7].length) (baseStart_3315444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315444 prefixEnd_3315444 := by exact prefixLift 3315444
  have htrace : WordTrace (prefixWord ++ tailWord_3315444) baseStart_3315444 baseEnd_3315444 := by
    simpa [prefixWord, tailWord_3315444, baseEnd_3315444] using wordTrace_append hprefix tailTrace_3315444
  have hstable : (prefixWord ++ tailWord_3315444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315444).length < 2 ^ (prefixWord ++ tailWord_3315444).sum := by decide
  have hdescent : baseEnd_3315444 < baseStart_3315444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315477 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 4, 2, 2]
def baseStart_3315477 : Nat := 118140960795 + 3315477 * 2 ^ 59
def prefixEnd_3315477 : Nat := 4983230072969 + 3 ^ 40 * 3315477 * 2
def baseEnd_3315477 : Nat := 1702433299926829914689905

theorem tailTrace_3315477 : CollatzResearch.WordTrace tailWord_3315477 prefixEnd_3315477 1702433299926829914689905 := by
  unfold tailWord_3315477
  simp only [CollatzResearch.WordTrace]
  refine ⟨120925380609600542236168685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80616920406400361490779123 120925380609600542236168685)
  ·
    refine ⟨45347017728600203338563257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120925380609600542236168685 45347017728600203338563257)
    ·
      refine ⟨34010263296450152503922443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45347017728600203338563257 34010263296450152503922443)
      ·
        refine ⟨51015394944675228755883665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34010263296450152503922443 51015394944675228755883665)
        ·
          refine ⟨38261546208506421566912749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51015394944675228755883665 38261546208506421566912749)
          ·
            refine ⟨14348079828189908087592281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38261546208506421566912749 14348079828189908087592281)
            ·
              refine ⟨10761059871142431065694211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14348079828189908087592281 10761059871142431065694211)
              ·
                refine ⟨16141589806713646598541317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10761059871142431065694211 16141589806713646598541317)
                ·
                  refine ⟨3026548088758808737226497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16141589806713646598541317 3026548088758808737226497)
                  ·
                    refine ⟨2269911066569106552919873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3026548088758808737226497 2269911066569106552919873)
                    ·
                      refine ⟨1702433299926829914689905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2269911066569106552919873 1702433299926829914689905)
                      ·
                        rfl

theorem cell23_3315477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_3315477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315477 prefixEnd_3315477 := by exact prefixLift 3315477
  have htrace : WordTrace (prefixWord ++ tailWord_3315477) baseStart_3315477 baseEnd_3315477 := by
    simpa [prefixWord, tailWord_3315477, baseEnd_3315477] using wordTrace_append hprefix tailTrace_3315477
  have hstable : (prefixWord ++ tailWord_3315477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315477).length < 2 ^ (prefixWord ++ tailWord_3315477).sum := by decide
  have hdescent : baseEnd_3315477 < baseStart_3315477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315523 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 5]
def baseStart_3315523 : Nat := 118140960795 + 3315523 * 2 ^ 59
def prefixEnd_3315523 : Nat := 4983230072969 + 3 ^ 40 * 3315523 * 2
def baseEnd_3315523 : Nat := 1702456920036936734714693

theorem tailTrace_3315523 : CollatzResearch.WordTrace tailWord_3315523 prefixEnd_3315523 1702456920036936734714693 := by
  unfold tailWord_3315523
  simp only [CollatzResearch.WordTrace]
  refine ⟨120927058367433892092343223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80618038911622594728228815 120927058367433892092343223)
  ·
    refine ⟨181390587551150838138514835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120927058367433892092343223 181390587551150838138514835)
    ·
      refine ⟨272085881326726257207772253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181390587551150838138514835 272085881326726257207772253)
      ·
        refine ⟨102032205497522346452914595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272085881326726257207772253 102032205497522346452914595)
        ·
          refine ⟨153048308246283519679371893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102032205497522346452914595 153048308246283519679371893)
          ·
            refine ⟨14348278898089079969941115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153048308246283519679371893 14348278898089079969941115)
            ·
              refine ⟨21522418347133619954911673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14348278898089079969941115 21522418347133619954911673)
              ·
                refine ⟨16141813760350214966183755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21522418347133619954911673 16141813760350214966183755)
                ·
                  refine ⟨24212720640525322449275633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16141813760350214966183755 24212720640525322449275633)
                  ·
                    refine ⟨18159540480393991836956725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24212720640525322449275633 18159540480393991836956725)
                    ·
                      refine ⟨1702456920036936734714693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18159540480393991836956725 1702456920036936734714693)
                      ·
                        rfl

theorem cell23_3315523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_3315523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315523 prefixEnd_3315523 := by exact prefixLift 3315523
  have htrace : WordTrace (prefixWord ++ tailWord_3315523) baseStart_3315523 baseEnd_3315523 := by
    simpa [prefixWord, tailWord_3315523, baseEnd_3315523] using wordTrace_append hprefix tailTrace_3315523
  have hstable : (prefixWord ++ tailWord_3315523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315523).length < 2 ^ (prefixWord ++ tailWord_3315523).sum := by decide
  have hdescent : baseEnd_3315523 < baseStart_3315523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315540 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_3315540 : Nat := 118140960795 + 3315540 * 2 ^ 59
def prefixEnd_3315540 : Nat := 4983230072969 + 3 ^ 40 * 3315540 * 2
def baseEnd_3315540 : Nat := 1702465649208063168202115

theorem tailTrace_3315540 : CollatzResearch.WordTrace tailWord_3315540 prefixEnd_3315540 1702465649208063168202115 := by
  unfold tailWord_3315540
  simp only [CollatzResearch.WordTrace]
  refine ⟨60463839204186151997856037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80618452272248202663808049 60463839204186151997856037)
  ·
    refine ⟨11336969850784903499598007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60463839204186151997856037 11336969850784903499598007)
    ·
      refine ⟨17005454776177355249397011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11336969850784903499598007 17005454776177355249397011)
      ·
        refine ⟨25508182164266032874095517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17005454776177355249397011 25508182164266032874095517)
        ·
          refine ⟨9565568311599762327785819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25508182164266032874095517 9565568311599762327785819)
          ·
            refine ⟨14348352467399643491678729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9565568311599762327785819 14348352467399643491678729)
            ·
              refine ⟨10761264350549732618759047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14348352467399643491678729 10761264350549732618759047)
              ·
                refine ⟨16141896525824598928138571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10761264350549732618759047 16141896525824598928138571)
                ·
                  refine ⟨24212844788736898392207857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16141896525824598928138571 24212844788736898392207857)
                  ·
                    refine ⟨18159633591552673794155893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24212844788736898392207857 18159633591552673794155893)
                    ·
                      refine ⟨1702465649208063168202115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18159633591552673794155893 1702465649208063168202115)
                      ·
                        rfl

theorem cell23_3315540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_3315540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315540 prefixEnd_3315540 := by exact prefixLift 3315540
  have htrace : WordTrace (prefixWord ++ tailWord_3315540) baseStart_3315540 baseEnd_3315540 := by
    simpa [prefixWord, tailWord_3315540, baseEnd_3315540] using wordTrace_append hprefix tailTrace_3315540
  have hstable : (prefixWord ++ tailWord_3315540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315540).length < 2 ^ (prefixWord ++ tailWord_3315540).sum := by decide
  have hdescent : baseEnd_3315540 < baseStart_3315540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315593 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_3315593 : Nat := 118140960795 + 3315593 * 2 ^ 59
def prefixEnd_3315593 : Nat := 4983230072969 + 3 ^ 40 * 3315593 * 2
def baseEnd_3315593 : Nat := 1702492863682751460839371

theorem tailTrace_3315593 : CollatzResearch.WordTrace tailWord_3315593 prefixEnd_3315593 1702492863682751460839371 := by
  unfold tailWord_3315593
  simp only [CollatzResearch.WordTrace]
  refine ⟨120929611477180294047391433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80619740984786862698260955 120929611477180294047391433)
  ·
    refine ⟨90697208607885220535543575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120929611477180294047391433 90697208607885220535543575)
    ·
      refine ⟨136045812911827830803315363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90697208607885220535543575 136045812911827830803315363)
      ·
        refine ⟨204068719367741746204973045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136045812911827830803315363 204068719367741746204973045)
        ·
          refine ⟨19131442440725788706716223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204068719367741746204973045 19131442440725788706716223)
          ·
            refine ⟨28697163661088683060074335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19131442440725788706716223 28697163661088683060074335)
            ·
              refine ⟨43045745491633024590111503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28697163661088683060074335 43045745491633024590111503)
              ·
                refine ⟨64568618237449536885167255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43045745491633024590111503 64568618237449536885167255)
                ·
                  refine ⟨96852927356174305327750883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64568618237449536885167255 96852927356174305327750883)
                  ·
                    refine ⟨145279391034261457991626325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96852927356174305327750883 145279391034261457991626325)
                    ·
                      refine ⟨1702492863682751460839371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 145279391034261457991626325 1702492863682751460839371)
                      ·
                        rfl

theorem cell23_3315593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_3315593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315593 prefixEnd_3315593 := by exact prefixLift 3315593
  have htrace : WordTrace (prefixWord ++ tailWord_3315593) baseStart_3315593 baseEnd_3315593 := by
    simpa [prefixWord, tailWord_3315593, baseEnd_3315593] using wordTrace_append hprefix tailTrace_3315593
  have hstable : (prefixWord ++ tailWord_3315593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315593).length < 2 ^ (prefixWord ++ tailWord_3315593).sum := by decide
  have hdescent : baseEnd_3315593 < baseStart_3315593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315594 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 3, 4]
def baseStart_3315594 : Nat := 118140960795 + 3315594 * 2 ^ 59
def prefixEnd_3315594 : Nat := 4983230072969 + 3 ^ 40 * 3315594 * 2
def baseEnd_3315594 : Nat := 567497792387801985642289

theorem tailTrace_3315594 : CollatzResearch.WordTrace tailWord_3315594 prefixEnd_3315594 567497792387801985642289 := by
  unfold tailWord_3315594
  simp only [CollatzResearch.WordTrace]
  refine ⟨30232411987544167804544459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80619765300117780812118557 30232411987544167804544459)
  ·
    refine ⟨45348617981316251706816689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30232411987544167804544459 45348617981316251706816689)
    ·
      refine ⟨34011463485987188780112517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45348617981316251706816689 34011463485987188780112517)
      ·
        refine ⟨6377149403622597896271097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34011463485987188780112517 6377149403622597896271097)
        ·
          refine ⟨4782862052716948422203323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6377149403622597896271097 4782862052716948422203323)
          ·
            refine ⟨7174293079075422633304985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782862052716948422203323 7174293079075422633304985)
            ·
              refine ⟨5380719809306566974978739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7174293079075422633304985 5380719809306566974978739)
              ·
                refine ⟨8071079713959850462468109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5380719809306566974978739 8071079713959850462468109)
                ·
                  refine ⟨3026654892734943923425541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8071079713959850462468109 3026654892734943923425541)
                  ·
                    refine ⟨567497792387801985642289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3026654892734943923425541 567497792387801985642289)
                    ·
                      rfl

theorem cell23_3315594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_3315594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315594 prefixEnd_3315594 := by exact prefixLift 3315594
  have htrace : WordTrace (prefixWord ++ tailWord_3315594) baseStart_3315594 baseEnd_3315594 := by
    simpa [prefixWord, tailWord_3315594, baseEnd_3315594] using wordTrace_append hprefix tailTrace_3315594
  have hstable : (prefixWord ++ tailWord_3315594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315594).length < 2 ^ (prefixWord ++ tailWord_3315594).sum := by decide
  have hdescent : baseEnd_3315594 < baseStart_3315594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315607 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 6]
def baseStart_3315607 : Nat := 118140960795 + 3315607 * 2 ^ 59
def prefixEnd_3315607 : Nat := 4983230072969 + 3 ^ 40 * 3315607 * 2
def baseEnd_3315607 : Nat := 189166672490212711784923

theorem tailTrace_3315607 : CollatzResearch.WordTrace tailWord_3315607 prefixEnd_3315607 189166672490212711784923 := by
  unfold tailWord_3315607
  simp only [CollatzResearch.WordTrace]
  refine ⟨120930122099129574438401075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80620081399419716292267383 120930122099129574438401075)
  ·
    refine ⟨181395183148694361657601613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120930122099129574438401075 181395183148694361657601613)
    ·
      refine ⟨68023193680760385621600605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181395183148694361657601613 68023193680760385621600605)
      ·
        refine ⟨25508697630285144608100227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68023193680760385621600605 25508697630285144608100227)
        ·
          refine ⟨38263046445427716912150341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25508697630285144608100227 38263046445427716912150341)
          ·
            refine ⟨7174321208517696921028189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38263046445427716912150341 7174321208517696921028189)
            ·
              refine ⟨2690370453194136345385571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7174321208517696921028189 2690370453194136345385571)
              ·
                refine ⟨4035555679791204518078357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2690370453194136345385571 4035555679791204518078357)
                ·
                  refine ⟨189166672490212711784923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4035555679791204518078357 189166672490212711784923)
                  ·
                    rfl

theorem cell23_3315607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 6].length) (baseStart_3315607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315607 prefixEnd_3315607 := by exact prefixLift 3315607
  have htrace : WordTrace (prefixWord ++ tailWord_3315607) baseStart_3315607 baseEnd_3315607 := by
    simpa [prefixWord, tailWord_3315607, baseEnd_3315607] using wordTrace_append hprefix tailTrace_3315607
  have hstable : (prefixWord ++ tailWord_3315607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315607).length < 2 ^ (prefixWord ++ tailWord_3315607).sum := by decide
  have hdescent : baseEnd_3315607 < baseStart_3315607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315637 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 1, 5]
def baseStart_3315637 : Nat := 118140960795 + 3315637 * 2 ^ 59
def prefixEnd_3315637 : Nat := 4983230072969 + 3 ^ 40 * 3315637 * 2
def baseEnd_3315637 : Nat := 567505152277183096229723

theorem tailTrace_3315637 : CollatzResearch.WordTrace tailWord_3315637 prefixEnd_3315637 567505152277183096229723 := by
  unfold tailWord_3315637
  simp only [CollatzResearch.WordTrace]
  refine ⟨120931216289020889561993165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80620810859347259707995443 120931216289020889561993165)
  ·
    refine ⟨45349206108382833585747437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120931216289020889561993165 45349206108382833585747437)
    ·
      refine ⟨17005952290643562594655289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45349206108382833585747437 17005952290643562594655289)
      ·
        refine ⟨12754464217982671945991467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17005952290643562594655289 12754464217982671945991467)
        ·
          refine ⟨19131696326974007918987201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12754464217982671945991467 19131696326974007918987201)
          ·
            refine ⟨14348772245230505939240401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19131696326974007918987201 14348772245230505939240401)
            ·
              refine ⟨10761579183922879454430301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14348772245230505939240401 10761579183922879454430301)
              ·
                refine ⟨4035592193971079795411363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10761579183922879454430301 4035592193971079795411363)
                ·
                  refine ⟨6053388290956619693117045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035592193971079795411363 6053388290956619693117045)
                  ·
                    refine ⟨567505152277183096229723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6053388290956619693117045 567505152277183096229723)
                    ·
                      rfl

theorem cell23_3315637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_3315637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315637 prefixEnd_3315637 := by exact prefixLift 3315637
  have htrace : WordTrace (prefixWord ++ tailWord_3315637) baseStart_3315637 baseEnd_3315637 := by
    simpa [prefixWord, tailWord_3315637, baseEnd_3315637] using wordTrace_append hprefix tailTrace_3315637
  have hstable : (prefixWord ++ tailWord_3315637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315637).length < 2 ^ (prefixWord ++ tailWord_3315637).sum := by decide
  have hdescent : baseEnd_3315637 < baseStart_3315637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315694 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_3315694 : Nat := 118140960795 + 3315694 * 2 ^ 59
def prefixEnd_3315694 : Nat := 4983230072969 + 3 ^ 40 * 3315694 * 2
def baseEnd_3315694 : Nat := 1702544725228855565676407

theorem tailTrace_3315694 : CollatzResearch.WordTrace tailWord_3315694 prefixEnd_3315694 1702544725228855565676407 := by
  unfold tailWord_3315694
  simp only [CollatzResearch.WordTrace]
  refine ⟨15116661906226798537102267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80622196833209592197878757 15116661906226798537102267)
  ·
    refine ⟨22674992859340197805653401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15116661906226798537102267 22674992859340197805653401)
    ·
      refine ⟨17006244644505148354240051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22674992859340197805653401 17006244644505148354240051)
      ·
        refine ⟨25509366966757722531360077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17006244644505148354240051 25509366966757722531360077)
        ·
          refine ⟨9566012612534145949260029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25509366966757722531360077 9566012612534145949260029)
          ·
            refine ⟨3587254729700304730972511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9566012612534145949260029 3587254729700304730972511)
            ·
              refine ⟨5380882094550457096458767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587254729700304730972511 5380882094550457096458767)
              ·
                refine ⟨8071323141825685644688151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5380882094550457096458767 8071323141825685644688151)
                ·
                  refine ⟨12106984712738528467032227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8071323141825685644688151 12106984712738528467032227)
                  ·
                    refine ⟨18160477069107792700548341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12106984712738528467032227 18160477069107792700548341)
                    ·
                      refine ⟨1702544725228855565676407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18160477069107792700548341 1702544725228855565676407)
                      ·
                        rfl

theorem cell23_3315694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_3315694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315694 prefixEnd_3315694 := by exact prefixLift 3315694
  have htrace : WordTrace (prefixWord ++ tailWord_3315694) baseStart_3315694 baseEnd_3315694 := by
    simpa [prefixWord, tailWord_3315694, baseEnd_3315694] using wordTrace_append hprefix tailTrace_3315694
  have hstable : (prefixWord ++ tailWord_3315694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315694).length < 2 ^ (prefixWord ++ tailWord_3315694).sum := by decide
  have hdescent : baseEnd_3315694 < baseStart_3315694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315702 : List Nat := [5, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_3315702 : Nat := 118140960795 + 3315702 * 2 ^ 59
def prefixEnd_3315702 : Nat := 4983230072969 + 3 ^ 40 * 3315702 * 2
def baseEnd_3315702 : Nat := 1702548833074091534376371

theorem tailTrace_3315702 : CollatzResearch.WordTrace tailWord_3315702 prefixEnd_3315702 1702548833074091534376371 := by
  unfold tailWord_3315702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7558349189611587853944335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80622391355856937108739573 7558349189611587853944335)
  ·
    refine ⟨11337523784417381780916503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7558349189611587853944335 11337523784417381780916503)
    ·
      refine ⟨17006285676626072671374755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11337523784417381780916503 17006285676626072671374755)
      ·
        refine ⟨25509428514939109007062133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17006285676626072671374755 25509428514939109007062133)
        ·
          refine ⟨2391508923275541469412075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25509428514939109007062133 2391508923275541469412075)
          ·
            refine ⟨3587263384913312204118113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391508923275541469412075 3587263384913312204118113)
            ·
              refine ⟨2690447538684984153088585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3587263384913312204118113 2690447538684984153088585)
              ·
                refine ⟨2017835654013738114816439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690447538684984153088585 2017835654013738114816439)
                ·
                  refine ⟨3026753481020607172224659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017835654013738114816439 3026753481020607172224659)
                  ·
                    refine ⟨4540130221530910758336989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3026753481020607172224659 4540130221530910758336989)
                    ·
                      refine ⟨1702548833074091534376371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4540130221530910758336989 1702548833074091534376371)
                      ·
                        rfl

theorem cell23_3315702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_3315702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315702 prefixEnd_3315702 := by exact prefixLift 3315702
  have htrace : WordTrace (prefixWord ++ tailWord_3315702) baseStart_3315702 baseEnd_3315702 := by
    simpa [prefixWord, tailWord_3315702, baseEnd_3315702] using wordTrace_append hprefix tailTrace_3315702
  have hstable : (prefixWord ++ tailWord_3315702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315702).length < 2 ^ (prefixWord ++ tailWord_3315702).sum := by decide
  have hdescent : baseEnd_3315702 < baseStart_3315702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315707 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 4, 1, 3]
def baseStart_3315707 : Nat := 118140960795 + 3315707 * 2 ^ 59
def prefixEnd_3315707 : Nat := 4983230072969 + 3 ^ 40 * 3315707 * 2
def baseEnd_3315707 : Nat := 1702551400477364014813847

theorem tailTrace_3315707 : CollatzResearch.WordTrace tailWord_3315707 prefixEnd_3315707 1702551400477364014813847 := by
  unfold tailWord_3315707
  simp only [CollatzResearch.WordTrace]
  refine ⟨120933769398767291517041375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80622512932511527678027583 120933769398767291517041375)
  ·
    refine ⟨181400654098150937275562063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120933769398767291517041375 181400654098150937275562063)
    ·
      refine ⟨272100981147226405913343095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181400654098150937275562063 272100981147226405913343095)
      ·
        refine ⟨408151471720839608870014643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272100981147226405913343095 408151471720839608870014643)
        ·
          refine ⟨612227207581259413305021965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408151471720839608870014643 612227207581259413305021965)
          ·
            refine ⟨229585202842972279989383237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612227207581259413305021965 229585202842972279989383237)
            ·
              refine ⟨43047225533057302498009357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229585202842972279989383237 43047225533057302498009357)
              ·
                refine ⟨16142709574896488436753509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43047225533057302498009357 16142709574896488436753509)
                ·
                  refine ⟨3026758045293091581891283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16142709574896488436753509 3026758045293091581891283)
                  ·
                    refine ⟨4540137067939637372836925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3026758045293091581891283 4540137067939637372836925)
                    ·
                      refine ⟨1702551400477364014813847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4540137067939637372836925 1702551400477364014813847)
                      ·
                        rfl

theorem cell23_3315707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 1, 3].length) (baseStart_3315707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315707 prefixEnd_3315707 := by exact prefixLift 3315707
  have htrace : WordTrace (prefixWord ++ tailWord_3315707) baseStart_3315707 baseEnd_3315707 := by
    simpa [prefixWord, tailWord_3315707, baseEnd_3315707] using wordTrace_append hprefix tailTrace_3315707
  have hstable : (prefixWord ++ tailWord_3315707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315707).length < 2 ^ (prefixWord ++ tailWord_3315707).sum := by decide
  have hdescent : baseEnd_3315707 < baseStart_3315707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315724 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 2, 1, 3]
def baseStart_3315724 : Nat := 118140960795 + 3315724 * 2 ^ 59
def prefixEnd_3315724 : Nat := 4983230072969 + 3 ^ 40 * 3315724 * 2
def baseEnd_3315724 : Nat := 1702560129648490448301269

theorem tailTrace_3315724 : CollatzResearch.WordTrace tailWord_3315724 prefixEnd_3315724 1702560129648490448301269 := by
  unfold tailWord_3315724
  simp only [CollatzResearch.WordTrace]
  refine ⟨60467194719852851710205113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80622926293137135613606817 60467194719852851710205113)
  ·
    refine ⟨45350396039889638782653835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60467194719852851710205113 45350396039889638782653835)
    ·
      refine ⟨68025594059834458173980753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45350396039889638782653835 68025594059834458173980753)
      ·
        refine ⟨51019195544875843630485565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68025594059834458173980753 51019195544875843630485565)
        ·
          refine ⟨19132198329328441361432087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51019195544875843630485565 19132198329328441361432087)
          ·
            refine ⟨28698297493992662042148131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19132198329328441361432087 28698297493992662042148131)
            ·
              refine ⟨43047446240988993063222197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28698297493992662042148131 43047446240988993063222197)
              ·
                refine ⟨4035698085092718099677081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43047446240988993063222197 4035698085092718099677081)
                ·
                  refine ⟨3026773563819538574757811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4035698085092718099677081 3026773563819538574757811)
                  ·
                    refine ⟨4540160345729307862136717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3026773563819538574757811 4540160345729307862136717)
                    ·
                      refine ⟨1702560129648490448301269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4540160345729307862136717 1702560129648490448301269)
                      ·
                        rfl

theorem cell23_3315724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_3315724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315724 prefixEnd_3315724 := by exact prefixLift 3315724
  have htrace : WordTrace (prefixWord ++ tailWord_3315724) baseStart_3315724 baseEnd_3315724 := by
    simpa [prefixWord, tailWord_3315724, baseEnd_3315724] using wordTrace_append hprefix tailTrace_3315724
  have hstable : (prefixWord ++ tailWord_3315724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315724).length < 2 ^ (prefixWord ++ tailWord_3315724).sum := by decide
  have hdescent : baseEnd_3315724 < baseStart_3315724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315758 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3315758 : Nat := 118140960795 + 3315758 * 2 ^ 59
def prefixEnd_3315758 : Nat := 4983230072969 + 3 ^ 40 * 3315758 * 2
def baseEnd_3315758 : Nat := 1702577587990743315276113

theorem tailTrace_3315758 : CollatzResearch.WordTrace tailWord_3315758 prefixEnd_3315758 1702577587990743315276113 := by
  unfold tailWord_3315758
  simp only [CollatzResearch.WordTrace]
  refine ⟨15116953690197815903393491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80623753014388351484765285 15116953690197815903393491)
  ·
    refine ⟨22675430535296723855090237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15116953690197815903393491 22675430535296723855090237)
    ·
      refine ⟨8503286450736271445658839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22675430535296723855090237 8503286450736271445658839)
      ·
        refine ⟨12754929676104407168488259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8503286450736271445658839 12754929676104407168488259)
        ·
          refine ⟨19132394514156610752732389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12754929676104407168488259 19132394514156610752732389)
          ·
            refine ⟨3587323971404364516137323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19132394514156610752732389 3587323971404364516137323)
            ·
              refine ⟨5380985957106546774205985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587323971404364516137323 5380985957106546774205985)
              ·
                refine ⟨4035739467829910080654489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5380985957106546774205985 4035739467829910080654489)
                ·
                  refine ⟨3026804600872432560490867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4035739467829910080654489 3026804600872432560490867)
                  ·
                    refine ⟨4540206901308648840736301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3026804600872432560490867 4540206901308648840736301)
                    ·
                      refine ⟨1702577587990743315276113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4540206901308648840736301 1702577587990743315276113)
                      ·
                        rfl

theorem cell23_3315758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3315758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315758 prefixEnd_3315758 := by exact prefixLift 3315758
  have htrace : WordTrace (prefixWord ++ tailWord_3315758) baseStart_3315758 baseEnd_3315758 := by
    simpa [prefixWord, tailWord_3315758, baseEnd_3315758] using wordTrace_append hprefix tailTrace_3315758
  have hstable : (prefixWord ++ tailWord_3315758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315758).length < 2 ^ (prefixWord ++ tailWord_3315758).sum := by decide
  have hdescent : baseEnd_3315758 < baseStart_3315758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315817 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 2, 5]
def baseStart_3315817 : Nat := 118140960795 + 3315817 * 2 ^ 59
def prefixEnd_3315817 : Nat := 4983230072969 + 3 ^ 40 * 3315817 * 2
def baseEnd_3315817 : Nat := 567535961116452861479447

theorem tailTrace_3315817 : CollatzResearch.WordTrace tailWord_3315817 prefixEnd_3315817 567535961116452861479447 := by
  unfold tailWord_3315817
  simp only [CollatzResearch.WordTrace]
  refine ⟨120937781428368780303545705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80625187618912520202363803 120937781428368780303545705)
  ·
    refine ⟨90703336071276585227659279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120937781428368780303545705 90703336071276585227659279)
    ·
      refine ⟨136055004106914877841488919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90703336071276585227659279 136055004106914877841488919)
      ·
        refine ⟨204082506160372316762233379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136055004106914877841488919 204082506160372316762233379)
        ·
          refine ⟨306123759240558475143350069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204082506160372316762233379 306123759240558475143350069)
          ·
            refine ⟨28699102428802357044689069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 306123759240558475143350069 28699102428802357044689069)
            ·
              refine ⟨10762163410800883891758401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28699102428802357044689069 10762163410800883891758401)
              ·
                refine ⟨8071622558100662918818801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10762163410800883891758401 8071622558100662918818801)
                ·
                  refine ⟨6053716918575497189114101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8071622558100662918818801 6053716918575497189114101)
                  ·
                    refine ⟨567535961116452861479447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6053716918575497189114101 567535961116452861479447)
                    ·
                      rfl

theorem cell23_3315817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_3315817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315817 prefixEnd_3315817 := by exact prefixLift 3315817
  have htrace : WordTrace (prefixWord ++ tailWord_3315817) baseStart_3315817 baseEnd_3315817 := by
    simpa [prefixWord, tailWord_3315817, baseEnd_3315817] using wordTrace_append hprefix tailTrace_3315817
  have hstable : (prefixWord ++ tailWord_3315817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315817).length < 2 ^ (prefixWord ++ tailWord_3315817).sum := by decide
  have hdescent : baseEnd_3315817 < baseStart_3315817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315821 : List Nat := [1, 5, 1, 1, 2, 1, 5, 2, 5]
def baseStart_3315821 : Nat := 118140960795 + 3315821 * 2 ^ 59
def prefixEnd_3315821 : Nat := 4983230072969 + 3 ^ 40 * 3315821 * 2
def baseEnd_3315821 : Nat := 189178881919108507643147

theorem tailTrace_3315821 : CollatzResearch.WordTrace tailWord_3315821 prefixEnd_3315821 189178881919108507643147 := by
  unfold tailWord_3315821
  simp only [CollatzResearch.WordTrace]
  refine ⟨120937927320354288986691317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80625284880236192657794211 120937927320354288986691317)
  ·
    refine ⟨11337930686283214592502311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120937927320354288986691317 11337930686283214592502311)
    ·
      refine ⟨17006896029424821888753467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11337930686283214592502311 17006896029424821888753467)
      ·
        refine ⟨25510344044137232833130201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17006896029424821888753467 25510344044137232833130201)
        ·
          refine ⟨19132758033102924624847651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25510344044137232833130201 19132758033102924624847651)
          ·
            refine ⟨28699137049654386937271477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19132758033102924624847651 28699137049654386937271477)
            ·
              refine ⟨2690544098405098775369201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28699137049654386937271477 2690544098405098775369201)
              ·
                refine ⟨2017908073803824081526901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690544098405098775369201 2017908073803824081526901)
                ·
                  refine ⟨189178881919108507643147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2017908073803824081526901 189178881919108507643147)
                  ·
                    rfl

theorem cell23_3315821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_3315821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315821 prefixEnd_3315821 := by exact prefixLift 3315821
  have htrace : WordTrace (prefixWord ++ tailWord_3315821) baseStart_3315821 baseEnd_3315821 := by
    simpa [prefixWord, tailWord_3315821, baseEnd_3315821] using wordTrace_append hprefix tailTrace_3315821
  have hstable : (prefixWord ++ tailWord_3315821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315821).length < 2 ^ (prefixWord ++ tailWord_3315821).sum := by decide
  have hdescent : baseEnd_3315821 < baseStart_3315821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315887 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 3]
def baseStart_3315887 : Nat := 118140960795 + 3315887 * 2 ^ 59
def prefixEnd_3315887 : Nat := 4983230072969 + 3 ^ 40 * 3315887 * 2
def baseEnd_3315887 : Nat := 1702643826995173310563019

theorem tailTrace_3315887 : CollatzResearch.WordTrace tailWord_3315887 prefixEnd_3315887 1702643826995173310563019 := by
  unfold tailWord_3315887
  simp only [CollatzResearch.WordTrace]
  refine ⟨120940334538115182258593915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80626889692076788172395943 120940334538115182258593915)
  ·
    refine ⟨181410501807172773387890873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120940334538115182258593915 181410501807172773387890873)
    ·
      refine ⟨136057876355379580040918155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181410501807172773387890873 136057876355379580040918155)
      ·
        refine ⟨204086814533069370061377233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136057876355379580040918155 204086814533069370061377233)
        ·
          refine ⟨153065110899802027546032925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204086814533069370061377233 153065110899802027546032925)
          ·
            refine ⟨57399416587425760329762347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153065110899802027546032925 57399416587425760329762347)
            ·
              refine ⟨86099124881138640494643521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57399416587425760329762347 86099124881138640494643521)
              ·
                refine ⟨64574343660853980370982641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86099124881138640494643521 64574343660853980370982641)
                ·
                  refine ⟨48430757745640485278236981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64574343660853980370982641 48430757745640485278236981)
                  ·
                    refine ⟨4540383538653795494834717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48430757745640485278236981 4540383538653795494834717)
                    ·
                      refine ⟨1702643826995173310563019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4540383538653795494834717 1702643826995173310563019)
                      ·
                        rfl

theorem cell23_3315887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 3].length) (baseStart_3315887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315887 prefixEnd_3315887 := by exact prefixLift 3315887
  have htrace : WordTrace (prefixWord ++ tailWord_3315887) baseStart_3315887 baseEnd_3315887 := by
    simpa [prefixWord, tailWord_3315887, baseEnd_3315887] using wordTrace_append hprefix tailTrace_3315887
  have hstable : (prefixWord ++ tailWord_3315887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315887).length < 2 ^ (prefixWord ++ tailWord_3315887).sum := by decide
  have hdescent : baseEnd_3315887 < baseStart_3315887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315905 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3315905 : Nat := 118140960795 + 3315905 * 2 ^ 59
def prefixEnd_3315905 : Nat := 4983230072969 + 3 ^ 40 * 3315905 * 2
def baseEnd_3315905 : Nat := 1702653069646954240137937

theorem tailTrace_3315905 : CollatzResearch.WordTrace tailWord_3315905 prefixEnd_3315905 1702653069646954240137937 := by
  unfold tailWord_3315905
  simp only [CollatzResearch.WordTrace]
  refine ⟨120940991052049971332749169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80627327368033314221832779 120940991052049971332749169)
  ·
    refine ⟨90705743289037478499561877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120940991052049971332749169 90705743289037478499561877)
    ·
      refine ⟨4251831716673631804666963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90705743289037478499561877 4251831716673631804666963)
      ·
        refine ⟨6377747575010447707000445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4251831716673631804666963 6377747575010447707000445)
        ·
          refine ⟨2391655340628917890125167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6377747575010447707000445 2391655340628917890125167)
          ·
            refine ⟨3587483010943376835187751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391655340628917890125167 3587483010943376835187751)
            ·
              refine ⟨5381224516415065252781627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587483010943376835187751 5381224516415065252781627)
              ·
                refine ⟨8071836774622597879172441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381224516415065252781627 8071836774622597879172441)
                ·
                  refine ⟨6053877580966948409379331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8071836774622597879172441 6053877580966948409379331)
                  ·
                    refine ⟨9080816371450422614068997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6053877580966948409379331 9080816371450422614068997)
                    ·
                      refine ⟨1702653069646954240137937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9080816371450422614068997 1702653069646954240137937)
                      ·
                        rfl

theorem cell23_3315905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3315905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315905 prefixEnd_3315905 := by exact prefixLift 3315905
  have htrace : WordTrace (prefixWord ++ tailWord_3315905) baseStart_3315905 baseEnd_3315905 := by
    simpa [prefixWord, tailWord_3315905, baseEnd_3315905] using wordTrace_append hprefix tailTrace_3315905
  have hstable : (prefixWord ++ tailWord_3315905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315905).length < 2 ^ (prefixWord ++ tailWord_3315905).sum := by decide
  have hdescent : baseEnd_3315905 < baseStart_3315905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315908 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_3315908 : Nat := 118140960795 + 3315908 * 2 ^ 59
def prefixEnd_3315908 : Nat := 4983230072969 + 3 ^ 40 * 3315908 * 2
def baseEnd_3315908 : Nat := 1702654610088917728400423

theorem tailTrace_3315908 : CollatzResearch.WordTrace tailWord_3315908 prefixEnd_3315908 1702654610088917728400423 := by
  unfold tailWord_3315908
  simp only [CollatzResearch.WordTrace]
  refine ⟨60470550235519551422554189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80627400314026068563405585 60470550235519551422554189)
  ·
    refine ⟨22676456338319831783457821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60470550235519551422554189 22676456338319831783457821)
    ·
      refine ⟨8503671126869936918796683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22676456338319831783457821 8503671126869936918796683)
      ·
        refine ⟨12755506690304905378195025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8503671126869936918796683 12755506690304905378195025)
        ·
          refine ⟨9566630017728679033646269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12755506690304905378195025 9566630017728679033646269)
          ·
            refine ⟨3587486256648254637617351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9566630017728679033646269 3587486256648254637617351)
            ·
              refine ⟨5381229384972381956426027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587486256648254637617351 5381229384972381956426027)
              ·
                refine ⟨8071844077458572934639041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381229384972381956426027 8071844077458572934639041)
                ·
                  refine ⟨6053883058093929700979281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8071844077458572934639041 6053883058093929700979281)
                  ·
                    refine ⟨4540412293570447275734461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6053883058093929700979281 4540412293570447275734461)
                    ·
                      refine ⟨1702654610088917728400423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4540412293570447275734461 1702654610088917728400423)
                      ·
                        rfl

theorem cell23_3315908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_3315908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315908 prefixEnd_3315908 := by exact prefixLift 3315908
  have htrace : WordTrace (prefixWord ++ tailWord_3315908) baseStart_3315908 baseEnd_3315908 := by
    simpa [prefixWord, tailWord_3315908, baseEnd_3315908] using wordTrace_append hprefix tailTrace_3315908
  have hstable : (prefixWord ++ tailWord_3315908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315908).length < 2 ^ (prefixWord ++ tailWord_3315908).sum := by decide
  have hdescent : baseEnd_3315908 < baseStart_3315908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315961 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 5, 2, 2]
def baseStart_3315961 : Nat := 118140960795 + 3315961 * 2 ^ 59
def prefixEnd_3315961 : Nat := 4983230072969 + 3 ^ 40 * 3315961 * 2
def baseEnd_3315961 : Nat := 1702681824563606021037679

theorem tailTrace_3315961 : CollatzResearch.WordTrace tailWord_3315961 prefixEnd_3315961 1702681824563606021037679 := by
  unfold tailWord_3315961
  simp only [CollatzResearch.WordTrace]
  refine ⟨120943033539847092896787737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80628689026564728597858491 120943033539847092896787737)
  ·
    refine ⟨90707275154885319672590803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120943033539847092896787737 90707275154885319672590803)
    ·
      refine ⟨136060912732327979508886205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90707275154885319672590803 136060912732327979508886205)
      ·
        refine ⟨51022842274622992315832327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136060912732327979508886205 51022842274622992315832327)
        ·
          refine ⟨76534263411934488473748491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51022842274622992315832327 76534263411934488473748491)
          ·
            refine ⟨114801395117901732710622737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76534263411934488473748491 114801395117901732710622737)
            ·
              refine ⟨86101046338426299532967053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114801395117901732710622737 86101046338426299532967053)
              ·
                refine ⟨32287892376909862324862645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86101046338426299532967053 32287892376909862324862645)
                ·
                  refine ⟨3026989910335299592955873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32287892376909862324862645 3026989910335299592955873)
                  ·
                    refine ⟨2270242432751474694716905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3026989910335299592955873 2270242432751474694716905)
                    ·
                      refine ⟨1702681824563606021037679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270242432751474694716905 1702681824563606021037679)
                      ·
                        rfl

theorem cell23_3315961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_3315961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315961 prefixEnd_3315961 := by exact prefixLift 3315961
  have htrace : WordTrace (prefixWord ++ tailWord_3315961) baseStart_3315961 baseEnd_3315961 := by
    simpa [prefixWord, tailWord_3315961, baseEnd_3315961] using wordTrace_append hprefix tailTrace_3315961
  have hstable : (prefixWord ++ tailWord_3315961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315961).length < 2 ^ (prefixWord ++ tailWord_3315961).sum := by decide
  have hdescent : baseEnd_3315961 < baseStart_3315961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315967 : List Nat := [1, 1, 2, 2, 1, 4, 3, 9]
def baseStart_3315967 : Nat := 118140960795 + 3315967 * 2 ^ 59
def prefixEnd_3315967 : Nat := 4983230072969 + 3 ^ 40 * 3315967 * 2
def baseEnd_3315967 : Nat := 63062403905464185094913

theorem tailTrace_3315967 : CollatzResearch.WordTrace tailWord_3315967 prefixEnd_3315967 63062403905464185094913 := by
  unfold tailWord_3315967
  simp only [CollatzResearch.WordTrace]
  refine ⟨120943252377825355921506155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80628834918550237281004103 120943252377825355921506155)
  ·
    refine ⟨181414878566738033882259233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120943252377825355921506155 181414878566738033882259233)
    ·
      refine ⟨136061158925053525411694425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181414878566738033882259233 136061158925053525411694425)
      ·
        refine ⟨102045869193790144058770819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136061158925053525411694425 102045869193790144058770819)
        ·
          refine ⟨153068803790685216088156229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102045869193790144058770819 153068803790685216088156229)
          ·
            refine ⟨28700400710753478016529293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153068803790685216088156229 28700400710753478016529293)
            ·
              refine ⟨10762650266532554256198485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28700400710753478016529293 10762650266532554256198485)
              ·
                refine ⟨63062403905464185094913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10762650266532554256198485 63062403905464185094913)
                ·
                  rfl

theorem cell23_3315967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 9].length) (baseStart_3315967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315967 prefixEnd_3315967 := by exact prefixLift 3315967
  have htrace : WordTrace (prefixWord ++ tailWord_3315967) baseStart_3315967 baseEnd_3315967 := by
    simpa [prefixWord, tailWord_3315967, baseEnd_3315967] using wordTrace_append hprefix tailTrace_3315967
  have hstable : (prefixWord ++ tailWord_3315967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315967).length < 2 ^ (prefixWord ++ tailWord_3315967).sum := by decide
  have hdescent : baseEnd_3315967 < baseStart_3315967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315972 : List Nat := [2, 3, 2, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_3315972 : Nat := 118140960795 + 3315972 * 2 ^ 59
def prefixEnd_3315972 : Nat := 4983230072969 + 3 ^ 40 * 3315972 * 2
def baseEnd_3315972 : Nat := 1702687472850805478000129

theorem tailTrace_3315972 : CollatzResearch.WordTrace tailWord_3315972 prefixEnd_3315972 1702687472850805478000129 := by
  unfold tailWord_3315972
  simp only [CollatzResearch.WordTrace]
  refine ⟨60471717371403620887719085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80628956495204827850292113 60471717371403620887719085)
  ·
    refine ⟨22676894014276357832894657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60471717371403620887719085 22676894014276357832894657)
    ·
      refine ⟨17007670510707268374670993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22676894014276357832894657 17007670510707268374670993)
      ·
        refine ⟨12755752883030451281003245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17007670510707268374670993 12755752883030451281003245)
        ·
          refine ⟨4783407331136419230376217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12755752883030451281003245 4783407331136419230376217)
          ·
            refine ⟨3587555498352314422782163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4783407331136419230376217 3587555498352314422782163)
            ·
              refine ⟨5381333247528471634173245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587555498352314422782163 5381333247528471634173245)
              ·
                refine ⟨2017999967823176862814967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5381333247528471634173245 2017999967823176862814967)
                ·
                  refine ⟨3026999951734765294222451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017999967823176862814967 3026999951734765294222451)
                  ·
                    refine ⟨4540499927602147941333677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3026999951734765294222451 4540499927602147941333677)
                    ·
                      refine ⟨1702687472850805478000129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4540499927602147941333677 1702687472850805478000129)
                      ·
                        rfl

theorem cell23_3315972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_3315972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315972 prefixEnd_3315972 := by exact prefixLift 3315972
  have htrace : WordTrace (prefixWord ++ tailWord_3315972) baseStart_3315972 baseEnd_3315972 := by
    simpa [prefixWord, tailWord_3315972, baseEnd_3315972] using wordTrace_append hprefix tailTrace_3315972
  have hstable : (prefixWord ++ tailWord_3315972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315972).length < 2 ^ (prefixWord ++ tailWord_3315972).sum := by decide
  have hdescent : baseEnd_3315972 < baseStart_3315972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315998 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3315998 : Nat := 118140960795 + 3315998 * 2 ^ 59
def prefixEnd_3315998 : Nat := 4983230072969 + 3 ^ 40 * 3315998 * 2
def baseEnd_3315998 : Nat := 1702700823347822376275009

theorem tailTrace_3315998 : CollatzResearch.WordTrace tailWord_3315998 prefixEnd_3315998 1702700823347822376275009 := by
  unfold tailWord_3315998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15118047880089131026985581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80629588693808698810589765 15118047880089131026985581)
  ·
    refine ⟨5669267955033424135119593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15118047880089131026985581 5669267955033424135119593)
    ·
      refine ⟨4251950966275068101339695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5669267955033424135119593 4251950966275068101339695)
      ·
        refine ⟨6377926449412602152009543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4251950966275068101339695 6377926449412602152009543)
        ·
          refine ⟨9566889674118903228014315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6377926449412602152009543 9566889674118903228014315)
          ·
            refine ⟨14350334511178354842021473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9566889674118903228014315 14350334511178354842021473)
            ·
              refine ⟨10762750883383766131516105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14350334511178354842021473 10762750883383766131516105)
              ·
                refine ⟨8072063162537824598637079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10762750883383766131516105 8072063162537824598637079)
                ·
                  refine ⟨12108094743806736897955619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8072063162537824598637079 12108094743806736897955619)
                  ·
                    refine ⟨18162142115710105346933429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12108094743806736897955619 18162142115710105346933429)
                    ·
                      refine ⟨1702700823347822376275009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18162142115710105346933429 1702700823347822376275009)
                      ·
                        rfl

theorem cell23_3315998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3315998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3315998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3315998 prefixEnd_3315998 := by exact prefixLift 3315998
  have htrace : WordTrace (prefixWord ++ tailWord_3315998) baseStart_3315998 baseEnd_3315998 := by
    simpa [prefixWord, tailWord_3315998, baseEnd_3315998] using wordTrace_append hprefix tailTrace_3315998
  have hstable : (prefixWord ++ tailWord_3315998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315998).length < 2 ^ (prefixWord ++ tailWord_3315998).sum := by decide
  have hdescent : baseEnd_3315998 < baseStart_3315998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316005 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 2, 4]
def baseStart_3316005 : Nat := 118140960795 + 3316005 * 2 ^ 59
def prefixEnd_3316005 : Nat := 4983230072969 + 3 ^ 40 * 3316005 * 2
def baseEnd_3316005 : Nat := 567568139237467949629159

theorem tailTrace_3316005 : CollatzResearch.WordTrace tailWord_3316005 prefixEnd_3316005 567568139237467949629159 := by
  unfold tailWord_3316005
  simp only [CollatzResearch.WordTrace]
  refine ⟨120944638351687688411389469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80629758901125125607592979 120944638351687688411389469)
  ·
    refine ⟨45354239381882883154271051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120944638351687688411389469 45354239381882883154271051)
    ·
      refine ⟨68031359072824324731406577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45354239381882883154271051 68031359072824324731406577)
      ·
        refine ⟨51023519304618243548554933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68031359072824324731406577 51023519304618243548554933)
        ·
          refine ⟨4783454934807960332677025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51023519304618243548554933 4783454934807960332677025)
          ·
            refine ⟨3587591201105970249507769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4783454934807960332677025 3587591201105970249507769)
            ·
              refine ⟨2690693400829477687130827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3587591201105970249507769 2690693400829477687130827)
              ·
                refine ⟨4036040101244216530696241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2690693400829477687130827 4036040101244216530696241)
                ·
                  refine ⟨3027030075933162398022181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4036040101244216530696241 3027030075933162398022181)
                  ·
                    refine ⟨567568139237467949629159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3027030075933162398022181 567568139237467949629159)
                    ·
                      rfl

theorem cell23_3316005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_3316005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316005 prefixEnd_3316005 := by exact prefixLift 3316005
  have htrace : WordTrace (prefixWord ++ tailWord_3316005) baseStart_3316005 baseEnd_3316005 := by
    simpa [prefixWord, tailWord_3316005, baseEnd_3316005] using wordTrace_append hprefix tailTrace_3316005
  have hstable : (prefixWord ++ tailWord_3316005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316005).length < 2 ^ (prefixWord ++ tailWord_3316005).sum := by decide
  have hdescent : baseEnd_3316005 < baseStart_3316005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316044 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_3316044 : Nat := 118140960795 + 3316044 * 2 ^ 59
def prefixEnd_3316044 : Nat := 4983230072969 + 3 ^ 40 * 3316044 * 2
def baseEnd_3316044 : Nat := 567574814485976398766599

theorem tailTrace_3316044 : CollatzResearch.WordTrace tailWord_3316044 prefixEnd_3316044 567574814485976398766599 := by
  unfold tailWord_3316044
  simp only [CollatzResearch.WordTrace]
  refine ⟨60473030399273199036029593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80630707199030932048039457 60473030399273199036029593)
  ·
    refine ⟨45354772799454899277022195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60473030399273199036029593 45354772799454899277022195)
    ·
      refine ⟨68032159199182348915533293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45354772799454899277022195 68032159199182348915533293)
      ·
        refine ⟨25512059699693380843324985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68032159199182348915533293 25512059699693380843324985)
        ·
          refine ⟨19134044774770035632493739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25512059699693380843324985 19134044774770035632493739)
          ·
            refine ⟨28701067162155053448740609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19134044774770035632493739 28701067162155053448740609)
            ·
              refine ⟨21525800371616290086555457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28701067162155053448740609 21525800371616290086555457)
              ·
                refine ⟨16144350278712217564916593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21525800371616290086555457 16144350278712217564916593)
                ·
                  refine ⟨12108262709034163173687445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16144350278712217564916593 12108262709034163173687445)
                  ·
                    refine ⟨567574814485976398766599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12108262709034163173687445 567574814485976398766599)
                    ·
                      rfl

theorem cell23_3316044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_3316044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316044 prefixEnd_3316044 := by exact prefixLift 3316044
  have htrace : WordTrace (prefixWord ++ tailWord_3316044) baseStart_3316044 baseEnd_3316044 := by
    simpa [prefixWord, tailWord_3316044, baseEnd_3316044] using wordTrace_append hprefix tailTrace_3316044
  have hstable : (prefixWord ++ tailWord_3316044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316044).length < 2 ^ (prefixWord ++ tailWord_3316044).sum := by decide
  have hdescent : baseEnd_3316044 < baseStart_3316044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316068 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 1, 4, 2]
def baseStart_3316068 : Nat := 118140960795 + 3316068 * 2 ^ 59
def prefixEnd_3316068 : Nat := 4983230072969 + 3 ^ 40 * 3316068 * 2
def baseEnd_3316068 : Nat := 1702736766993637102399687

theorem tailTrace_3316068 : CollatzResearch.WordTrace tailWord_3316068 prefixEnd_3316068 1702736766993637102399687 := by
  unfold tailWord_3316068
  simp only [CollatzResearch.WordTrace]
  refine ⟨60473468075229725085466429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80631290766972966780621905 60473468075229725085466429)
  ·
    refine ⟨22677550528211146907049911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60473468075229725085466429 22677550528211146907049911)
    ·
      refine ⟨34016325792316720360574867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22677550528211146907049911 34016325792316720360574867)
      ·
        refine ⟨51024488688475080540862301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34016325792316720360574867 51024488688475080540862301)
        ·
          refine ⟨19134183258178155202823363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51024488688475080540862301 19134183258178155202823363)
          ·
            refine ⟨28701274887267232804235045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19134183258178155202823363 28701274887267232804235045)
            ·
              refine ⟨5381489041362606150794071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28701274887267232804235045 5381489041362606150794071)
              ·
                refine ⟨8072233562043909226191107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381489041362606150794071 8072233562043909226191107)
                ·
                  refine ⟨12108350343065863839286661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8072233562043909226191107 12108350343065863839286661)
                  ·
                    refine ⟨2270315689324849469866249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12108350343065863839286661 2270315689324849469866249)
                    ·
                      refine ⟨1702736766993637102399687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270315689324849469866249 1702736766993637102399687)
                      ·
                        rfl

theorem cell23_3316068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_3316068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316068 prefixEnd_3316068 := by exact prefixLift 3316068
  have htrace : WordTrace (prefixWord ++ tailWord_3316068) baseStart_3316068 baseEnd_3316068 := by
    simpa [prefixWord, tailWord_3316068, baseEnd_3316068] using wordTrace_append hprefix tailTrace_3316068
  have hstable : (prefixWord ++ tailWord_3316068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316068).length < 2 ^ (prefixWord ++ tailWord_3316068).sum := by decide
  have hdescent : baseEnd_3316068 < baseStart_3316068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316091 : List Nat := [1, 1, 1, 1, 1, 7, 1, 5, 5]
def baseStart_3316091 : Nat := 118140960795 + 3316091 * 2 ^ 59
def prefixEnd_3316091 : Nat := 4983230072969 + 3 ^ 40 * 3316091 * 2
def baseEnd_3316091 : Nat := 189194286338743390268009

theorem tailTrace_3316091 : CollatzResearch.WordTrace tailWord_3316091 prefixEnd_3316091 189194286338743390268009 := by
  unfold tailWord_3316091
  simp only [CollatzResearch.WordTrace]
  refine ⟨120947775029376125099020127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80631850019584083399346751 120947775029376125099020127)
  ·
    refine ⟨181421662544064187648530191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120947775029376125099020127 181421662544064187648530191)
    ·
      refine ⟨272132493816096281472795287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181421662544064187648530191 272132493816096281472795287)
      ·
        refine ⟨408198740724144422209192931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272132493816096281472795287 408198740724144422209192931)
        ·
          refine ⟨612298111086216633313789397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408198740724144422209192931 612298111086216633313789397)
          ·
            refine ⟨14350736978583202343291939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 612298111086216633313789397 14350736978583202343291939)
            ·
              refine ⟨21526105467874803514937909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14350736978583202343291939 21526105467874803514937909)
              ·
                refine ⟨2018072387613262829525429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21526105467874803514937909 2018072387613262829525429)
                ·
                  refine ⟨189194286338743390268009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2018072387613262829525429 189194286338743390268009)
                  ·
                    rfl

theorem cell23_3316091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 5].length) (baseStart_3316091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316091 prefixEnd_3316091 := by exact prefixLift 3316091
  have htrace : WordTrace (prefixWord ++ tailWord_3316091) baseStart_3316091 baseEnd_3316091 := by
    simpa [prefixWord, tailWord_3316091, baseEnd_3316091] using wordTrace_append hprefix tailTrace_3316091
  have hstable : (prefixWord ++ tailWord_3316091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316091).length < 2 ^ (prefixWord ++ tailWord_3316091).sum := by decide
  have hdescent : baseEnd_3316091 < baseStart_3316091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316154 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_3316154 : Nat := 118140960795 + 3316154 * 2 ^ 59
def prefixEnd_3316154 : Nat := 4983230072969 + 3 ^ 40 * 3316154 * 2
def baseEnd_3316154 : Nat := 1702780926329923765924291

theorem tailTrace_3316154 : CollatzResearch.WordTrace tailWord_3316154 prefixEnd_3316154 1702780926329923765924291 := by
  unfold tailWord_3316154
  simp only [CollatzResearch.WordTrace]
  refine ⟨30237518207036971714640879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80633381885431924572375677 30237518207036971714640879)
  ·
    refine ⟨45356277310555457571961319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30237518207036971714640879 45356277310555457571961319)
    ·
      refine ⟨68034415965833186357941979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45356277310555457571961319 68034415965833186357941979)
      ·
        refine ⟨102051623948749779536912969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68034415965833186357941979 102051623948749779536912969)
        ·
          refine ⟨76538717961562334652684727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102051623948749779536912969 76538717961562334652684727)
          ·
            refine ⟨114808076942343501979027091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76538717961562334652684727 114808076942343501979027091)
            ·
              refine ⟨172212115413515252968540637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114808076942343501979027091 172212115413515252968540637)
              ·
                refine ⟨64579543280068219863202739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172212115413515252968540637 64579543280068219863202739)
                ·
                  refine ⟨96869314920102329794804109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64579543280068219863202739 96869314920102329794804109)
                  ·
                    refine ⟨36325993095038373673051541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96869314920102329794804109 36325993095038373673051541)
                    ·
                      refine ⟨1702780926329923765924291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36325993095038373673051541 1702780926329923765924291)
                      ·
                        rfl

theorem cell23_3316154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_3316154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316154 prefixEnd_3316154 := by exact prefixLift 3316154
  have htrace : WordTrace (prefixWord ++ tailWord_3316154) baseStart_3316154 baseEnd_3316154 := by
    simpa [prefixWord, tailWord_3316154, baseEnd_3316154] using wordTrace_append hprefix tailTrace_3316154
  have hstable : (prefixWord ++ tailWord_3316154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316154).length < 2 ^ (prefixWord ++ tailWord_3316154).sum := by decide
  have hdescent : baseEnd_3316154 < baseStart_3316154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316158 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_3316158 : Nat := 118140960795 + 3316158 * 2 ^ 59
def prefixEnd_3316158 : Nat := 4983230072969 + 3 ^ 40 * 3316158 * 2
def baseEnd_3316158 : Nat := 1702782980252541750274273

theorem tailTrace_3316158 : CollatzResearch.WordTrace tailWord_3316158 prefixEnd_3316158 1702782980252541750274273 := by
  unfold tailWord_3316158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15118777340016674442713641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80633479146755597027806085 15118777340016674442713641)
  ·
    refine ⟨11339083005012505832035231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15118777340016674442713641 11339083005012505832035231)
    ·
      refine ⟨17008624507518758748052847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11339083005012505832035231 17008624507518758748052847)
      ·
        refine ⟨25512936761278138122079271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17008624507518758748052847 25512936761278138122079271)
        ·
          refine ⟨38269405141917207183118907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25512936761278138122079271 38269405141917207183118907)
          ·
            refine ⟨57404107712875810774678361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38269405141917207183118907 57404107712875810774678361)
            ·
              refine ⟨43053080784656858081008771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57404107712875810774678361 43053080784656858081008771)
              ·
                refine ⟨64579621176985287121513157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43053080784656858081008771 64579621176985287121513157)
                ·
                  refine ⟨12108678970684741335283717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64579621176985287121513157 12108678970684741335283717)
                  ·
                    refine ⟨2270377307003389000365697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12108678970684741335283717 2270377307003389000365697)
                    ·
                      refine ⟨1702782980252541750274273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270377307003389000365697 1702782980252541750274273)
                      ·
                        rfl

theorem cell23_3316158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_3316158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316158 prefixEnd_3316158 := by exact prefixLift 3316158
  have htrace : WordTrace (prefixWord ++ tailWord_3316158) baseStart_3316158 baseEnd_3316158 := by
    simpa [prefixWord, tailWord_3316158, baseEnd_3316158] using wordTrace_append hprefix tailTrace_3316158
  have hstable : (prefixWord ++ tailWord_3316158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316158).length < 2 ^ (prefixWord ++ tailWord_3316158).sum := by decide
  have hdescent : baseEnd_3316158 < baseStart_3316158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
