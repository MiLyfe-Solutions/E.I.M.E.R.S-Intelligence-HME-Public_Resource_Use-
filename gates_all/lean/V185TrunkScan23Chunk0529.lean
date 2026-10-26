import V185TrunkScan23Chunk0528

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3127657 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 3, 5]
def baseStart_3127657 : Nat := 118140960795 + 3127657 * 2 ^ 59
def prefixEnd_3127657 : Nat := 4983230072969 + 3 ^ 40 * 3127657 * 2
def baseEnd_3127657 : Nat := 535330454466458253767891

theorem tailTrace_3127657 : CollatzResearch.WordTrace tailWord_3127657 prefixEnd_3127657 535330454466458253767891 := by
  unfold tailWord_3127657
  simp only [CollatzResearch.WordTrace]
  refine ⟨114075022430040325133957225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76050014953360216755971483 114075022430040325133957225)
  ·
    refine ⟨85556266822530243850467919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114075022430040325133957225 85556266822530243850467919)
    ·
      refine ⟨128334400233795365775701879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85556266822530243850467919 128334400233795365775701879)
      ·
        refine ⟨192501600350693048663552819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128334400233795365775701879 192501600350693048663552819)
        ·
          refine ⟨288752400526039572995329229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192501600350693048663552819 288752400526039572995329229)
          ·
            refine ⟨108282150197264839873248461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288752400526039572995329229 108282150197264839873248461)
            ·
              refine ⟨40605806323974314952468173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108282150197264839873248461 40605806323974314952468173)
              ·
                refine ⟨15227177371490368107175565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40605806323974314952468173 15227177371490368107175565)
                ·
                  refine ⟨5710191514308888040190837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15227177371490368107175565 5710191514308888040190837)
                  ·
                    refine ⟨535330454466458253767891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5710191514308888040190837 535330454466458253767891)
                    ·
                      rfl

theorem cell23_3127657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_3127657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127657 prefixEnd_3127657 := by exact prefixLift 3127657
  have htrace : WordTrace (prefixWord ++ tailWord_3127657) baseStart_3127657 baseEnd_3127657 := by
    simpa [prefixWord, tailWord_3127657, baseEnd_3127657] using wordTrace_append hprefix tailTrace_3127657
  have hstable : (prefixWord ++ tailWord_3127657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127657).length < 2 ^ (prefixWord ++ tailWord_3127657).sum := by decide
  have hdescent : baseEnd_3127657 < baseStart_3127657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127658 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3127658 : Nat := 118140960795 + 3127658 * 2 ^ 59
def prefixEnd_3127658 : Nat := 4983230072969 + 3 ^ 40 * 3127658 * 2
def baseEnd_3127658 : Nat := 1605991876880029257391169

theorem tailTrace_3127658 : CollatzResearch.WordTrace tailWord_3127658 prefixEnd_3127658 1605991876880029257391169 := by
  unfold tailWord_3127658
  simp only [CollatzResearch.WordTrace]
  refine ⟨28518764725759175576185907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76050039268691134869829085 28518764725759175576185907)
  ·
    refine ⟨42778147088638763364278861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28518764725759175576185907 42778147088638763364278861)
    ·
      refine ⟨16041805158239536261604573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42778147088638763364278861 16041805158239536261604573)
      ·
        refine ⟨6015676934339826098101715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16041805158239536261604573 6015676934339826098101715)
        ·
          refine ⟨9023515401509739147152573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6015676934339826098101715 9023515401509739147152573)
          ·
            refine ⟨3383818275566152180182215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9023515401509739147152573 3383818275566152180182215)
            ·
              refine ⟨5075727413349228270273323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383818275566152180182215 5075727413349228270273323)
              ·
                refine ⟨7613591120023842405409985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5075727413349228270273323 7613591120023842405409985)
                ·
                  refine ⟨5710193340017881804057489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7613591120023842405409985 5710193340017881804057489)
                  ·
                    refine ⟨4282645005013411353043117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5710193340017881804057489 4282645005013411353043117)
                    ·
                      refine ⟨1605991876880029257391169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4282645005013411353043117 1605991876880029257391169)
                      ·
                        rfl

theorem cell23_3127658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3127658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127658 prefixEnd_3127658 := by exact prefixLift 3127658
  have htrace : WordTrace (prefixWord ++ tailWord_3127658) baseStart_3127658 baseEnd_3127658 := by
    simpa [prefixWord, tailWord_3127658, baseEnd_3127658] using wordTrace_append hprefix tailTrace_3127658
  have hstable : (prefixWord ++ tailWord_3127658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127658).length < 2 ^ (prefixWord ++ tailWord_3127658).sum := by decide
  have hdescent : baseEnd_3127658 < baseStart_3127658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127688 : List Nat := [2, 1, 3, 3, 1, 1, 1, 6, 1, 1, 3]
def baseStart_3127688 : Nat := 118140960795 + 3127688 * 2 ^ 59
def prefixEnd_3127688 : Nat := 4983230072969 + 3 ^ 40 * 3127688 * 2
def baseEnd_3127688 : Nat := 1606007281299664140016031

theorem tailTrace_3127688 : CollatzResearch.WordTrace tailWord_3127688 prefixEnd_3127688 1606007281299664140016031 := by
  unfold tailWord_3127688
  simp only [CollatzResearch.WordTrace]
  refine ⟨57038076546464008714167859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76050768728618678285557145 57038076546464008714167859)
  ·
    refine ⟨85557114819696013071251789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57038076546464008714167859 85557114819696013071251789)
    ·
      refine ⟨32083918057386004901719421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85557114819696013071251789 32083918057386004901719421)
      ·
        refine ⟨12031469271519751838144783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32083918057386004901719421 12031469271519751838144783)
        ·
          refine ⟨18047203907279627757217175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12031469271519751838144783 18047203907279627757217175)
          ·
            refine ⟨27070805860919441635825763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18047203907279627757217175 27070805860919441635825763)
            ·
              refine ⟨40606208791379162453738645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27070805860919441635825763 40606208791379162453738645)
              ·
                refine ⟨1903416037095898240018999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40606208791379162453738645 1903416037095898240018999)
                ·
                  refine ⟨2855124055643847360028499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903416037095898240018999 2855124055643847360028499)
                  ·
                    refine ⟨4282686083465771040042749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2855124055643847360028499 4282686083465771040042749)
                    ·
                      refine ⟨1606007281299664140016031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4282686083465771040042749 1606007281299664140016031)
                      ·
                        rfl

theorem cell23_3127688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_3127688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127688 prefixEnd_3127688 := by exact prefixLift 3127688
  have htrace : WordTrace (prefixWord ++ tailWord_3127688) baseStart_3127688 baseEnd_3127688 := by
    simpa [prefixWord, tailWord_3127688, baseEnd_3127688] using wordTrace_append hprefix tailTrace_3127688
  have hstable : (prefixWord ++ tailWord_3127688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127688).length < 2 ^ (prefixWord ++ tailWord_3127688).sum := by decide
  have hdescent : baseEnd_3127688 < baseStart_3127688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127711 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 4]
def baseStart_3127711 : Nat := 118140960795 + 3127711 * 2 ^ 59
def prefixEnd_3127711 : Nat := 4983230072969 + 3 ^ 40 * 3127711 * 2
def baseEnd_3127711 : Nat := 1606019091354717550028425

theorem tailTrace_3127711 : CollatzResearch.WordTrace tailWord_3127711 prefixEnd_3127711 1606019091354717550028425 := by
  unfold tailWord_3127711
  simp only [CollatzResearch.WordTrace]
  refine ⟨114076991971844692356422987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76051327981229794904281991 114076991971844692356422987)
  ·
    refine ⟨171115487957767038534634481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114076991971844692356422987 171115487957767038534634481)
    ·
      refine ⟨128336615968325278900975861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171115487957767038534634481 128336615968325278900975861)
      ·
        refine ⟨12031557747030494896966487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128336615968325278900975861 12031557747030494896966487)
        ·
          refine ⟨18047336620545742345449731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12031557747030494896966487 18047336620545742345449731)
          ·
            refine ⟨27071004930818613518174597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18047336620545742345449731 27071004930818613518174597)
            ·
              refine ⟨5075813424528490034657737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27071004930818613518174597 5075813424528490034657737)
              ·
                refine ⟨3806860068396367525993303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5075813424528490034657737 3806860068396367525993303)
                ·
                  refine ⟨5710290102594551288989955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3806860068396367525993303 5710290102594551288989955)
                  ·
                    refine ⟨8565435153891826933484933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5710290102594551288989955 8565435153891826933484933)
                    ·
                      refine ⟨1606019091354717550028425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8565435153891826933484933 1606019091354717550028425)
                      ·
                        rfl

theorem cell23_3127711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_3127711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127711 prefixEnd_3127711 := by exact prefixLift 3127711
  have htrace : WordTrace (prefixWord ++ tailWord_3127711) baseStart_3127711 baseEnd_3127711 := by
    simpa [prefixWord, tailWord_3127711, baseEnd_3127711] using wordTrace_append hprefix tailTrace_3127711
  have hstable : (prefixWord ++ tailWord_3127711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127711).length < 2 ^ (prefixWord ++ tailWord_3127711).sum := by decide
  have hdescent : baseEnd_3127711 < baseStart_3127711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127714 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3127714 : Nat := 118140960795 + 3127714 * 2 ^ 59
def prefixEnd_3127714 : Nat := 4983230072969 + 3 ^ 40 * 3127714 * 2
def baseEnd_3127714 : Nat := 1606020631796681038290911

theorem tailTrace_3127714 : CollatzResearch.WordTrace tailWord_3127714 prefixEnd_3127714 1606020631796681038290911 := by
  unfold tailWord_3127714
  simp only [CollatzResearch.WordTrace]
  refine ⟨28519275347708455967195549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76051400927222549245854797 28519275347708455967195549)
  ·
    refine ⟨10694728255390670987698331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28519275347708455967195549 10694728255390670987698331)
    ·
      refine ⟨16042092383086006481547497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10694728255390670987698331 16042092383086006481547497)
      ·
        refine ⟨12031569287314504861160623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16042092383086006481547497 12031569287314504861160623)
        ·
          refine ⟨18047353930971757291740935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12031569287314504861160623 18047353930971757291740935)
          ·
            refine ⟨27071030896457635937611403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18047353930971757291740935 27071030896457635937611403)
            ·
              refine ⟨40606546344686453906417105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27071030896457635937611403 40606546344686453906417105)
              ·
                refine ⟨30454909758514840429812829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40606546344686453906417105 30454909758514840429812829)
                ·
                  refine ⟨11420591159443065161179811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30454909758514840429812829 11420591159443065161179811)
                  ·
                    refine ⟨17130886739164597741769717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11420591159443065161179811 17130886739164597741769717)
                    ·
                      refine ⟨1606020631796681038290911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17130886739164597741769717 1606020631796681038290911)
                      ·
                        rfl

theorem cell23_3127714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3127714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127714 prefixEnd_3127714 := by exact prefixLift 3127714
  have htrace : WordTrace (prefixWord ++ tailWord_3127714) baseStart_3127714 baseEnd_3127714 := by
    simpa [prefixWord, tailWord_3127714, baseEnd_3127714] using wordTrace_append hprefix tailTrace_3127714
  have hstable : (prefixWord ++ tailWord_3127714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127714).length < 2 ^ (prefixWord ++ tailWord_3127714).sum := by decide
  have hdescent : baseEnd_3127714 < baseStart_3127714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127717 : List Nat := [1, 3, 1, 2, 1, 1, 5, 9]
def baseStart_3127717 : Nat := 118140960795 + 3127717 * 2 ^ 59
def prefixEnd_3127717 : Nat := 4983230072969 + 3 ^ 40 * 3127717 * 2
def baseEnd_3127717 : Nat := 59482302675505352835311

theorem tailTrace_3127717 : CollatzResearch.WordTrace tailWord_3127717 prefixEnd_3127717 59482302675505352835311 := by
  unfold tailWord_3127717
  simp only [CollatzResearch.WordTrace]
  refine ⟨114077210809822955381141405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76051473873215303587427603 114077210809822955381141405)
  ·
    refine ⟨42778954053683608267928027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114077210809822955381141405 42778954053683608267928027)
    ·
      refine ⟨64168431080525412401892041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42778954053683608267928027 64168431080525412401892041)
      ·
        refine ⟨48126323310394059301419031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64168431080525412401892041 48126323310394059301419031)
        ·
          refine ⟨72189484965591088952128547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48126323310394059301419031 72189484965591088952128547)
          ·
            refine ⟨108284227448386633428192821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72189484965591088952128547 108284227448386633428192821)
            ·
              refine ⟨10151646323286246883893077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108284227448386633428192821 10151646323286246883893077)
              ·
                refine ⟨59482302675505352835311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10151646323286246883893077 59482302675505352835311)
                ·
                  rfl

theorem cell23_3127717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 9].length) (baseStart_3127717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127717 prefixEnd_3127717 := by exact prefixLift 3127717
  have htrace : WordTrace (prefixWord ++ tailWord_3127717) baseStart_3127717 baseEnd_3127717 := by
    simpa [prefixWord, tailWord_3127717, baseEnd_3127717] using wordTrace_append hprefix tailTrace_3127717
  have hstable : (prefixWord ++ tailWord_3127717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127717).length < 2 ^ (prefixWord ++ tailWord_3127717).sum := by decide
  have hdescent : baseEnd_3127717 < baseStart_3127717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127732 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_3127732 : Nat := 118140960795 + 3127732 * 2 ^ 59
def prefixEnd_3127732 : Nat := 4983230072969 + 3 ^ 40 * 3127732 * 2
def baseEnd_3127732 : Nat := 1606029874448461967865829

theorem tailTrace_3127732 : CollatzResearch.WordTrace tailWord_3127732 prefixEnd_3127732 1606029874448461967865829 := by
  unfold tailWord_3127732
  simp only [CollatzResearch.WordTrace]
  refine ⟨57038878952384306471468725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76051838603179075295291633 57038878952384306471468725)
  ·
    refine ⟨5347394901786028731700193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57038878952384306471468725 5347394901786028731700193)
    ·
      refine ⟨4010546176339521548775145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5347394901786028731700193 4010546176339521548775145)
      ·
        refine ⟨3007909632254641161581359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4010546176339521548775145 3007909632254641161581359)
        ·
          refine ⟨4511864448381961742372039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007909632254641161581359 4511864448381961742372039)
          ·
            refine ⟨6767796672572942613558059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4511864448381961742372039 6767796672572942613558059)
            ·
              refine ⟨10151695008859413920337089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6767796672572942613558059 10151695008859413920337089)
              ·
                refine ⟨7613771256644560440252817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10151695008859413920337089 7613771256644560440252817)
                ·
                  refine ⟨5710328442483420330189613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7613771256644560440252817 5710328442483420330189613)
                  ·
                    refine ⟨2141373165931282623821105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5710328442483420330189613 2141373165931282623821105)
                    ·
                      refine ⟨1606029874448461967865829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141373165931282623821105 1606029874448461967865829)
                      ·
                        rfl

theorem cell23_3127732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_3127732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127732 prefixEnd_3127732 := by exact prefixLift 3127732
  have htrace : WordTrace (prefixWord ++ tailWord_3127732) baseStart_3127732 baseEnd_3127732 := by
    simpa [prefixWord, tailWord_3127732, baseEnd_3127732] using wordTrace_append hprefix tailTrace_3127732
  have hstable : (prefixWord ++ tailWord_3127732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127732).length < 2 ^ (prefixWord ++ tailWord_3127732).sum := by decide
  have hdescent : baseEnd_3127732 < baseStart_3127732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127747 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 2, 7]
def baseStart_3127747 : Nat := 118140960795 + 3127747 * 2 ^ 59
def prefixEnd_3127747 : Nat := 4983230072969 + 3 ^ 40 * 3127747 * 2
def baseEnd_3127747 : Nat := 535345858886093136392753

theorem tailTrace_3127747 : CollatzResearch.WordTrace tailWord_3127747 prefixEnd_3127747 535345858886093136392753 := by
  unfold tailWord_3127747
  simp only [CollatzResearch.WordTrace]
  refine ⟨114078304999714270504733495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76052203333142847003155663 114078304999714270504733495)
  ·
    refine ⟨171117457499571405757100243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114078304999714270504733495 171117457499571405757100243)
    ·
      refine ⟨256676186249357108635650365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171117457499571405757100243 256676186249357108635650365)
      ·
        refine ⟨96253569843508915738368887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256676186249357108635650365 96253569843508915738368887)
        ·
          refine ⟨144380354765263373607553331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96253569843508915738368887 144380354765263373607553331)
          ·
            refine ⟨216570532147895060411329997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144380354765263373607553331 216570532147895060411329997)
            ·
              refine ⟨81213949555460647654248749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216570532147895060411329997 81213949555460647654248749)
              ·
                refine ⟨30455231083297742870343281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81213949555460647654248749 30455231083297742870343281)
                ·
                  refine ⟨22841423312473307152757461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30455231083297742870343281 22841423312473307152757461)
                  ·
                    refine ⟨535345858886093136392753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22841423312473307152757461 535345858886093136392753)
                    ·
                      rfl

theorem cell23_3127747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 7].length) (baseStart_3127747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127747 prefixEnd_3127747 := by exact prefixLift 3127747
  have htrace : WordTrace (prefixWord ++ tailWord_3127747) baseStart_3127747 baseEnd_3127747 := by
    simpa [prefixWord, tailWord_3127747, baseEnd_3127747] using wordTrace_append hprefix tailTrace_3127747
  have hstable : (prefixWord ++ tailWord_3127747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127747).length < 2 ^ (prefixWord ++ tailWord_3127747).sum := by decide
  have hdescent : baseEnd_3127747 < baseStart_3127747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127762 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_3127762 : Nat := 118140960795 + 3127762 * 2 ^ 59
def prefixEnd_3127762 : Nat := 4983230072969 + 3 ^ 40 * 3127762 * 2
def baseEnd_3127762 : Nat := 1606045278868096850490691

theorem tailTrace_3127762 : CollatzResearch.WordTrace tailWord_3127762 prefixEnd_3127762 1606045278868096850490691 := by
  unfold tailWord_3127762
  simp only [CollatzResearch.WordTrace]
  refine ⟨28519713023664982016632385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76052568063106618711019693 28519713023664982016632385)
  ·
    refine ⟨21389784767748736512474289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28519713023664982016632385 21389784767748736512474289)
    ·
      refine ⟨16042338575811552384355717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21389784767748736512474289 16042338575811552384355717)
      ·
        refine ⟨3007938482964666072066697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16042338575811552384355717 3007938482964666072066697)
        ·
          refine ⟨2255953862223499554050023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3007938482964666072066697 2255953862223499554050023)
          ·
            refine ⟨3383930793335249331075035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255953862223499554050023 3383930793335249331075035)
            ·
              refine ⟨5075896190002873996612553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383930793335249331075035 5075896190002873996612553)
              ·
                refine ⟨3806922142502155497459415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5075896190002873996612553 3806922142502155497459415)
                ·
                  refine ⟨5710383213753233246189123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3806922142502155497459415 5710383213753233246189123)
                  ·
                    refine ⟨8565574820629849869283685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5710383213753233246189123 8565574820629849869283685)
                    ·
                      refine ⟨1606045278868096850490691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8565574820629849869283685 1606045278868096850490691)
                      ·
                        rfl

theorem cell23_3127762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_3127762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127762 prefixEnd_3127762 := by exact prefixLift 3127762
  have htrace : WordTrace (prefixWord ++ tailWord_3127762) baseStart_3127762 baseEnd_3127762 := by
    simpa [prefixWord, tailWord_3127762, baseEnd_3127762] using wordTrace_append hprefix tailTrace_3127762
  have hstable : (prefixWord ++ tailWord_3127762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127762).length < 2 ^ (prefixWord ++ tailWord_3127762).sum := by decide
  have hdescent : baseEnd_3127762 < baseStart_3127762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127767 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_3127767 : Nat := 118140960795 + 3127767 * 2 ^ 59
def prefixEnd_3127767 : Nat := 4983230072969 + 3 ^ 40 * 3127767 * 2
def baseEnd_3127767 : Nat := 1606047846271369330928167

theorem tailTrace_3127767 : CollatzResearch.WordTrace tailWord_3127767 prefixEnd_3127767 1606047846271369330928167 := by
  unfold tailWord_3127767
  simp only [CollatzResearch.WordTrace]
  refine ⟨114079034459641813920461555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76052689639761209280307703 114079034459641813920461555)
  ·
    refine ⟨171118551689462720880692333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114079034459641813920461555 171118551689462720880692333)
    ·
      refine ⟨64169456883548520330259625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171118551689462720880692333 64169456883548520330259625)
      ·
        refine ⟨48127092662661390247694719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64169456883548520330259625 48127092662661390247694719)
        ·
          refine ⟨72190638993992085371542079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48127092662661390247694719 72190638993992085371542079)
          ·
            refine ⟨108285958490988128057313119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72190638993992085371542079 108285958490988128057313119)
            ·
              refine ⟨162428937736482192085969679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108285958490988128057313119 162428937736482192085969679)
              ·
                refine ⟨243643406604723288128954519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162428937736482192085969679 243643406604723288128954519)
                ·
                  refine ⟨365465109907084932193431779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243643406604723288128954519 365465109907084932193431779)
                  ·
                    refine ⟨548197664860627398290147669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 365465109907084932193431779 548197664860627398290147669)
                    ·
                      refine ⟨1606047846271369330928167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 548197664860627398290147669 1606047846271369330928167)
                      ·
                        rfl

theorem cell23_3127767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_3127767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127767 prefixEnd_3127767 := by exact prefixLift 3127767
  have htrace : WordTrace (prefixWord ++ tailWord_3127767) baseStart_3127767 baseEnd_3127767 := by
    simpa [prefixWord, tailWord_3127767, baseEnd_3127767] using wordTrace_append hprefix tailTrace_3127767
  have hstable : (prefixWord ++ tailWord_3127767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127767).length < 2 ^ (prefixWord ++ tailWord_3127767).sum := by decide
  have hdescent : baseEnd_3127767 < baseStart_3127767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127818 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2]
def baseStart_3127818 : Nat := 118140960795 + 3127818 * 2 ^ 59
def prefixEnd_3127818 : Nat := 4983230072969 + 3 ^ 40 * 3127818 * 2
def baseEnd_3127818 : Nat := 1606074033784748631390433

theorem tailTrace_3127818 : CollatzResearch.WordTrace tailWord_3127818 prefixEnd_3127818 1606074033784748631390433 := by
  unfold tailWord_3127818
  simp only [CollatzResearch.WordTrace]
  refine ⟨28520223645614262407642027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76053929721638033087045405 28520223645614262407642027)
  ·
    refine ⟨42780335468421393611463041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28520223645614262407642027 42780335468421393611463041)
    ·
      refine ⟨32085251601316045208597281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42780335468421393611463041 32085251601316045208597281)
      ·
        refine ⟨24063938700987033906447961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32085251601316045208597281 24063938700987033906447961)
        ·
          refine ⟨18047954025740275429835971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24063938700987033906447961 18047954025740275429835971)
          ·
            refine ⟨27071931038610413144753957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18047954025740275429835971 27071931038610413144753957)
            ·
              refine ⟨5075987069739452464641367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27071931038610413144753957 5075987069739452464641367)
              ·
                refine ⟨7613980604609178696962051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5075987069739452464641367 7613980604609178696962051)
                ·
                  refine ⟨11420970906913768045443077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7613980604609178696962051 11420970906913768045443077)
                  ·
                    refine ⟨2141432045046331508520577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11420970906913768045443077 2141432045046331508520577)
                    ·
                      refine ⟨1606074033784748631390433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141432045046331508520577 1606074033784748631390433)
                      ·
                        rfl

theorem cell23_3127818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_3127818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127818 prefixEnd_3127818 := by exact prefixLift 3127818
  have htrace : WordTrace (prefixWord ++ tailWord_3127818) baseStart_3127818 baseEnd_3127818 := by
    simpa [prefixWord, tailWord_3127818, baseEnd_3127818] using wordTrace_append hprefix tailTrace_3127818
  have hstable : (prefixWord ++ tailWord_3127818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127818).length < 2 ^ (prefixWord ++ tailWord_3127818).sum := by decide
  have hdescent : baseEnd_3127818 < baseStart_3127818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127864 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_3127864 : Nat := 118140960795 + 3127864 * 2 ^ 59
def prefixEnd_3127864 : Nat := 4983230072969 + 3 ^ 40 * 3127864 * 2
def baseEnd_3127864 : Nat := 1606097653894855451415221

theorem tailTrace_3127864 : CollatzResearch.WordTrace tailWord_3127864 prefixEnd_3127864 1606097653894855451415221 := by
  unfold tailWord_3127864
  simp only [CollatzResearch.WordTrace]
  refine ⟨57041286170145199743371323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76055048226860266324495097 57041286170145199743371323)
  ·
    refine ⟨85561929255217799615056985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57041286170145199743371323 85561929255217799615056985)
    ·
      refine ⟨64171446941413349711292739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85561929255217799615056985 64171446941413349711292739)
      ·
        refine ⟨96257170412120024566939109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64171446941413349711292739 96257170412120024566939109)
        ·
          refine ⟨18048219452272504606301083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96257170412120024566939109 18048219452272504606301083)
          ·
            refine ⟨27072329178408756909451625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18048219452272504606301083 27072329178408756909451625)
            ·
              refine ⟨20304246883806567682088719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27072329178408756909451625 20304246883806567682088719)
              ·
                refine ⟨30456370325709851523133079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20304246883806567682088719 30456370325709851523133079)
                ·
                  refine ⟨45684555488564777284699619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30456370325709851523133079 45684555488564777284699619)
                  ·
                    refine ⟨68526833232847165927049429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45684555488564777284699619 68526833232847165927049429)
                    ·
                      refine ⟨1606097653894855451415221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68526833232847165927049429 1606097653894855451415221)
                      ·
                        rfl

theorem cell23_3127864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_3127864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127864 prefixEnd_3127864 := by exact prefixLift 3127864
  have htrace : WordTrace (prefixWord ++ tailWord_3127864) baseStart_3127864 baseEnd_3127864 := by
    simpa [prefixWord, tailWord_3127864, baseEnd_3127864] using wordTrace_append hprefix tailTrace_3127864
  have hstable : (prefixWord ++ tailWord_3127864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127864).length < 2 ^ (prefixWord ++ tailWord_3127864).sum := by decide
  have hdescent : baseEnd_3127864 < baseStart_3127864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127884 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_3127884 : Nat := 118140960795 + 3127884 * 2 ^ 59
def prefixEnd_3127884 : Nat := 4983230072969 + 3 ^ 40 * 3127884 * 2
def baseEnd_3127884 : Nat := 535369307835981791055043

theorem tailTrace_3127884 : CollatzResearch.WordTrace tailWord_3127884 prefixEnd_3127884 535369307835981791055043 := by
  unfold tailWord_3127884
  simp only [CollatzResearch.WordTrace]
  refine ⟨57041650900108971451235353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76055534533478628601647137 57041650900108971451235353)
  ·
    refine ⟨42781238175081728588426515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57041650900108971451235353 42781238175081728588426515)
    ·
      refine ⟨64171857262622592882639773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42781238175081728588426515 64171857262622592882639773)
      ·
        refine ⟨24064446473483472330989915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64171857262622592882639773 24064446473483472330989915)
        ·
          refine ⟨36096669710225208496484873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24064446473483472330989915 36096669710225208496484873)
          ·
            refine ⟨27072502282668906372363655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36096669710225208496484873 27072502282668906372363655)
            ·
              refine ⟨40608753424003359558545483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27072502282668906372363655 40608753424003359558545483)
              ·
                refine ⟨60913130136005039337818225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40608753424003359558545483 60913130136005039337818225)
                ·
                  refine ⟨45684847602003779503363669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60913130136005039337818225 45684847602003779503363669)
                  ·
                    refine ⟨535369307835981791055043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45684847602003779503363669 535369307835981791055043)
                    ·
                      rfl

theorem cell23_3127884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_3127884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127884 prefixEnd_3127884 := by exact prefixLift 3127884
  have htrace : WordTrace (prefixWord ++ tailWord_3127884) baseStart_3127884 baseEnd_3127884 := by
    simpa [prefixWord, tailWord_3127884, baseEnd_3127884] using wordTrace_append hprefix tailTrace_3127884
  have hstable : (prefixWord ++ tailWord_3127884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127884).length < 2 ^ (prefixWord ++ tailWord_3127884).sum := by decide
  have hdescent : baseEnd_3127884 < baseStart_3127884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127904 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_3127904 : Nat := 118140960795 + 3127904 * 2 ^ 59
def prefixEnd_3127904 : Nat := 4983230072969 + 3 ^ 40 * 3127904 * 2
def baseEnd_3127904 : Nat := 1606118193121035294915037

theorem tailTrace_3127904 : CollatzResearch.WordTrace tailWord_3127904 prefixEnd_3127904 1606118193121035294915037 := by
  unfold tailWord_3127904
  simp only [CollatzResearch.WordTrace]
  refine ⟨57042015630072743159099383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76056020840096990878799177 57042015630072743159099383)
  ·
    refine ⟨85563023445109114738649075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57042015630072743159099383 85563023445109114738649075)
    ·
      refine ⟨128344535167663672107973613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85563023445109114738649075 128344535167663672107973613)
      ·
        refine ⟨48129200687873877040490105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128344535167663672107973613 48129200687873877040490105)
        ·
          refine ⟨36096900515905407780367579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48129200687873877040490105 36096900515905407780367579)
          ·
            refine ⟨54145350773858111670551369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36096900515905407780367579 54145350773858111670551369)
            ·
              refine ⟨40609013080393583752913527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54145350773858111670551369 40609013080393583752913527)
              ·
                refine ⟨60913519620590375629370291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40609013080393583752913527 60913519620590375629370291)
                ·
                  refine ⟨91370279430885563444055437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60913519620590375629370291 91370279430885563444055437)
                  ·
                    refine ⟨34263854786582086291520789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91370279430885563444055437 34263854786582086291520789)
                    ·
                      refine ⟨1606118193121035294915037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34263854786582086291520789 1606118193121035294915037)
                      ·
                        rfl

theorem cell23_3127904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_3127904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127904 prefixEnd_3127904 := by exact prefixLift 3127904
  have htrace : WordTrace (prefixWord ++ tailWord_3127904) baseStart_3127904 baseEnd_3127904 := by
    simpa [prefixWord, tailWord_3127904, baseEnd_3127904] using wordTrace_append hprefix tailTrace_3127904
  have hstable : (prefixWord ++ tailWord_3127904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127904).length < 2 ^ (prefixWord ++ tailWord_3127904).sum := by decide
  have hdescent : baseEnd_3127904 < baseStart_3127904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127969 : List Nat := [1, 2, 3, 3, 3, 2, 2, 2, 1, 4]
def baseStart_3127969 : Nat := 118140960795 + 3127969 * 2 ^ 59
def prefixEnd_3127969 : Nat := 4983230072969 + 3 ^ 40 * 3127969 * 2
def baseEnd_3127969 : Nat := 535383856454525846867413

theorem tailTrace_3127969 : CollatzResearch.WordTrace tailWord_3127969 prefixEnd_3127969 535383856454525846867413 := by
  unfold tailWord_3127969
  simp only [CollatzResearch.WordTrace]
  refine ⟨114086402004910002419314961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76057601336606668279543307 114086402004910002419314961)
  ·
    refine ⟨85564801503682501814486221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114086402004910002419314961 85564801503682501814486221)
    ·
      refine ⟨32086800563880938180432333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85564801503682501814486221 32086800563880938180432333)
      ·
        refine ⟨12032550211455351817662125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32086800563880938180432333 12032550211455351817662125)
        ·
          refine ⟨4512206329295756931623297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12032550211455351817662125 4512206329295756931623297)
          ·
            refine ⟨3384154746971817698717473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4512206329295756931623297 3384154746971817698717473)
            ·
              refine ⟨2538116060228863274038105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3384154746971817698717473 2538116060228863274038105)
              ·
                refine ⟨1903587045171647455528579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2538116060228863274038105 1903587045171647455528579)
                ·
                  refine ⟨2855380567757471183292869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903587045171647455528579 2855380567757471183292869)
                  ·
                    refine ⟨535383856454525846867413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2855380567757471183292869 535383856454525846867413)
                    ·
                      rfl

theorem cell23_3127969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_3127969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127969 prefixEnd_3127969 := by exact prefixLift 3127969
  have htrace : WordTrace (prefixWord ++ tailWord_3127969) baseStart_3127969 baseEnd_3127969 := by
    simpa [prefixWord, tailWord_3127969, baseEnd_3127969] using wordTrace_append hprefix tailTrace_3127969
  have hstable : (prefixWord ++ tailWord_3127969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127969).length < 2 ^ (prefixWord ++ tailWord_3127969).sum := by decide
  have hdescent : baseEnd_3127969 < baseStart_3127969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127998 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_3127998 : Nat := 118140960795 + 3127998 * 2 ^ 59
def prefixEnd_3127998 : Nat := 4983230072969 + 3 ^ 40 * 3127998 * 2
def baseEnd_3127998 : Nat := 1606166460302557927139605

theorem tailTrace_3127998 : CollatzResearch.WordTrace tailWord_3127998 prefixEnd_3127998 1606166460302557927139605 := by
  unfold tailWord_3127998
  simp only [CollatzResearch.WordTrace]
  refine ⟨14260932465225617546515081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76058306481203293581413765 14260932465225617546515081)
  ·
    refine ⟨10695699348919213159886311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14260932465225617546515081 10695699348919213159886311)
    ·
      refine ⟨16043549023378819739829467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10695699348919213159886311 16043549023378819739829467)
      ·
        refine ⟨24065323535068229609744201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16043549023378819739829467 24065323535068229609744201)
        ·
          refine ⟨18048992651301172207308151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24065323535068229609744201 18048992651301172207308151)
          ·
            refine ⟨27073488976951758310962227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18048992651301172207308151 27073488976951758310962227)
            ·
              refine ⟨40610233465427637466443341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27073488976951758310962227 40610233465427637466443341)
              ·
                refine ⟨15228837549535364049916253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40610233465427637466443341 15228837549535364049916253)
                ·
                  refine ⟨5710814081075761518718595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15228837549535364049916253 5710814081075761518718595)
                  ·
                    refine ⟨8566221121613642278077893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5710814081075761518718595 8566221121613642278077893)
                    ·
                      refine ⟨1606166460302557927139605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8566221121613642278077893 1606166460302557927139605)
                      ·
                        rfl

theorem cell23_3127998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_3127998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127998 prefixEnd_3127998 := by exact prefixLift 3127998
  have htrace : WordTrace (prefixWord ++ tailWord_3127998) baseStart_3127998 baseEnd_3127998 := by
    simpa [prefixWord, tailWord_3127998, baseEnd_3127998] using wordTrace_append hprefix tailTrace_3127998
  have hstable : (prefixWord ++ tailWord_3127998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127998).length < 2 ^ (prefixWord ++ tailWord_3127998).sum := by decide
  have hdescent : baseEnd_3127998 < baseStart_3127998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128012 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 1, 5]
def baseStart_3128012 : Nat := 118140960795 + 3128012 * 2 ^ 59
def prefixEnd_3128012 : Nat := 4983230072969 + 3 ^ 40 * 3128012 * 2
def baseEnd_3128012 : Nat := 535391216343906957454847

theorem tailTrace_3128012 : CollatzResearch.WordTrace tailWord_3128012 prefixEnd_3128012 535391216343906957454847 := by
  unfold tailWord_3128012
  simp only [CollatzResearch.WordTrace]
  refine ⟨57043985171877110381565145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76058646895836147175420193 57043985171877110381565145)
  ·
    refine ⟨42782988878907832786173859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57043985171877110381565145 42782988878907832786173859)
    ·
      refine ⟨64174483318361749179260789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42782988878907832786173859 64174483318361749179260789)
      ·
        refine ⟨6016357811096413985555699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64174483318361749179260789 6016357811096413985555699)
        ·
          refine ⟨9024536716644620978333549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6016357811096413985555699 9024536716644620978333549)
          ·
            refine ⟨3384201268741732866875081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9024536716644620978333549 3384201268741732866875081)
            ·
              refine ⟨2538150951556299650156311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3384201268741732866875081 2538150951556299650156311)
              ·
                refine ⟨3807226427334449475234467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2538150951556299650156311 3807226427334449475234467)
                ·
                  refine ⟨5710839641001674212851701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807226427334449475234467 5710839641001674212851701)
                  ·
                    refine ⟨535391216343906957454847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5710839641001674212851701 535391216343906957454847)
                    ·
                      rfl

theorem cell23_3128012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_3128012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128012 prefixEnd_3128012 := by exact prefixLift 3128012
  have htrace : WordTrace (prefixWord ++ tailWord_3128012) baseStart_3128012 baseEnd_3128012 := by
    simpa [prefixWord, tailWord_3128012, baseEnd_3128012] using wordTrace_append hprefix tailTrace_3128012
  have hstable : (prefixWord ++ tailWord_3128012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128012).length < 2 ^ (prefixWord ++ tailWord_3128012).sum := by decide
  have hdescent : baseEnd_3128012 < baseStart_3128012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128061 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_3128061 : Nat := 118140960795 + 3128061 * 2 ^ 59
def prefixEnd_3128061 : Nat := 4983230072969 + 3 ^ 40 * 3128061 * 2
def baseEnd_3128061 : Nat := 1606198809583791180651815

theorem tailTrace_3128061 : CollatzResearch.WordTrace tailWord_3128061 prefixEnd_3128061 1606198809583791180651815 := by
  unfold tailWord_3128061
  simp only [CollatzResearch.WordTrace]
  refine ⟨114089757520576702131664037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76059838347051134754442691 114089757520576702131664037)
  ·
    refine ⟨21391829535108131649687007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114089757520576702131664037 21391829535108131649687007)
    ·
      refine ⟨32087744302662197474530511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21391829535108131649687007 32087744302662197474530511)
      ·
        refine ⟨48131616453993296211795767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32087744302662197474530511 48131616453993296211795767)
        ·
          refine ⟨72197424680989944317693651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48131616453993296211795767 72197424680989944317693651)
          ·
            refine ⟨108296137021484916476540477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72197424680989944317693651 108296137021484916476540477)
            ·
              refine ⟨40611051383056843678702679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108296137021484916476540477 40611051383056843678702679)
              ·
                refine ⟨60916577074585265518054019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40611051383056843678702679 60916577074585265518054019)
                ·
                  refine ⟨91374865611877898277081029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60916577074585265518054019 91374865611877898277081029)
                  ·
                    refine ⟨17132787302227105926952693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91374865611877898277081029 17132787302227105926952693)
                    ·
                      refine ⟨1606198809583791180651815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17132787302227105926952693 1606198809583791180651815)
                      ·
                        rfl

theorem cell23_3128061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_3128061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128061 prefixEnd_3128061 := by exact prefixLift 3128061
  have htrace : WordTrace (prefixWord ++ tailWord_3128061) baseStart_3128061 baseEnd_3128061 := by
    simpa [prefixWord, tailWord_3128061, baseEnd_3128061] using wordTrace_append hprefix tailTrace_3128061
  have hstable : (prefixWord ++ tailWord_3128061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128061).length < 2 ^ (prefixWord ++ tailWord_3128061).sum := by decide
  have hdescent : baseEnd_3128061 < baseStart_3128061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128066 : List Nat := [3, 4, 1, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_3128066 : Nat := 118140960795 + 3128066 * 2 ^ 59
def prefixEnd_3128066 : Nat := 4983230072969 + 3 ^ 40 * 3128066 * 2
def baseEnd_3128066 : Nat := 1606201376987063661089293

theorem tailTrace_3128066 : CollatzResearch.WordTrace tailWord_3128066 prefixEnd_3128066 1606201376987063661089293 := by
  unfold tailWord_3128066
  simp only [CollatzResearch.WordTrace]
  refine ⟨28522484971389646996399013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76059959923705725323730701 28522484971389646996399013)
  ·
    refine ⟨5347965932135558811824815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28522484971389646996399013 5347965932135558811824815)
    ·
      refine ⟨8021948898203338217737223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5347965932135558811824815 8021948898203338217737223)
      ·
        refine ⟨12032923347305007326605835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8021948898203338217737223 12032923347305007326605835)
        ·
          refine ⟨18049385020957510989908753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12032923347305007326605835 18049385020957510989908753)
          ·
            refine ⟨13537038765718133242431565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18049385020957510989908753 13537038765718133242431565)
            ·
              refine ⟨5076389537144299965911837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13537038765718133242431565 5076389537144299965911837)
              ·
                refine ⟨1903646076429112487216939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5076389537144299965911837 1903646076429112487216939)
                ·
                  refine ⟨2855469114643668730825409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903646076429112487216939 2855469114643668730825409)
                  ·
                    refine ⟨2141601835982751548119057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2855469114643668730825409 2141601835982751548119057)
                    ·
                      refine ⟨1606201376987063661089293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141601835982751548119057 1606201376987063661089293)
                      ·
                        rfl

theorem cell23_3128066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_3128066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128066 prefixEnd_3128066 := by exact prefixLift 3128066
  have htrace : WordTrace (prefixWord ++ tailWord_3128066) baseStart_3128066 baseEnd_3128066 := by
    simpa [prefixWord, tailWord_3128066, baseEnd_3128066] using wordTrace_append hprefix tailTrace_3128066
  have hstable : (prefixWord ++ tailWord_3128066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128066).length < 2 ^ (prefixWord ++ tailWord_3128066).sum := by decide
  have hdescent : baseEnd_3128066 < baseStart_3128066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128081 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 4, 6]
def baseStart_3128081 : Nat := 118140960795 + 3128081 * 2 ^ 59
def prefixEnd_3128081 : Nat := 4983230072969 + 3 ^ 40 * 3128081 * 2
def baseEnd_3128081 : Nat := 535403026398960367467241

theorem tailTrace_3128081 : CollatzResearch.WordTrace tailWord_3128081 prefixEnd_3128081 535403026398960367467241 := by
  unfold tailWord_3128081
  simp only [CollatzResearch.WordTrace]
  refine ⟨114090486980504245547392097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76060324653669497031594731 114090486980504245547392097)
  ·
    refine ⟨85567865235378184160544073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114090486980504245547392097 85567865235378184160544073)
    ·
      refine ⟨64175898926533638120408055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85567865235378184160544073 64175898926533638120408055)
      ·
        refine ⟨96263848389800457180612083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64175898926533638120408055 96263848389800457180612083)
        ·
          refine ⟨144395772584700685770918125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96263848389800457180612083 144395772584700685770918125)
          ·
            refine ⟨54148414719262757164094297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144395772584700685770918125 54148414719262757164094297)
            ·
              refine ⟨40611311039447067873070723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54148414719262757164094297 40611311039447067873070723)
              ·
                refine ⟨60916966559170601809606085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40611311039447067873070723 60916966559170601809606085)
                ·
                  refine ⟨11421931229844487839301141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60916966559170601809606085 11421931229844487839301141)
                  ·
                    refine ⟨535403026398960367467241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11421931229844487839301141 535403026398960367467241)
                    ·
                      rfl

theorem cell23_3128081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_3128081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128081 prefixEnd_3128081 := by exact prefixLift 3128081
  have htrace : WordTrace (prefixWord ++ tailWord_3128081) baseStart_3128081 baseEnd_3128081 := by
    simpa [prefixWord, tailWord_3128081, baseEnd_3128081] using wordTrace_append hprefix tailTrace_3128081
  have hstable : (prefixWord ++ tailWord_3128081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128081).length < 2 ^ (prefixWord ++ tailWord_3128081).sum := by decide
  have hdescent : baseEnd_3128081 < baseStart_3128081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128091 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 5]
def baseStart_3128091 : Nat := 118140960795 + 3128091 * 2 ^ 59
def prefixEnd_3128091 : Nat := 4983230072969 + 3 ^ 40 * 3128091 * 2
def baseEnd_3128091 : Nat := 1606214214003426063276677

theorem tailTrace_3128091 : CollatzResearch.WordTrace tailWord_3128091 prefixEnd_3128091 1606214214003426063276677 := by
  unfold tailWord_3128091
  simp only [CollatzResearch.WordTrace]
  refine ⟨114090851710468017255256127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76060567806978678170170751 114090851710468017255256127)
  ·
    refine ⟨171136277565702025882884191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114090851710468017255256127 171136277565702025882884191)
    ·
      refine ⟨256704416348553038824326287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171136277565702025882884191 256704416348553038824326287)
      ·
        refine ⟨385056624522829558236489431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256704416348553038824326287 385056624522829558236489431)
        ·
          refine ⟨577584936784244337354734147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385056624522829558236489431 577584936784244337354734147)
          ·
            refine ⟨866377405176366506032101221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577584936784244337354734147 866377405176366506032101221)
            ·
              refine ⟨162445763470568719881018979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 866377405176366506032101221 162445763470568719881018979)
              ·
                refine ⟨243668645205853079821528469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162445763470568719881018979 243668645205853079821528469)
                ·
                  refine ⟨11421967744024363116634147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 243668645205853079821528469 11421967744024363116634147)
                  ·
                    refine ⟨17132951616036544674951221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11421967744024363116634147 17132951616036544674951221)
                    ·
                      refine ⟨1606214214003426063276677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17132951616036544674951221 1606214214003426063276677)
                      ·
                        rfl

theorem cell23_3128091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 5].length) (baseStart_3128091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128091 prefixEnd_3128091 := by exact prefixLift 3128091
  have htrace : WordTrace (prefixWord ++ tailWord_3128091) baseStart_3128091 baseEnd_3128091 := by
    simpa [prefixWord, tailWord_3128091, baseEnd_3128091] using wordTrace_append hprefix tailTrace_3128091
  have hstable : (prefixWord ++ tailWord_3128091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128091).length < 2 ^ (prefixWord ++ tailWord_3128091).sum := by decide
  have hdescent : baseEnd_3128091 < baseStart_3128091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128122 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2]
def baseStart_3128122 : Nat := 118140960795 + 3128122 * 2 ^ 59
def prefixEnd_3128122 : Nat := 4983230072969 + 3 ^ 40 * 3128122 * 2
def baseEnd_3128122 : Nat := 1606230131903715441989035

theorem tailTrace_3128122 : CollatzResearch.WordTrace tailWord_3128122 prefixEnd_3128122 1606230131903715441989035 := by
  unfold tailWord_3128122
  simp only [CollatzResearch.WordTrace]
  refine ⟨28522995593338927387408655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76061321582237139699756413 28522995593338927387408655)
  ·
    refine ⟨42784493390008391081112983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28522995593338927387408655 42784493390008391081112983)
    ·
      refine ⟨64176740085012586621669475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42784493390008391081112983 64176740085012586621669475)
      ·
        refine ⟨96265110127518879932504213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64176740085012586621669475 96265110127518879932504213)
        ·
          refine ⟨4512427037227447496836135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96265110127518879932504213 4512427037227447496836135)
          ·
            refine ⟨6768640555841171245254203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512427037227447496836135 6768640555841171245254203)
            ·
              refine ⟨10152960833761756867881305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6768640555841171245254203 10152960833761756867881305)
              ·
                refine ⟨7614720625321317650910979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10152960833761756867881305 7614720625321317650910979)
                ·
                  refine ⟨11422080937981976476366469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7614720625321317650910979 11422080937981976476366469)
                  ·
                    refine ⟨2141640175871620589318713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11422080937981976476366469 2141640175871620589318713)
                    ·
                      refine ⟨1606230131903715441989035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141640175871620589318713 1606230131903715441989035)
                      ·
                        rfl

theorem cell23_3128122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2].length) (baseStart_3128122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128122 prefixEnd_3128122 := by exact prefixLift 3128122
  have htrace : WordTrace (prefixWord ++ tailWord_3128122) baseStart_3128122 baseEnd_3128122 := by
    simpa [prefixWord, tailWord_3128122, baseEnd_3128122] using wordTrace_append hprefix tailTrace_3128122
  have hstable : (prefixWord ++ tailWord_3128122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128122).length < 2 ^ (prefixWord ++ tailWord_3128122).sum := by decide
  have hdescent : baseEnd_3128122 < baseStart_3128122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128126 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_3128126 : Nat := 118140960795 + 3128126 * 2 ^ 59
def prefixEnd_3128126 : Nat := 4983230072969 + 3 ^ 40 * 3128126 * 2
def baseEnd_3128126 : Nat := 1606232185826333426339017

theorem tailTrace_3128126 : CollatzResearch.WordTrace tailWord_3128126 prefixEnd_3128126 1606232185826333426339017 := by
  unfold tailWord_3128126
  simp only [CollatzResearch.WordTrace]
  refine ⟨14261516033167652279097529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76061418843560812155186821 14261516033167652279097529)
  ·
    refine ⟨10696137024875739209323147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14261516033167652279097529 10696137024875739209323147)
    ·
      refine ⟨16044205537313608813984721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10696137024875739209323147 16044205537313608813984721)
      ·
        refine ⟨12033154152985206610488541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16044205537313608813984721 12033154152985206610488541)
        ·
          refine ⟨4512432807369452478933203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12033154152985206610488541 4512432807369452478933203)
          ·
            refine ⟨6768649211054178718399805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512432807369452478933203 6768649211054178718399805)
            ·
              refine ⟨2538243454145317019399927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6768649211054178718399805 2538243454145317019399927)
              ·
                refine ⟨3807365181217975529099891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2538243454145317019399927 3807365181217975529099891)
                ·
                  refine ⟨5711047771826963293649837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807365181217975529099891 5711047771826963293649837)
                  ·
                    refine ⟨2141642914435111235118689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5711047771826963293649837 2141642914435111235118689)
                    ·
                      refine ⟨1606232185826333426339017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141642914435111235118689 1606232185826333426339017)
                      ·
                        rfl

theorem cell23_3128126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_3128126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128126 prefixEnd_3128126 := by exact prefixLift 3128126
  have htrace : WordTrace (prefixWord ++ tailWord_3128126) baseStart_3128126 baseEnd_3128126 := by
    simpa [prefixWord, tailWord_3128126, baseEnd_3128126] using wordTrace_append hprefix tailTrace_3128126
  have hstable : (prefixWord ++ tailWord_3128126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128126).length < 2 ^ (prefixWord ++ tailWord_3128126).sum := by decide
  have hdescent : baseEnd_3128126 < baseStart_3128126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128190 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_3128190 : Nat := 118140960795 + 3128190 * 2 ^ 59
def prefixEnd_3128190 : Nat := 4983230072969 + 3 ^ 40 * 3128190 * 2
def baseEnd_3128190 : Nat := 1606265048588221175938723

theorem tailTrace_3128190 : CollatzResearch.WordTrace tailWord_3128190 prefixEnd_3128190 1606265048588221175938723 := by
  unfold tailWord_3128190
  simp only [CollatzResearch.WordTrace]
  refine ⟨14261807817138669645388753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76062975024739571442073349 14261807817138669645388753)
  ·
    refine ⟨10696355862854002234041565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14261807817138669645388753 10696355862854002234041565)
    ·
      refine ⟨4011133448570250837765587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10696355862854002234041565 4011133448570250837765587)
      ·
        refine ⟨6016700172855376256648381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4011133448570250837765587 6016700172855376256648381)
        ·
          refine ⟨2256262564820766096243143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6016700172855376256648381 2256262564820766096243143)
          ·
            refine ⟨3384393847231149144364715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256262564820766096243143 3384393847231149144364715)
            ·
              refine ⟨5076590770846723716547073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384393847231149144364715 5076590770846723716547073)
              ·
                refine ⟨3807443078135042787410305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5076590770846723716547073 3807443078135042787410305)
                ·
                  refine ⟨2855582308601282090557729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3807443078135042787410305 2855582308601282090557729)
                  ·
                    refine ⟨2141686731450961567918297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2855582308601282090557729 2141686731450961567918297)
                    ·
                      refine ⟨1606265048588221175938723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141686731450961567918297 1606265048588221175938723)
                      ·
                        rfl

theorem cell23_3128190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_3128190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128190 prefixEnd_3128190 := by exact prefixLift 3128190
  have htrace : WordTrace (prefixWord ++ tailWord_3128190) baseStart_3128190 baseEnd_3128190 := by
    simpa [prefixWord, tailWord_3128190, baseEnd_3128190] using wordTrace_append hprefix tailTrace_3128190
  have hstable : (prefixWord ++ tailWord_3128190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128190).length < 2 ^ (prefixWord ++ tailWord_3128190).sum := by decide
  have hdescent : baseEnd_3128190 < baseStart_3128190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128195 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 4, 4, 2]
def baseStart_3128195 : Nat := 118140960795 + 3128195 * 2 ^ 59
def prefixEnd_3128195 : Nat := 4983230072969 + 3 ^ 40 * 3128195 * 2
def baseEnd_3128195 : Nat := 1606267615991493656376199

theorem tailTrace_3128195 : CollatzResearch.WordTrace tailWord_3128195 prefixEnd_3128195 1606267615991493656376199 := by
  unfold tailWord_3128195
  simp only [CollatzResearch.WordTrace]
  refine ⟨114094644902091243017042039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76063096601394162011361359 114094644902091243017042039)
  ·
    refine ⟨171141967353136864525563059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114094644902091243017042039 171141967353136864525563059)
    ·
      refine ⟨256712951029705296788344589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171141967353136864525563059 256712951029705296788344589)
      ·
        refine ⟨96267356636139486295629221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256712951029705296788344589 96267356636139486295629221)
        ·
          refine ⟨18050129369276153680430479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96267356636139486295629221 18050129369276153680430479)
          ·
            refine ⟨27075194053914230520645719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18050129369276153680430479 27075194053914230520645719)
            ·
              refine ⟨40612791080871345780968579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27075194053914230520645719 40612791080871345780968579)
              ·
                refine ⟨60919186621307018671452869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40612791080871345780968579 60919186621307018671452869)
                ·
                  refine ⟨11422347491495066000897413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60919186621307018671452869 11422347491495066000897413)
                  ·
                    refine ⟨2141690154655324875168265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11422347491495066000897413 2141690154655324875168265)
                    ·
                      refine ⟨1606267615991493656376199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141690154655324875168265 1606267615991493656376199)
                      ·
                        rfl

theorem cell23_3128195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 4, 2].length) (baseStart_3128195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128195 prefixEnd_3128195 := by exact prefixLift 3128195
  have htrace : WordTrace (prefixWord ++ tailWord_3128195) baseStart_3128195 baseEnd_3128195 := by
    simpa [prefixWord, tailWord_3128195, baseEnd_3128195] using wordTrace_append hprefix tailTrace_3128195
  have hstable : (prefixWord ++ tailWord_3128195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128195).length < 2 ^ (prefixWord ++ tailWord_3128195).sum := by decide
  have hdescent : baseEnd_3128195 < baseStart_3128195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128212 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_3128212 : Nat := 118140960795 + 3128212 * 2 ^ 59
def prefixEnd_3128212 : Nat := 4983230072969 + 3 ^ 40 * 3128212 * 2
def baseEnd_3128212 : Nat := 1606276345162620089863621

theorem tailTrace_3128212 : CollatzResearch.WordTrace tailWord_3128212 prefixEnd_3128212 1606276345162620089863621 := by
  unfold tailWord_3128212
  simp only [CollatzResearch.WordTrace]
  refine ⟨57047632471514827460205445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76063509962019769946940593 57047632471514827460205445)
  ·
    refine ⟨10696431088409030148788521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57047632471514827460205445 10696431088409030148788521)
    ·
      refine ⟨8022323316306772611591391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10696431088409030148788521 8022323316306772611591391)
      ·
        refine ⟨12033484974460158917387087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8022323316306772611591391 12033484974460158917387087)
        ·
          refine ⟨18050227461690238376080631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12033484974460158917387087 18050227461690238376080631)
          ·
            refine ⟨27075341192535357564120947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18050227461690238376080631 27075341192535357564120947)
            ·
              refine ⟨40613011788803036346181421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27075341192535357564120947 40613011788803036346181421)
              ·
                refine ⟨15229879420801138629818033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40613011788803036346181421 15229879420801138629818033)
                ·
                  refine ⟨11422409565600853972363525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15229879420801138629818033 11422409565600853972363525)
                  ·
                    refine ⟨2141701793550160119818161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11422409565600853972363525 2141701793550160119818161)
                    ·
                      refine ⟨1606276345162620089863621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141701793550160119818161 1606276345162620089863621)
                      ·
                        rfl

theorem cell23_3128212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_3128212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128212 prefixEnd_3128212 := by exact prefixLift 3128212
  have htrace : WordTrace (prefixWord ++ tailWord_3128212) baseStart_3128212 baseEnd_3128212 := by
    simpa [prefixWord, tailWord_3128212, baseEnd_3128212] using wordTrace_append hprefix tailTrace_3128212
  have hstable : (prefixWord ++ tailWord_3128212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128212).length < 2 ^ (prefixWord ++ tailWord_3128212).sum := by decide
  have hdescent : baseEnd_3128212 < baseStart_3128212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128255 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 3, 5, 2]
def baseStart_3128255 : Nat := 118140960795 + 3128255 * 2 ^ 59
def prefixEnd_3128255 : Nat := 4983230072969 + 3 ^ 40 * 3128255 * 2
def baseEnd_3128255 : Nat := 1606298424830763421625923

theorem tailTrace_3128255 : CollatzResearch.WordTrace tailWord_3128255 prefixEnd_3128255 1606298424830763421625923 := by
  unfold tailWord_3128255
  simp only [CollatzResearch.WordTrace]
  refine ⟨114096833281873873264226219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76064555521249248842817479 114096833281873873264226219)
  ·
    refine ⟨171145249922810809896339329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114096833281873873264226219 171145249922810809896339329)
    ·
      refine ⟨128358937442108107422254497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171145249922810809896339329 128358937442108107422254497)
      ·
        refine ⟨96269203081581080566690873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128358937442108107422254497 96269203081581080566690873)
        ·
          refine ⟨72201902311185810425018155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96269203081581080566690873 72201902311185810425018155)
          ·
            refine ⟨108302853466778715637527233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72201902311185810425018155 108302853466778715637527233)
            ·
              refine ⟨81227140100084036728145425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108302853466778715637527233 81227140100084036728145425)
              ·
                refine ⟨60920355075063027546109069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81227140100084036728145425 60920355075063027546109069)
                ·
                  refine ⟨22845133153148635329790901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60920355075063027546109069 22845133153148635329790901)
                  ·
                    refine ⟨2141731233107684562167897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22845133153148635329790901 2141731233107684562167897)
                    ·
                      refine ⟨1606298424830763421625923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141731233107684562167897 1606298424830763421625923)
                      ·
                        rfl

theorem cell23_3128255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 5, 2].length) (baseStart_3128255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128255 prefixEnd_3128255 := by exact prefixLift 3128255
  have htrace : WordTrace (prefixWord ++ tailWord_3128255) baseStart_3128255 baseEnd_3128255 := by
    simpa [prefixWord, tailWord_3128255, baseEnd_3128255] using wordTrace_append hprefix tailTrace_3128255
  have hstable : (prefixWord ++ tailWord_3128255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128255).length < 2 ^ (prefixWord ++ tailWord_3128255).sum := by decide
  have hdescent : baseEnd_3128255 < baseStart_3128255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128282 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 1, 5]
def baseStart_3128282 : Nat := 118140960795 + 3128282 * 2 ^ 59
def prefixEnd_3128282 : Nat := 4983230072969 + 3 ^ 40 * 3128282 * 2
def baseEnd_3128282 : Nat := 535437429602811605329433

theorem tailTrace_3128282 : CollatzResearch.WordTrace tailWord_3128282 prefixEnd_3128282 535437429602811605329433 := by
  unfold tailWord_3128282
  simp only [CollatzResearch.WordTrace]
  refine ⟨28524454513194014218864775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76065212035184037916972733 28524454513194014218864775)
  ·
    refine ⟨42786681769791021328297163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28524454513194014218864775 42786681769791021328297163)
    ·
      refine ⟨64180022654686531992445745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42786681769791021328297163 64180022654686531992445745)
      ·
        refine ⟨48135016991014898994334309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64180022654686531992445745 48135016991014898994334309)
        ·
          refine ⟨9025315685815293561437683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48135016991014898994334309 9025315685815293561437683)
          ·
            refine ⟨13537973528722940342156525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025315685815293561437683 13537973528722940342156525)
            ·
              refine ⟨5076740073271102628308697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13537973528722940342156525 5076740073271102628308697)
              ·
                refine ⟨3807555054953326971231523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5076740073271102628308697 3807555054953326971231523)
                ·
                  refine ⟨5711332582429990456847285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807555054953326971231523 5711332582429990456847285)
                  ·
                    refine ⟨535437429602811605329433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5711332582429990456847285 535437429602811605329433)
                    ·
                      rfl

theorem cell23_3128282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_3128282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128282 prefixEnd_3128282 := by exact prefixLift 3128282
  have htrace : WordTrace (prefixWord ++ tailWord_3128282) baseStart_3128282 baseEnd_3128282 := by
    simpa [prefixWord, tailWord_3128282, baseEnd_3128282] using wordTrace_append hprefix tailTrace_3128282
  have hstable : (prefixWord ++ tailWord_3128282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128282).length < 2 ^ (prefixWord ++ tailWord_3128282).sum := by decide
  have hdescent : baseEnd_3128282 < baseStart_3128282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128288 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_3128288 : Nat := 118140960795 + 3128288 * 2 ^ 59
def prefixEnd_3128288 : Nat := 4983230072969 + 3 ^ 40 * 3128288 * 2
def baseEnd_3128288 : Nat := 1606315369692361792513271

theorem tailTrace_3128288 : CollatzResearch.WordTrace tailWord_3128288 prefixEnd_3128288 1606315369692361792513271 := by
  unfold tailWord_3128288
  simp only [CollatzResearch.WordTrace]
  refine ⟨57049018445377159950088759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76065357927169546600118345 57049018445377159950088759)
  ·
    refine ⟨85573527668065739925133139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57049018445377159950088759 85573527668065739925133139)
    ·
      refine ⟨128360291502098609887699709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85573527668065739925133139 128360291502098609887699709)
      ·
        refine ⟨48135109313286978707887391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128360291502098609887699709 48135109313286978707887391)
        ·
          refine ⟨72202663969930468061831087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48135109313286978707887391 72202663969930468061831087)
          ·
            refine ⟨108303995954895702092746631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72202663969930468061831087 108303995954895702092746631)
            ·
              refine ⟨162455993932343553139119947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108303995954895702092746631 162455993932343553139119947)
              ·
                refine ⟨243683990898515329708679921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162455993932343553139119947 243683990898515329708679921)
                ·
                  refine ⟨182762993173886497281509941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243683990898515329708679921 182762993173886497281509941)
                  ·
                    refine ⟨17134030610051859120141557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 182762993173886497281509941 17134030610051859120141557)
                    ·
                      refine ⟨1606315369692361792513271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17134030610051859120141557 1606315369692361792513271)
                      ·
                        rfl

theorem cell23_3128288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_3128288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128288 prefixEnd_3128288 := by exact prefixLift 3128288
  have htrace : WordTrace (prefixWord ++ tailWord_3128288) baseStart_3128288 baseEnd_3128288 := by
    simpa [prefixWord, tailWord_3128288, baseEnd_3128288] using wordTrace_append hprefix tailTrace_3128288
  have hstable : (prefixWord ++ tailWord_3128288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128288).length < 2 ^ (prefixWord ++ tailWord_3128288).sum := by decide
  have hdescent : baseEnd_3128288 < baseStart_3128288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128295 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 3, 6]
def baseStart_3128295 : Nat := 118140960795 + 3128295 * 2 ^ 59
def prefixEnd_3128295 : Nat := 4983230072969 + 3 ^ 40 * 3128295 * 2
def baseEnd_3128295 : Nat := 535439654685647755041913

theorem tailTrace_3128295 : CollatzResearch.WordTrace tailWord_3128295 prefixEnd_3128295 535439654685647755041913 := by
  unfold tailWord_3128295
  simp only [CollatzResearch.WordTrace]
  refine ⟨114098292201728960095682339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76065528134485973397121559 114098292201728960095682339)
  ·
    refine ⟨171147438302593440143523509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114098292201728960095682339 171147438302593440143523509)
    ·
      refine ⟨16045072340868135013455329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171147438302593440143523509 16045072340868135013455329)
      ·
        refine ⟨12033804255651101260091497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16045072340868135013455329 12033804255651101260091497)
        ·
          refine ⟨9025353191738325945068623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12033804255651101260091497 9025353191738325945068623)
          ·
            refine ⟨13538029787607488917602935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025353191738325945068623 13538029787607488917602935)
            ·
              refine ⟨20307044681411233376404403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13538029787607488917602935 20307044681411233376404403)
              ·
                refine ⟨30460567022116850064606605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20307044681411233376404403 30460567022116850064606605)
                ·
                  refine ⟨11422712633293818774227477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30460567022116850064606605 11422712633293818774227477)
                  ·
                    refine ⟨535439654685647755041913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11422712633293818774227477 535439654685647755041913)
                    ·
                      rfl

theorem cell23_3128295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_3128295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128295 prefixEnd_3128295 := by exact prefixLift 3128295
  have htrace : WordTrace (prefixWord ++ tailWord_3128295) baseStart_3128295 baseEnd_3128295 := by
    simpa [prefixWord, tailWord_3128295, baseEnd_3128295] using wordTrace_append hprefix tailTrace_3128295
  have hstable : (prefixWord ++ tailWord_3128295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128295).length < 2 ^ (prefixWord ++ tailWord_3128295).sum := by decide
  have hdescent : baseEnd_3128295 < baseStart_3128295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128332 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 1, 2, 4]
def baseStart_3128332 : Nat := 118140960795 + 3128332 * 2 ^ 59
def prefixEnd_3128332 : Nat := 4983230072969 + 3 ^ 40 * 3128332 * 2
def baseEnd_3128332 : Nat := 1606337962841159620363069

theorem tailTrace_3128332 : CollatzResearch.WordTrace tailWord_3128332 prefixEnd_3128332 1606337962841159620363069 := by
  unfold tailWord_3128332
  simp only [CollatzResearch.WordTrace]
  refine ⟨57049820851297457707389625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76066427801729943609852833 57049820851297457707389625)
  ·
    refine ⟨42787365638473093280542219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57049820851297457707389625 42787365638473093280542219)
    ·
      refine ⟨64181048457709639920813329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42787365638473093280542219 64181048457709639920813329)
      ·
        refine ⟨48135786343282229940609997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64181048457709639920813329 48135786343282229940609997)
        ·
          refine ⟨18050919878730836227728749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48135786343282229940609997 18050919878730836227728749)
          ·
            refine ⟨6769094954524063585398281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18050919878730836227728749 6769094954524063585398281)
            ·
              refine ⟨5076821215893047689048711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6769094954524063585398281 5076821215893047689048711)
              ·
                refine ⟨7615231823839571533573067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5076821215893047689048711 7615231823839571533573067)
                ·
                  refine ⟨11422847735759357300359601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7615231823839571533573067 11422847735759357300359601)
                  ·
                    refine ⟨8567135801819517975269701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11422847735759357300359601 8567135801819517975269701)
                    ·
                      refine ⟨1606337962841159620363069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8567135801819517975269701 1606337962841159620363069)
                      ·
                        rfl

theorem cell23_3128332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_3128332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128332 prefixEnd_3128332 := by exact prefixLift 3128332
  have htrace : WordTrace (prefixWord ++ tailWord_3128332) baseStart_3128332 baseEnd_3128332 := by
    simpa [prefixWord, tailWord_3128332, baseEnd_3128332] using wordTrace_append hprefix tailTrace_3128332
  have hstable : (prefixWord ++ tailWord_3128332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128332).length < 2 ^ (prefixWord ++ tailWord_3128332).sum := by decide
  have hdescent : baseEnd_3128332 < baseStart_3128332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128353 : List Nat := [1, 2, 3, 2, 3, 2, 2, 3, 1, 2, 2]
def baseStart_3128353 : Nat := 118140960795 + 3128353 * 2 ^ 59
def prefixEnd_3128353 : Nat := 4983230072969 + 3 ^ 40 * 3128353 * 2
def baseEnd_3128353 : Nat := 1606348745934904038200473

theorem tailTrace_3128353 : CollatzResearch.WordTrace tailWord_3128353 prefixEnd_3128353 1606348745934904038200473 := by
  unfold tailWord_3128353
  simp only [CollatzResearch.WordTrace]
  refine ⟨114100407635518836001293713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76066938423679224000862475 114100407635518836001293713)
  ·
    refine ⟨85575305726639127000970285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114100407635518836001293713 85575305726639127000970285)
    ·
      refine ⟨32090739647489672625363857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85575305726639127000970285 32090739647489672625363857)
      ·
        refine ⟨24068054735617254469022893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32090739647489672625363857 24068054735617254469022893)
        ·
          refine ⟨9025520525856470425883585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24068054735617254469022893 9025520525856470425883585)
          ·
            refine ⟨6769140394392352819412689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9025520525856470425883585 6769140394392352819412689)
            ·
              refine ⟨5076855295794264614559517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6769140394392352819412689 5076855295794264614559517)
              ·
                refine ⟨1903820735922849230459819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5076855295794264614559517 1903820735922849230459819)
                ·
                  refine ⟨2855731103884273845689729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903820735922849230459819 2855731103884273845689729)
                  ·
                    refine ⟨2141798327913205384267297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2855731103884273845689729 2141798327913205384267297)
                    ·
                      refine ⟨1606348745934904038200473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141798327913205384267297 1606348745934904038200473)
                      ·
                        rfl

theorem cell23_3128353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_3128353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128353 prefixEnd_3128353 := by exact prefixLift 3128353
  have htrace : WordTrace (prefixWord ++ tailWord_3128353) baseStart_3128353 baseEnd_3128353 := by
    simpa [prefixWord, tailWord_3128353, baseEnd_3128353] using wordTrace_append hprefix tailTrace_3128353
  have hstable : (prefixWord ++ tailWord_3128353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128353).length < 2 ^ (prefixWord ++ tailWord_3128353).sum := by decide
  have hdescent : baseEnd_3128353 < baseStart_3128353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128356 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 1, 2, 3]
def baseStart_3128356 : Nat := 118140960795 + 3128356 * 2 ^ 59
def prefixEnd_3128356 : Nat := 4983230072969 + 3 ^ 40 * 3128356 * 2
def baseEnd_3128356 : Nat := 1606350286376867526462959

theorem tailTrace_3128356 : CollatzResearch.WordTrace tailWord_3128356 prefixEnd_3128356 1606350286376867526462959 := by
  unfold tailWord_3128356
  simp only [CollatzResearch.WordTrace]
  refine ⟨57050258527253983756826461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76067011369671978342435281 57050258527253983756826461)
  ·
    refine ⟨21393846947720243908809923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57050258527253983756826461 21393846947720243908809923)
    ·
      refine ⟨32090770421580365863214885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21393846947720243908809923 32090770421580365863214885)
      ·
        refine ⟨6017019454046318599352791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32090770421580365863214885 6017019454046318599352791)
        ·
          refine ⟨9025529181069477899029187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6017019454046318599352791 9025529181069477899029187)
          ·
            refine ⟨13538293771604216848543781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025529181069477899029187 13538293771604216848543781)
            ·
              refine ⟨2538430082175790659101959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13538293771604216848543781 2538430082175790659101959)
              ·
                refine ⟨3807645123263685988652939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2538430082175790659101959 3807645123263685988652939)
                ·
                  refine ⟨5711467684895528982979409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807645123263685988652939 5711467684895528982979409)
                  ·
                    refine ⟨4283600763671646737234557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5711467684895528982979409 4283600763671646737234557)
                    ·
                      refine ⟨1606350286376867526462959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4283600763671646737234557 1606350286376867526462959)
                      ·
                        rfl

theorem cell23_3128356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_3128356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128356 prefixEnd_3128356 := by exact prefixLift 3128356
  have htrace : WordTrace (prefixWord ++ tailWord_3128356) baseStart_3128356 baseEnd_3128356 := by
    simpa [prefixWord, tailWord_3128356, baseEnd_3128356] using wordTrace_append hprefix tailTrace_3128356
  have hstable : (prefixWord ++ tailWord_3128356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128356).length < 2 ^ (prefixWord ++ tailWord_3128356).sum := by decide
  have hdescent : baseEnd_3128356 < baseStart_3128356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128412 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3128412 : Nat := 118140960795 + 3128412 * 2 ^ 59
def prefixEnd_3128412 : Nat := 4983230072969 + 3 ^ 40 * 3128412 * 2
def baseEnd_3128412 : Nat := 1606379041293519307362701

theorem tailTrace_3128412 : CollatzResearch.WordTrace tailWord_3128412 prefixEnd_3128412 1606379041293519307362701 := by
  unfold tailWord_3128412
  simp only [CollatzResearch.WordTrace]
  refine ⟨57051279771152544538845745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76068373028203392718460993 57051279771152544538845745)
  ·
    refine ⟨42788459828364408404134309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57051279771152544538845745 42788459828364408404134309)
    ·
      refine ⟨8022836217818326575775183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42788459828364408404134309 8022836217818326575775183)
      ·
        refine ⟨12034254326727489863662775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8022836217818326575775183 12034254326727489863662775)
        ·
          refine ⟨18051381490091234795494163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12034254326727489863662775 18051381490091234795494163)
          ·
            refine ⟨27077072235136852193241245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18051381490091234795494163 27077072235136852193241245)
            ·
              refine ⟨10153902088176319572465467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27077072235136852193241245 10153902088176319572465467)
              ·
                refine ⟨15230853132264479358698201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10153902088176319572465467 15230853132264479358698201)
                ·
                  refine ⟨11423139849198359519023651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15230853132264479358698201 11423139849198359519023651)
                  ·
                    refine ⟨17134709773797539278535477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11423139849198359519023651 17134709773797539278535477)
                    ·
                      refine ⟨1606379041293519307362701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17134709773797539278535477 1606379041293519307362701)
                      ·
                        rfl

theorem cell23_3128412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3128412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128412 prefixEnd_3128412 := by exact prefixLift 3128412
  have htrace : WordTrace (prefixWord ++ tailWord_3128412) baseStart_3128412 baseEnd_3128412 := by
    simpa [prefixWord, tailWord_3128412, baseEnd_3128412] using wordTrace_append hprefix tailTrace_3128412
  have hstable : (prefixWord ++ tailWord_3128412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128412).length < 2 ^ (prefixWord ++ tailWord_3128412).sum := by decide
  have hdescent : baseEnd_3128412 < baseStart_3128412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128426 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_3128426 : Nat := 118140960795 + 3128426 * 2 ^ 59
def prefixEnd_3128426 : Nat := 4983230072969 + 3 ^ 40 * 3128426 * 2
def baseEnd_3128426 : Nat := 1606386230022682252587637

theorem tailTrace_3128426 : CollatzResearch.WordTrace tailWord_3128426 prefixEnd_3128426 1606386230022682252587637 := by
  unfold tailWord_3128426
  simp only [CollatzResearch.WordTrace]
  refine ⟨28525767541063592367175283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76068713442836246312467421 28525767541063592367175283)
  ·
    refine ⟨42788651311595388550762925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28525767541063592367175283 42788651311595388550762925)
    ·
      refine ⟨16045744241848270706536097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42788651311595388550762925 16045744241848270706536097)
      ·
        refine ⟨12034308181386203029902073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16045744241848270706536097 12034308181386203029902073)
        ·
          refine ⟨9025731136039652272426555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12034308181386203029902073 9025731136039652272426555)
          ·
            refine ⟨13538596704059478408639833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025731136039652272426555 13538596704059478408639833)
            ·
              refine ⟨10153947528044608806479875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13538596704059478408639833 10153947528044608806479875)
              ·
                refine ⟨15230921292066913209719813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10153947528044608806479875 15230921292066913209719813)
                ·
                  refine ⟨2855797742262546226822465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15230921292066913209719813 2855797742262546226822465)
                  ·
                    refine ⟨2141848306696909670116849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2855797742262546226822465 2141848306696909670116849)
                    ·
                      refine ⟨1606386230022682252587637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141848306696909670116849 1606386230022682252587637)
                      ·
                        rfl

theorem cell23_3128426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_3128426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128426 prefixEnd_3128426 := by exact prefixLift 3128426
  have htrace : WordTrace (prefixWord ++ tailWord_3128426) baseStart_3128426 baseEnd_3128426 := by
    simpa [prefixWord, tailWord_3128426, baseEnd_3128426] using wordTrace_append hprefix tailTrace_3128426
  have hstable : (prefixWord ++ tailWord_3128426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128426).length < 2 ^ (prefixWord ++ tailWord_3128426).sum := by decide
  have hdescent : baseEnd_3128426 < baseStart_3128426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128437 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3128437 : Nat := 118140960795 + 3128437 * 2 ^ 59
def prefixEnd_3128437 : Nat := 4983230072969 + 3 ^ 40 * 3128437 * 2
def baseEnd_3128437 : Nat := 1606391878309881709550087

theorem tailTrace_3128437 : CollatzResearch.WordTrace tailWord_3128437 prefixEnd_3128437 1606391878309881709550087 := by
  unfold tailWord_3128437
  simp only [CollatzResearch.WordTrace]
  refine ⟨114103471367214518347351565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76068980911476345564901043 114103471367214518347351565)
  ·
    refine ⟨42788801762705444380256837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114103471367214518347351565 42788801762705444380256837)
    ·
      refine ⟨8022900330507270821298157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42788801762705444380256837 8022900330507270821298157)
      ·
        refine ⟨3008587623940226557986809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8022900330507270821298157 3008587623940226557986809)
        ·
          refine ⟨2256440717955169918490107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3008587623940226557986809 2256440717955169918490107)
          ·
            refine ⟨3384661076932754877735161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256440717955169918490107 3384661076932754877735161)
            ·
              refine ⟨2538495807699566158301371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3384661076932754877735161 2538495807699566158301371)
              ·
                refine ⟨3807743711549349237452057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2538495807699566158301371 3807743711549349237452057)
                ·
                  refine ⟨2855807783662011928089043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3807743711549349237452057 2855807783662011928089043)
                  ·
                    refine ⟨4283711675493017892133565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2855807783662011928089043 4283711675493017892133565)
                    ·
                      refine ⟨1606391878309881709550087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4283711675493017892133565 1606391878309881709550087)
                      ·
                        rfl

theorem cell23_3128437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3128437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128437 prefixEnd_3128437 := by exact prefixLift 3128437
  have htrace : WordTrace (prefixWord ++ tailWord_3128437) baseStart_3128437 baseEnd_3128437 := by
    simpa [prefixWord, tailWord_3128437, baseEnd_3128437] using wordTrace_append hprefix tailTrace_3128437
  have hstable : (prefixWord ++ tailWord_3128437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128437).length < 2 ^ (prefixWord ++ tailWord_3128437).sum := by decide
  have hdescent : baseEnd_3128437 < baseStart_3128437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128455 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_3128455 : Nat := 118140960795 + 3128455 * 2 ^ 59
def prefixEnd_3128455 : Nat := 4983230072969 + 3 ^ 40 * 3128455 * 2
def baseEnd_3128455 : Nat := 1606401120961662639125003

theorem tailTrace_3128455 : CollatzResearch.WordTrace tailWord_3128455 prefixEnd_3128455 1606401120961662639125003 := by
  unfold tailWord_3128455
  simp only [CollatzResearch.WordTrace]
  refine ⟨114104127881149307421506819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76069418587432871614337879 114104127881149307421506819)
  ·
    refine ⟨171156191821723961132260229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114104127881149307421506819 171156191821723961132260229)
    ·
      refine ⟨32091785966573242712298793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171156191821723961132260229 32091785966573242712298793)
      ·
        refine ⟨24068839474929932034224095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32091785966573242712298793 24068839474929932034224095)
        ·
          refine ⟨36103259212394898051336143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24068839474929932034224095 36103259212394898051336143)
          ·
            refine ⟨54154888818592347077004215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36103259212394898051336143 54154888818592347077004215)
            ·
              refine ⟨81232333227888520615506323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54154888818592347077004215 81232333227888520615506323)
              ·
                refine ⟨121848499841832780923259485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81232333227888520615506323 121848499841832780923259485)
                ·
                  refine ⟨45693187440687292846222307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121848499841832780923259485 45693187440687292846222307)
                  ·
                    refine ⟨68539781161030939269333461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45693187440687292846222307 68539781161030939269333461)
                    ·
                      refine ⟨1606401120961662639125003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68539781161030939269333461 1606401120961662639125003)
                      ·
                        rfl

theorem cell23_3128455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_3128455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128455 prefixEnd_3128455 := by exact prefixLift 3128455
  have htrace : WordTrace (prefixWord ++ tailWord_3128455) baseStart_3128455 baseEnd_3128455 := by
    simpa [prefixWord, tailWord_3128455, baseEnd_3128455] using wordTrace_append hprefix tailTrace_3128455
  have hstable : (prefixWord ++ tailWord_3128455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128455).length < 2 ^ (prefixWord ++ tailWord_3128455).sum := by decide
  have hdescent : baseEnd_3128455 < baseStart_3128455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128472 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3128472 : Nat := 118140960795 + 3128472 * 2 ^ 59
def prefixEnd_3128472 : Nat := 4983230072969 + 3 ^ 40 * 3128472 * 2
def baseEnd_3128472 : Nat := 1606409850132789072612425

theorem tailTrace_3128472 : CollatzResearch.WordTrace tailWord_3128472 prefixEnd_3128472 1606409850132789072612425 := by
  unfold tailWord_3128472
  simp only [CollatzResearch.WordTrace]
  refine ⟨57052373961043859662437835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76069831948058479549917113 57052373961043859662437835)
  ·
    refine ⟨85578560941565789493656753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57052373961043859662437835 85578560941565789493656753)
    ·
      refine ⟨64183920706174342120242565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85578560941565789493656753 64183920706174342120242565)
      ·
        refine ⟨12034485132407689147545481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64183920706174342120242565 12034485132407689147545481)
        ·
          refine ⟨9025863849305766860659111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12034485132407689147545481 9025863849305766860659111)
          ·
            refine ⟨13538795773958650290988667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025863849305766860659111 13538795773958650290988667)
            ·
              refine ⟨20308193660937975436483001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13538795773958650290988667 20308193660937975436483001)
              ·
                refine ⟨15231145245703481577362251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20308193660937975436483001 15231145245703481577362251)
                ·
                  refine ⟨22846717868555222366043377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15231145245703481577362251 22846717868555222366043377)
                  ·
                    refine ⟨17135038401416416774532533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22846717868555222366043377 17135038401416416774532533)
                    ·
                      refine ⟨1606409850132789072612425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17135038401416416774532533 1606409850132789072612425)
                      ·
                        rfl

theorem cell23_3128472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3128472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128472 prefixEnd_3128472 := by exact prefixLift 3128472
  have htrace : WordTrace (prefixWord ++ tailWord_3128472) baseStart_3128472 baseEnd_3128472 := by
    simpa [prefixWord, tailWord_3128472, baseEnd_3128472] using wordTrace_append hprefix tailTrace_3128472
  have hstable : (prefixWord ++ tailWord_3128472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128472).length < 2 ^ (prefixWord ++ tailWord_3128472).sum := by decide
  have hdescent : baseEnd_3128472 < baseStart_3128472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128569 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 1, 5]
def baseStart_3128569 : Nat := 118140960795 + 3128569 * 2 ^ 59
def prefixEnd_3128569 : Nat := 4983230072969 + 3 ^ 40 * 3128569 * 2
def baseEnd_3128569 : Nat := 535486552585425064366493

theorem tailTrace_3128569 : CollatzResearch.WordTrace tailWord_3128569 prefixEnd_3128569 535486552585425064366493 := by
  unfold tailWord_3128569
  simp only [CollatzResearch.WordTrace]
  refine ⟨114108285802736304891156761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76072190535157536594104507 114108285802736304891156761)
  ·
    refine ⟨85581214352052228668367571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114108285802736304891156761 85581214352052228668367571)
    ·
      refine ⟨128371821528078343002551357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85581214352052228668367571 128371821528078343002551357)
      ·
        refine ⟨48139433073029378625956759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128371821528078343002551357 48139433073029378625956759)
        ·
          refine ⟨72209149609544067938935139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48139433073029378625956759 72209149609544067938935139)
          ·
            refine ⟨108313724414316101908402709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72209149609544067938935139 108313724414316101908402709)
            ·
              refine ⟨5077205831921067276956377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108313724414316101908402709 5077205831921067276956377)
              ·
                refine ⟨3807904373940800457717283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5077205831921067276956377 3807904373940800457717283)
                ·
                  refine ⟨5711856560911200686575925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807904373940800457717283 5711856560911200686575925)
                  ·
                    refine ⟨535486552585425064366493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5711856560911200686575925 535486552585425064366493)
                    ·
                      rfl

theorem cell23_3128569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 5].length) (baseStart_3128569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128569 prefixEnd_3128569 := by exact prefixLift 3128569
  have htrace : WordTrace (prefixWord ++ tailWord_3128569) baseStart_3128569 baseEnd_3128569 := by
    simpa [prefixWord, tailWord_3128569, baseEnd_3128569] using wordTrace_append hprefix tailTrace_3128569
  have hstable : (prefixWord ++ tailWord_3128569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128569).length < 2 ^ (prefixWord ++ tailWord_3128569).sum := by decide
  have hdescent : baseEnd_3128569 < baseStart_3128569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128592 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 3]
def baseStart_3128592 : Nat := 118140960795 + 3128592 * 2 ^ 59
def prefixEnd_3128592 : Nat := 4983230072969 + 3 ^ 40 * 3128592 * 2
def baseEnd_3128592 : Nat := 1606471467811328603111873

theorem tailTrace_3128592 : CollatzResearch.WordTrace tailWord_3128592 prefixEnd_3128592 1606471467811328603111873 := by
  unfold tailWord_3128592
  simp only [CollatzResearch.WordTrace]
  refine ⟨57054562340826489909622015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76072749787768653212829353 57054562340826489909622015)
  ·
    refine ⟨85581843511239734864433023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57054562340826489909622015 85581843511239734864433023)
    ·
      refine ⟨128372765266859602296649535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85581843511239734864433023 128372765266859602296649535)
      ·
        refine ⟨192559147900289403444974303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128372765266859602296649535 192559147900289403444974303)
        ·
          refine ⟨288838721850434105167461455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192559147900289403444974303 288838721850434105167461455)
          ·
            refine ⟨433258082775651157751192183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288838721850434105167461455 433258082775651157751192183)
            ·
              refine ⟨649887124163476736626788275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433258082775651157751192183 649887124163476736626788275)
              ·
                refine ⟨974830686245215104940182413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649887124163476736626788275 974830686245215104940182413)
                ·
                  refine ⟨365561507341955664352568405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974830686245215104940182413 365561507341955664352568405)
                  ·
                    refine ⟨4283923914163542941631661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 365561507341955664352568405 4283923914163542941631661)
                    ·
                      refine ⟨1606471467811328603111873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4283923914163542941631661 1606471467811328603111873)
                      ·
                        rfl

theorem cell23_3128592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 3].length) (baseStart_3128592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128592 prefixEnd_3128592 := by exact prefixLift 3128592
  have htrace : WordTrace (prefixWord ++ tailWord_3128592) baseStart_3128592 baseEnd_3128592 := by
    simpa [prefixWord, tailWord_3128592, baseEnd_3128592] using wordTrace_append hprefix tailTrace_3128592
  have hstable : (prefixWord ++ tailWord_3128592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128592).length < 2 ^ (prefixWord ++ tailWord_3128592).sum := by decide
  have hdescent : baseEnd_3128592 < baseStart_3128592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128599 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 4, 4]
def baseStart_3128599 : Nat := 118140960795 + 3128599 * 2 ^ 59
def prefixEnd_3128599 : Nat := 4983230072969 + 3 ^ 40 * 3128599 * 2
def baseEnd_3128599 : Nat := 535491687391970025241447

theorem tailTrace_3128599 : CollatzResearch.WordTrace tailWord_3128599 prefixEnd_3128599 535491687391970025241447 := by
  unfold tailWord_3128599
  simp only [CollatzResearch.WordTrace]
  refine ⟨114109379992627620014748851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76072919995085080009832567 114109379992627620014748851)
  ·
    refine ⟨171164069988941430022123277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114109379992627620014748851 171164069988941430022123277)
    ·
      refine ⟨64186526245853036258296229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171164069988941430022123277 64186526245853036258296229)
      ·
        refine ⟨12034973671097444298430543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64186526245853036258296229 12034973671097444298430543)
        ·
          refine ⟨18052460506646166447645815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12034973671097444298430543 18052460506646166447645815)
          ·
            refine ⟨27078690759969249671468723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18052460506646166447645815 27078690759969249671468723)
            ·
              refine ⟨40618036139953874507203085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27078690759969249671468723 40618036139953874507203085)
              ·
                refine ⟨15231763552482702940201157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40618036139953874507203085 15231763552482702940201157)
                ·
                  refine ⟨2855955666090506801287717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15231763552482702940201157 2855955666090506801287717)
                  ·
                    refine ⟨535491687391970025241447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2855955666090506801287717 535491687391970025241447)
                    ·
                      rfl

theorem cell23_3128599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_3128599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128599 prefixEnd_3128599 := by exact prefixLift 3128599
  have htrace : WordTrace (prefixWord ++ tailWord_3128599) baseStart_3128599 baseEnd_3128599 := by
    simpa [prefixWord, tailWord_3128599, baseEnd_3128599] using wordTrace_append hprefix tailTrace_3128599
  have hstable : (prefixWord ++ tailWord_3128599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128599).length < 2 ^ (prefixWord ++ tailWord_3128599).sum := by decide
  have hdescent : baseEnd_3128599 < baseStart_3128599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128600 : List Nat := [2, 1, 2, 3, 1, 4, 3, 2, 1, 1, 3]
def baseStart_3128600 : Nat := 118140960795 + 3128600 * 2 ^ 59
def prefixEnd_3128600 : Nat := 4983230072969 + 3 ^ 40 * 3128600 * 2
def baseEnd_3128600 : Nat := 1606475575656564571811837

theorem tailTrace_3128600 : CollatzResearch.WordTrace tailWord_3128600 prefixEnd_3128600 1606475575656564571811837 := by
  unfold tailWord_3128600
  simp only [CollatzResearch.WordTrace]
  refine ⟨57054708232811998592767627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76072944310415998123690169 57054708232811998592767627)
  ·
    refine ⟨85582062349217997889151441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57054708232811998592767627 85582062349217997889151441)
    ·
      refine ⟨64186546761913498416863581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85582062349217997889151441 64186546761913498416863581)
      ·
        refine ⟨24069955035717561906323843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64186546761913498416863581 24069955035717561906323843)
        ·
          refine ⟨36104932553576342859485765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24069955035717561906323843 36104932553576342859485765)
          ·
            refine ⟨6769674853795564286153581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36104932553576342859485765 6769674853795564286153581)
            ·
              refine ⟨2538628070173336607307593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6769674853795564286153581 2538628070173336607307593)
              ·
                refine ⟨1903971052630002455480695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2538628070173336607307593 1903971052630002455480695)
                ·
                  refine ⟨2855956578945003683221043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903971052630002455480695 2855956578945003683221043)
                  ·
                    refine ⟨4283934868417505524831565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2855956578945003683221043 4283934868417505524831565)
                    ·
                      refine ⟨1606475575656564571811837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4283934868417505524831565 1606475575656564571811837)
                      ·
                        rfl

theorem cell23_3128600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_3128600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128600 prefixEnd_3128600 := by exact prefixLift 3128600
  have htrace : WordTrace (prefixWord ++ tailWord_3128600) baseStart_3128600 baseEnd_3128600 := by
    simpa [prefixWord, tailWord_3128600, baseEnd_3128600] using wordTrace_append hprefix tailTrace_3128600
  have hstable : (prefixWord ++ tailWord_3128600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128600).length < 2 ^ (prefixWord ++ tailWord_3128600).sum := by decide
  have hdescent : baseEnd_3128600 < baseStart_3128600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128609 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_3128609 : Nat := 118140960795 + 3128609 * 2 ^ 59
def prefixEnd_3128609 : Nat := 4983230072969 + 3 ^ 40 * 3128609 * 2
def baseEnd_3128609 : Nat := 1606480196982455036599295

theorem tailTrace_3128609 : CollatzResearch.WordTrace tailWord_3128609 prefixEnd_3128609 1606480196982455036599295 := by
  unfold tailWord_3128609
  simp only [CollatzResearch.WordTrace]
  refine ⟨114109744722591391722612881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76073163148394261148408587 114109744722591391722612881)
  ·
    refine ⟨85582308541943543791959661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114109744722591391722612881 85582308541943543791959661)
    ·
      refine ⟨32093365703228828921984873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85582308541943543791959661 32093365703228828921984873)
      ·
        refine ⟨24070024277421621691488655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32093365703228828921984873 24070024277421621691488655)
        ·
          refine ⟨36105036416132432537232983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24070024277421621691488655 36105036416132432537232983)
          ·
            refine ⟨54157554624198648805849475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36105036416132432537232983 54157554624198648805849475)
            ·
              refine ⟨81236331936297973208774213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54157554624198648805849475 81236331936297973208774213)
              ·
                refine ⟨15231812238055869976645165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81236331936297973208774213 15231812238055869976645165)
                ·
                  refine ⟨5711929589270951241241937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15231812238055869976645165 5711929589270951241241937)
                  ·
                    refine ⟨4283947191953213430931453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5711929589270951241241937 4283947191953213430931453)
                    ·
                      refine ⟨1606480196982455036599295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4283947191953213430931453 1606480196982455036599295)
                      ·
                        rfl

theorem cell23_3128609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_3128609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128609 prefixEnd_3128609 := by exact prefixLift 3128609
  have htrace : WordTrace (prefixWord ++ tailWord_3128609) baseStart_3128609 baseEnd_3128609 := by
    simpa [prefixWord, tailWord_3128609, baseEnd_3128609] using wordTrace_append hprefix tailTrace_3128609
  have hstable : (prefixWord ++ tailWord_3128609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128609).length < 2 ^ (prefixWord ++ tailWord_3128609).sum := by decide
  have hdescent : baseEnd_3128609 < baseStart_3128609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128626 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_3128626 : Nat := 118140960795 + 3128626 * 2 ^ 59
def prefixEnd_3128626 : Nat := 4983230072969 + 3 ^ 40 * 3128626 * 2
def baseEnd_3128626 : Nat := 1606488926153581470086717

theorem tailTrace_3128626 : CollatzResearch.WordTrace tailWord_3128626 prefixEnd_3128626 1606488926153581470086717 := by
  unfold tailWord_3128626
  simp only [CollatzResearch.WordTrace]
  refine ⟨28527591190882450906495433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76073576509019869083987821 28527591190882450906495433)
  ·
    refine ⟨21395693393161838179871575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28527591190882450906495433 21395693393161838179871575)
    ·
      refine ⟨32093540089742757269807363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21395693393161838179871575 32093540089742757269807363)
      ·
        refine ⟨48140310134614135904711045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32093540089742757269807363 48140310134614135904711045)
        ·
          refine ⟨9026308150240150482133321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48140310134614135904711045 9026308150240150482133321)
          ·
            refine ⟨6769731112680112861599991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9026308150240150482133321 6769731112680112861599991)
            ·
              refine ⟨10154596669020169292399987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6769731112680112861599991 10154596669020169292399987)
              ·
                refine ⟨15231895003530253938599981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10154596669020169292399987 15231895003530253938599981)
                ·
                  refine ⟨5711960626323845226974993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15231895003530253938599981 5711960626323845226974993)
                  ·
                    refine ⟨4283970469742883920231245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5711960626323845226974993 4283970469742883920231245)
                    ·
                      refine ⟨1606488926153581470086717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4283970469742883920231245 1606488926153581470086717)
                      ·
                        rfl

theorem cell23_3128626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_3128626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128626 prefixEnd_3128626 := by exact prefixLift 3128626
  have htrace : WordTrace (prefixWord ++ tailWord_3128626) baseStart_3128626 baseEnd_3128626 := by
    simpa [prefixWord, tailWord_3128626, baseEnd_3128626] using wordTrace_append hprefix tailTrace_3128626
  have hstable : (prefixWord ++ tailWord_3128626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128626).length < 2 ^ (prefixWord ++ tailWord_3128626).sum := by decide
  have hdescent : baseEnd_3128626 < baseStart_3128626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128639 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 3]
def baseStart_3128639 : Nat := 118140960795 + 3128639 * 2 ^ 59
def prefixEnd_3128639 : Nat := 4983230072969 + 3 ^ 40 * 3128639 * 2
def baseEnd_3128639 : Nat := 1606495601402089919224157

theorem tailTrace_3128639 : CollatzResearch.WordTrace tailWord_3128639 prefixEnd_3128639 1606495601402089919224157 := by
  unfold tailWord_3128639
  simp only [CollatzResearch.WordTrace]
  refine ⟨114110838912482706846204971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76073892608321804564136647 114110838912482706846204971)
  ·
    refine ⟨171166258368724060269307457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114110838912482706846204971 171166258368724060269307457)
    ·
      refine ⟨128374693776543045201980593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171166258368724060269307457 128374693776543045201980593)
      ·
        refine ⟨96281020332407283901485445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128374693776543045201980593 96281020332407283901485445)
        ·
          refine ⟨18052691312326365731528521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96281020332407283901485445 18052691312326365731528521)
          ·
            refine ⟨13539518484244774298646391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18052691312326365731528521 13539518484244774298646391)
            ·
              refine ⟨20309277726367161447969587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13539518484244774298646391 20309277726367161447969587)
              ·
                refine ⟨30463916589550742171954381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20309277726367161447969587 30463916589550742171954381)
                ·
                  refine ⟨11423968721081528314482893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30463916589550742171954381 11423968721081528314482893)
                  ·
                    refine ⟨4283988270405573117931085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11423968721081528314482893 4283988270405573117931085)
                    ·
                      refine ⟨1606495601402089919224157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4283988270405573117931085 1606495601402089919224157)
                      ·
                        rfl

theorem cell23_3128639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_3128639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128639 prefixEnd_3128639 := by exact prefixLift 3128639
  have htrace : WordTrace (prefixWord ++ tailWord_3128639) baseStart_3128639 baseEnd_3128639 := by
    simpa [prefixWord, tailWord_3128639, baseEnd_3128639] using wordTrace_append hprefix tailTrace_3128639
  have hstable : (prefixWord ++ tailWord_3128639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128639).length < 2 ^ (prefixWord ++ tailWord_3128639).sum := by decide
  have hdescent : baseEnd_3128639 < baseStart_3128639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128646 : List Nat := [6, 1, 1, 3, 12]
def baseStart_3128646 : Nat := 118140960795 + 3128646 * 2 ^ 59
def prefixEnd_3128646 : Nat := 4983230072969 + 3 ^ 40 * 3128646 * 2
def baseEnd_3128646 : Nat := 2203702600502978589625

theorem tailTrace_3128646 : CollatzResearch.WordTrace tailWord_3128646 prefixEnd_3128646 2203702600502978589625 := by
  unfold tailWord_3128646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565971694483042095053431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76074062815638231361139861 3565971694483042095053431)
  ·
    refine ⟨5348957541724563142580147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3565971694483042095053431 5348957541724563142580147)
    ·
      refine ⟨8023436312586844713870221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5348957541724563142580147 8023436312586844713870221)
      ·
        refine ⟨3008788617220066767701333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8023436312586844713870221 3008788617220066767701333)
        ·
          refine ⟨2203702600502978589625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3008788617220066767701333 2203702600502978589625)
          ·
            rfl

theorem cell23_3128646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 12].length) (baseStart_3128646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128646 prefixEnd_3128646 := by exact prefixLift 3128646
  have htrace : WordTrace (prefixWord ++ tailWord_3128646) baseStart_3128646 baseEnd_3128646 := by
    simpa [prefixWord, tailWord_3128646, baseEnd_3128646] using wordTrace_append hprefix tailTrace_3128646
  have hstable : (prefixWord ++ tailWord_3128646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128646).length < 2 ^ (prefixWord ++ tailWord_3128646).sum := by decide
  have hdescent : baseEnd_3128646 < baseStart_3128646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128666 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2]
def baseStart_3128666 : Nat := 118140960795 + 3128666 * 2 ^ 59
def prefixEnd_3128666 : Nat := 4983230072969 + 3 ^ 40 * 3128666 * 2
def baseEnd_3128666 : Nat := 1606509465379761313586533

theorem tailTrace_3128666 : CollatzResearch.WordTrace tailWord_3128666 prefixEnd_3128666 1606509465379761313586533 := by
  unfold tailWord_3128666
  simp only [CollatzResearch.WordTrace]
  refine ⟨28527955920846222614359463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76074549122256593638291901 28527955920846222614359463)
  ·
    refine ⟨42791933881269333921539195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28527955920846222614359463 42791933881269333921539195)
    ·
      refine ⟨64187900821904000882308793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42791933881269333921539195 64187900821904000882308793)
      ·
        refine ⟨48140925616428000661731595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64187900821904000882308793 48140925616428000661731595)
        ·
          refine ⟨72211388424642000992597393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48140925616428000661731595 72211388424642000992597393)
          ·
            refine ⟨54158541318481500744448045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72211388424642000992597393 54158541318481500744448045)
            ·
              refine ⟨20309452994430562779168017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54158541318481500744448045 20309452994430562779168017)
              ·
                refine ⟨15232089745822922084376013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20309452994430562779168017 15232089745822922084376013)
                ·
                  refine ⟨5712033654683595781641005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15232089745822922084376013 5712033654683595781641005)
                  ·
                    refine ⟨2142012620506348418115377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5712033654683595781641005 2142012620506348418115377)
                    ·
                      refine ⟨1606509465379761313586533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2142012620506348418115377 1606509465379761313586533)
                      ·
                        rfl

theorem cell23_3128666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_3128666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128666 prefixEnd_3128666 := by exact prefixLift 3128666
  have htrace : WordTrace (prefixWord ++ tailWord_3128666) baseStart_3128666 baseEnd_3128666 := by
    simpa [prefixWord, tailWord_3128666, baseEnd_3128666] using wordTrace_append hprefix tailTrace_3128666
  have hstable : (prefixWord ++ tailWord_3128666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128666).length < 2 ^ (prefixWord ++ tailWord_3128666).sum := by decide
  have hdescent : baseEnd_3128666 < baseStart_3128666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128709 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_3128709 : Nat := 118140960795 + 3128709 * 2 ^ 59
def prefixEnd_3128709 : Nat := 4983230072969 + 3 ^ 40 * 3128709 * 2
def baseEnd_3128709 : Nat := 1606531545047904645348835

theorem tailTrace_3128709 : CollatzResearch.WordTrace tailWord_3128709 prefixEnd_3128709 1606531545047904645348835 := by
  unfold tailWord_3128709
  simp only [CollatzResearch.WordTrace]
  refine ⟨114113392022229108801253181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76075594681486072534168787 114113392022229108801253181)
  ·
    refine ⟨42792522008335915800469943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114113392022229108801253181 42792522008335915800469943)
    ·
      refine ⟨64188783012503873700704915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42792522008335915800469943 64188783012503873700704915)
      ·
        refine ⟨96283174518755810551057373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64188783012503873700704915 96283174518755810551057373)
        ·
          refine ⟨36106190444533428956646515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96283174518755810551057373 36106190444533428956646515)
          ·
            refine ⟨54159285666800143434969773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36106190444533428956646515 54159285666800143434969773)
            ·
              refine ⟨20309732125050053788113665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54159285666800143434969773 20309732125050053788113665)
              ·
                refine ⟨15232299093787540341085249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20309732125050053788113665 15232299093787540341085249)
                ·
                  refine ⟨11424224320340655255813937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15232299093787540341085249 11424224320340655255813937)
                  ·
                    refine ⟨8568168240255491441860453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11424224320340655255813937 8568168240255491441860453)
                    ·
                      refine ⟨1606531545047904645348835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8568168240255491441860453 1606531545047904645348835)
                      ·
                        rfl

theorem cell23_3128709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_3128709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128709 prefixEnd_3128709 := by exact prefixLift 3128709
  have htrace : WordTrace (prefixWord ++ tailWord_3128709) baseStart_3128709 baseEnd_3128709 := by
    simpa [prefixWord, tailWord_3128709, baseEnd_3128709] using wordTrace_append hprefix tailTrace_3128709
  have hstable : (prefixWord ++ tailWord_3128709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128709).length < 2 ^ (prefixWord ++ tailWord_3128709).sum := by decide
  have hdescent : baseEnd_3128709 < baseStart_3128709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128759 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_3128759 : Nat := 118140960795 + 3128759 * 2 ^ 59
def prefixEnd_3128759 : Nat := 4983230072969 + 3 ^ 40 * 3128759 * 2
def baseEnd_3128759 : Nat := 1606557219080629449723605

theorem tailTrace_3128759 : CollatzResearch.WordTrace tailWord_3128759 prefixEnd_3128759 1606557219080629449723605 := by
  unfold tailWord_3128759
  simp only [CollatzResearch.WordTrace]
  refine ⟨114115215672047967340573331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76076810448031978227048887 114115215672047967340573331)
  ·
    refine ⟨171172823508071951010859997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114115215672047967340573331 171172823508071951010859997)
    ·
      refine ⟨64189808815526981629072499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171172823508071951010859997 64189808815526981629072499)
      ·
        refine ⟨96284713223290472443608749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64189808815526981629072499 96284713223290472443608749)
        ·
          refine ⟨36106767458733927166353281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96284713223290472443608749 36106767458733927166353281)
          ·
            refine ⟨27080075594050445374764961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36106767458733927166353281 27080075594050445374764961)
            ·
              refine ⟨20310056695537834031073721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27080075594050445374764961 20310056695537834031073721)
              ·
                refine ⟨15232542521653375523305291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20310056695537834031073721 15232542521653375523305291)
                ·
                  refine ⟨22848813782480063284957937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15232542521653375523305291 22848813782480063284957937)
                  ·
                    refine ⟨17136610336860047463718453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22848813782480063284957937 17136610336860047463718453)
                    ·
                      refine ⟨1606557219080629449723605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17136610336860047463718453 1606557219080629449723605)
                      ·
                        rfl

theorem cell23_3128759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_3128759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128759 prefixEnd_3128759 := by exact prefixLift 3128759
  have htrace : WordTrace (prefixWord ++ tailWord_3128759) baseStart_3128759 baseEnd_3128759 := by
    simpa [prefixWord, tailWord_3128759, baseEnd_3128759] using wordTrace_append hprefix tailTrace_3128759
  have hstable : (prefixWord ++ tailWord_3128759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128759).length < 2 ^ (prefixWord ++ tailWord_3128759).sum := by decide
  have hdescent : baseEnd_3128759 < baseStart_3128759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128803 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 4]
def baseStart_3128803 : Nat := 118140960795 + 3128803 * 2 ^ 59
def prefixEnd_3128803 : Nat := 4983230072969 + 3 ^ 40 * 3128803 * 2
def baseEnd_3128803 : Nat := 1606579812229427277573403

theorem tailTrace_3128803 : CollatzResearch.WordTrace tailWord_3128803 prefixEnd_3128803 1606579812229427277573403 := by
  unfold tailWord_3128803
  simp only [CollatzResearch.WordTrace]
  refine ⟨114116820483888562855175063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76077880322592375236783375 114116820483888562855175063)
  ·
    refine ⟨171175230725832844282762595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114116820483888562855175063 171175230725832844282762595)
    ·
      refine ⟨256762846088749266424143893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171175230725832844282762595 256762846088749266424143893)
      ·
        refine ⟨12035758410410121863631745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 256762846088749266424143893 12035758410410121863631745)
        ·
          refine ⟨9026818807807591397723809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12035758410410121863631745 9026818807807591397723809)
          ·
            refine ⟨6770114105855693548292857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9026818807807591397723809 6770114105855693548292857)
            ·
              refine ⟨5077585579391770161219643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6770114105855693548292857 5077585579391770161219643)
              ·
                refine ⟨7616378369087655241829465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5077585579391770161219643 7616378369087655241829465)
                ·
                  refine ⟨5712283776815741431372099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7616378369087655241829465 5712283776815741431372099)
                  ·
                    refine ⟨8568425665223612147058149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5712283776815741431372099 8568425665223612147058149)
                    ·
                      refine ⟨1606579812229427277573403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8568425665223612147058149 1606579812229427277573403)
                      ·
                        rfl

theorem cell23_3128803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_3128803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128803 prefixEnd_3128803 := by exact prefixLift 3128803
  have htrace : WordTrace (prefixWord ++ tailWord_3128803) baseStart_3128803 baseEnd_3128803 := by
    simpa [prefixWord, tailWord_3128803, baseEnd_3128803] using wordTrace_append hprefix tailTrace_3128803
  have hstable : (prefixWord ++ tailWord_3128803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128803).length < 2 ^ (prefixWord ++ tailWord_3128803).sum := by decide
  have hdescent : baseEnd_3128803 < baseStart_3128803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128826 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 6]
def baseStart_3128826 : Nat := 118140960795 + 3128826 * 2 ^ 59
def prefixEnd_3128826 : Nat := 4983230072969 + 3 ^ 40 * 3128826 * 2
def baseEnd_3128826 : Nat := 178510180253831187509533

theorem tailTrace_3128826 : CollatzResearch.WordTrace tailWord_3128826 prefixEnd_3128826 178510180253831187509533 := by
  unfold tailWord_3128826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28529414840701309445815583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76078439575203491855508221 28529414840701309445815583)
  ·
    refine ⟨42794122261051964168723375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28529414840701309445815583 42794122261051964168723375)
    ·
      refine ⟨64191183391577946253085063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42794122261051964168723375 64191183391577946253085063)
      ·
        refine ⟨96286775087366919379627595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64191183391577946253085063 96286775087366919379627595)
        ·
          refine ⟨144430162631050379069441393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96286775087366919379627595 144430162631050379069441393)
          ·
            refine ⟨108322621973287784302081045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144430162631050379069441393 108322621973287784302081045)
            ·
              refine ⟨5077622904997864889160049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108322621973287784302081045 5077622904997864889160049)
              ·
                refine ⟨3808217178748398666870037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5077622904997864889160049 3808217178748398666870037)
                ·
                  refine ⟨178510180253831187509533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3808217178748398666870037 178510180253831187509533)
                  ·
                    rfl

theorem cell23_3128826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_3128826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128826 prefixEnd_3128826 := by exact prefixLift 3128826
  have htrace : WordTrace (prefixWord ++ tailWord_3128826) baseStart_3128826 baseEnd_3128826 := by
    simpa [prefixWord, tailWord_3128826, baseEnd_3128826] using wordTrace_append hprefix tailTrace_3128826
  have hstable : (prefixWord ++ tailWord_3128826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128826).length < 2 ^ (prefixWord ++ tailWord_3128826).sum := by decide
  have hdescent : baseEnd_3128826 < baseStart_3128826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128849 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_3128849 : Nat := 118140960795 + 3128849 * 2 ^ 59
def prefixEnd_3128849 : Nat := 4983230072969 + 3 ^ 40 * 3128849 * 2
def baseEnd_3128849 : Nat := 1606603432339534097598191

theorem tailTrace_3128849 : CollatzResearch.WordTrace tailWord_3128849 prefixEnd_3128849 1606603432339534097598191 := by
  unfold tailWord_3128849
  simp only [CollatzResearch.WordTrace]
  refine ⟨114118498241721912711349601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76078998827814608474233067 114118498241721912711349601)
  ·
    refine ⟨85588873681291434533512201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114118498241721912711349601 85588873681291434533512201)
    ·
      refine ⟨64191655260968575900134151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85588873681291434533512201 64191655260968575900134151)
      ·
        refine ⟨96287482891452863850201227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64191655260968575900134151 96287482891452863850201227)
        ·
          refine ⟨144431224337179295775301841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96287482891452863850201227 144431224337179295775301841)
          ·
            refine ⟨108323418252884471831476381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144431224337179295775301841 108323418252884471831476381)
            ·
              refine ⟨40621281844831676936803643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108323418252884471831476381 40621281844831676936803643)
              ·
                refine ⟨60931922767247515405205465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40621281844831676936803643 60931922767247515405205465)
                ·
                  refine ⟨45698942075435636553904099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60931922767247515405205465 45698942075435636553904099)
                  ·
                    refine ⟨68548413113153454830856149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45698942075435636553904099 68548413113153454830856149)
                    ·
                      refine ⟨1606603432339534097598191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68548413113153454830856149 1606603432339534097598191)
                      ·
                        rfl

theorem cell23_3128849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_3128849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128849 prefixEnd_3128849 := by exact prefixLift 3128849
  have htrace : WordTrace (prefixWord ++ tailWord_3128849) baseStart_3128849 baseEnd_3128849 := by
    simpa [prefixWord, tailWord_3128849, baseEnd_3128849] using wordTrace_append hprefix tailTrace_3128849
  have hstable : (prefixWord ++ tailWord_3128849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128849).length < 2 ^ (prefixWord ++ tailWord_3128849).sum := by decide
  have hdescent : baseEnd_3128849 < baseStart_3128849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128853 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_3128853 : Nat := 118140960795 + 3128853 * 2 ^ 59
def prefixEnd_3128853 : Nat := 4983230072969 + 3 ^ 40 * 3128853 * 2
def baseEnd_3128853 : Nat := 1606605486262152081948173

theorem tailTrace_3128853 : CollatzResearch.WordTrace tailWord_3128853 prefixEnd_3128853 1606605486262152081948173 := by
  unfold tailWord_3128853
  simp only [CollatzResearch.WordTrace]
  refine ⟨114118644133707421394495213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76079096089138280929663475 114118644133707421394495213)
  ·
    refine ⟨42794491550140283022935705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114118644133707421394495213 42794491550140283022935705)
    ·
      refine ⟨32095868662605212267201779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42794491550140283022935705 32095868662605212267201779)
      ·
        refine ⟨48143802993907818400802669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32095868662605212267201779 48143802993907818400802669)
        ·
          refine ⟨18053926122715431900301001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48143802993907818400802669 18053926122715431900301001)
          ·
            refine ⟨13540444592036573925225751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18053926122715431900301001 13540444592036573925225751)
            ·
              refine ⟨20310666888054860887838627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13540444592036573925225751 20310666888054860887838627)
              ·
                refine ⟨30466000332082291331757941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20310666888054860887838627 30466000332082291331757941)
                ·
                  refine ⟨2856187531132714812352307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30466000332082291331757941 2856187531132714812352307)
                  ·
                    refine ⟨4284281296699072218528461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2856187531132714812352307 4284281296699072218528461)
                    ·
                      refine ⟨1606605486262152081948173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4284281296699072218528461 1606605486262152081948173)
                      ·
                        rfl

theorem cell23_3128853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_3128853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128853 prefixEnd_3128853 := by exact prefixLift 3128853
  have htrace : WordTrace (prefixWord ++ tailWord_3128853) baseStart_3128853 baseEnd_3128853 := by
    simpa [prefixWord, tailWord_3128853, baseEnd_3128853] using wordTrace_append hprefix tailTrace_3128853
  have hstable : (prefixWord ++ tailWord_3128853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128853).length < 2 ^ (prefixWord ++ tailWord_3128853).sum := by decide
  have hdescent : baseEnd_3128853 < baseStart_3128853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128906 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_3128906 : Nat := 118140960795 + 3128906 * 2 ^ 59
def prefixEnd_3128906 : Nat := 4983230072969 + 3 ^ 40 * 3128906 * 2
def baseEnd_3128906 : Nat := 1606632700736840374585429

theorem tailTrace_3128906 : CollatzResearch.WordTrace tailWord_3128906 prefixEnd_3128906 1606632700736840374585429 := by
  unfold tailWord_3128906
  simp only [CollatzResearch.WordTrace]
  refine ⟨28530144300628852861543643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76080384801676940964116381 28530144300628852861543643)
  ·
    refine ⟨42795216450943279292315465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28530144300628852861543643 42795216450943279292315465)
    ·
      refine ⟨32096412338207459469236599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42795216450943279292315465 32096412338207459469236599)
      ·
        refine ⟨48144618507311189203854899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32096412338207459469236599 48144618507311189203854899)
        ·
          refine ⟨72216927760966783805782349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48144618507311189203854899 72216927760966783805782349)
          ·
            refine ⟨27081347910362543927168381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72216927760966783805782349 27081347910362543927168381)
            ·
              refine ⟨10155505466385953972688143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27081347910362543927168381 10155505466385953972688143)
              ·
                refine ⟨15233258199578930959032215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10155505466385953972688143 15233258199578930959032215)
                ·
                  refine ⟨22849887299368396438548323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15233258199578930959032215 22849887299368396438548323)
                  ·
                    refine ⟨34274830949052594657822485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22849887299368396438548323 34274830949052594657822485)
                    ·
                      refine ⟨1606632700736840374585429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34274830949052594657822485 1606632700736840374585429)
                      ·
                        rfl

theorem cell23_3128906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_3128906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128906 prefixEnd_3128906 := by exact prefixLift 3128906
  have htrace : WordTrace (prefixWord ++ tailWord_3128906) baseStart_3128906 baseEnd_3128906 := by
    simpa [prefixWord, tailWord_3128906, baseEnd_3128906] using wordTrace_append hprefix tailTrace_3128906
  have hstable : (prefixWord ++ tailWord_3128906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128906).length < 2 ^ (prefixWord ++ tailWord_3128906).sum := by decide
  have hdescent : baseEnd_3128906 < baseStart_3128906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128916 : List Nat := [2, 4, 1, 1, 1, 2, 3, 9]
def baseStart_3128916 : Nat := 118140960795 + 3128916 * 2 ^ 59
def prefixEnd_3128916 : Nat := 4983230072969 + 3 ^ 40 * 3128916 * 2
def baseEnd_3128916 : Nat := 59505105020125382794829

theorem tailTrace_3128916 : CollatzResearch.WordTrace tailWord_3128916 prefixEnd_3128916 59505105020125382794829 := by
  unfold tailWord_3128916
  simp only [CollatzResearch.WordTrace]
  refine ⟨57060470966239591577019301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76080627954986122102692401 57060470966239591577019301)
  ·
    refine ⟨10698838306169923420691119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57060470966239591577019301 10698838306169923420691119)
    ·
      refine ⟨16048257459254885131036679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10698838306169923420691119 16048257459254885131036679)
      ·
        refine ⟨24072386188882327696555019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16048257459254885131036679 24072386188882327696555019)
        ·
          refine ⟨36108579283323491544832529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24072386188882327696555019 36108579283323491544832529)
          ·
            refine ⟨27081434462492618658624397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36108579283323491544832529 27081434462492618658624397)
            ·
              refine ⟨10155537923434731996984149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27081434462492618658624397 10155537923434731996984149)
              ·
                refine ⟨59505105020125382794829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10155537923434731996984149 59505105020125382794829)
                ·
                  rfl

theorem cell23_3128916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 9].length) (baseStart_3128916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128916 prefixEnd_3128916 := by exact prefixLift 3128916
  have htrace : WordTrace (prefixWord ++ tailWord_3128916) baseStart_3128916 baseEnd_3128916 := by
    simpa [prefixWord, tailWord_3128916, baseEnd_3128916] using wordTrace_append hprefix tailTrace_3128916
  have hstable : (prefixWord ++ tailWord_3128916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128916).length < 2 ^ (prefixWord ++ tailWord_3128916).sum := by decide
  have hdescent : baseEnd_3128916 < baseStart_3128916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128960 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 2, 1, 3]
def baseStart_3128960 : Nat := 118140960795 + 3128960 * 2 ^ 59
def prefixEnd_3128960 : Nat := 4983230072969 + 3 ^ 40 * 3128960 * 2
def baseEnd_3128960 : Nat := 1606660428692183163310181

theorem tailTrace_3128960 : CollatzResearch.WordTrace tailWord_3128960 prefixEnd_3128960 1606660428692183163310181 := by
  unfold tailWord_3128960
  simp only [CollatzResearch.WordTrace]
  refine ⟨57061273372159889334320167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76081697829546519112426889 57061273372159889334320167)
  ·
    refine ⟨85591910058239834001480251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57061273372159889334320167 85591910058239834001480251)
    ·
      refine ⟨128387865087359751002220377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85591910058239834001480251 128387865087359751002220377)
      ·
        refine ⟨96290898815519813251665283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128387865087359751002220377 96290898815519813251665283)
        ·
          refine ⟨144436348223279719877497925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96290898815519813251665283 144436348223279719877497925)
          ·
            refine ⟨27081815291864947477030861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144436348223279719877497925 27081815291864947477030861)
            ·
              refine ⟨10155680734449355303886573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27081815291864947477030861 10155680734449355303886573)
              ·
                refine ⟨3808380275418508238957465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10155680734449355303886573 3808380275418508238957465)
                ·
                  refine ⟨2856285206563881179218099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3808380275418508238957465 2856285206563881179218099)
                  ·
                    refine ⟨4284427809845821768827149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2856285206563881179218099 4284427809845821768827149)
                    ·
                      refine ⟨1606660428692183163310181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4284427809845821768827149 1606660428692183163310181)
                      ·
                        rfl

theorem cell23_3128960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_3128960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128960 prefixEnd_3128960 := by exact prefixLift 3128960
  have htrace : WordTrace (prefixWord ++ tailWord_3128960) baseStart_3128960 baseEnd_3128960 := by
    simpa [prefixWord, tailWord_3128960, baseEnd_3128960] using wordTrace_append hprefix tailTrace_3128960
  have hstable : (prefixWord ++ tailWord_3128960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128960).length < 2 ^ (prefixWord ++ tailWord_3128960).sum := by decide
  have hdescent : baseEnd_3128960 < baseStart_3128960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128964 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_3128964 : Nat := 118140960795 + 3128964 * 2 ^ 59
def prefixEnd_3128964 : Nat := 4983230072969 + 3 ^ 40 * 3128964 * 2
def baseEnd_3128964 : Nat := 1606662482614801147660163

theorem tailTrace_3128964 : CollatzResearch.WordTrace tailWord_3128964 prefixEnd_3128964 1606662482614801147660163 := by
  unfold tailWord_3128964
  simp only [CollatzResearch.WordTrace]
  refine ⟨57061346318152643675892973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76081795090870191567857297 57061346318152643675892973)
  ·
    refine ⟨21398004869307241378459865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57061346318152643675892973 21398004869307241378459865)
    ·
      refine ⟨16048503651980431033844899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21398004869307241378459865 16048503651980431033844899)
      ·
        refine ⟨24072755477970646550767349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16048503651980431033844899 24072755477970646550767349)
        ·
          refine ⟨2256820826059748114134439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24072755477970646550767349 2256820826059748114134439)
          ·
            refine ⟨3385231239089622171201659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256820826059748114134439 3385231239089622171201659)
            ·
              refine ⟨5077846858634433256802489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3385231239089622171201659 5077846858634433256802489)
              ·
                refine ⟨3808385143975824942601867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5077846858634433256802489 3808385143975824942601867)
                ·
                  refine ⟨5712577715963737413902801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3808385143975824942601867 5712577715963737413902801)
                  ·
                    refine ⟨4284433286972803060427101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5712577715963737413902801 4284433286972803060427101)
                    ·
                      refine ⟨1606662482614801147660163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4284433286972803060427101 1606662482614801147660163)
                      ·
                        rfl

theorem cell23_3128964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_3128964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3128964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3128964 prefixEnd_3128964 := by exact prefixLift 3128964
  have htrace : WordTrace (prefixWord ++ tailWord_3128964) baseStart_3128964 baseEnd_3128964 := by
    simpa [prefixWord, tailWord_3128964, baseEnd_3128964] using wordTrace_append hprefix tailTrace_3128964
  have hstable : (prefixWord ++ tailWord_3128964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128964).length < 2 ^ (prefixWord ++ tailWord_3128964).sum := by decide
  have hdescent : baseEnd_3128964 < baseStart_3128964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129017 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 2, 2, 2]
def baseStart_3129017 : Nat := 118140960795 + 3129017 * 2 ^ 59
def prefixEnd_3129017 : Nat := 4983230072969 + 3 ^ 40 * 3129017 * 2
def baseEnd_3129017 : Nat := 1606689697089489440297419

theorem tailTrace_3129017 : CollatzResearch.WordTrace tailWord_3129017 prefixEnd_3129017 1606689697089489440297419 := by
  unfold tailWord_3129017
  simp only [CollatzResearch.WordTrace]
  refine ⟨114124625705113277403465305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76083083803408851602310203 114124625705113277403465305)
  ·
    refine ⟨85593469278834958052598979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114124625705113277403465305 85593469278834958052598979)
    ·
      refine ⟨128390203918252437078898469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85593469278834958052598979 128390203918252437078898469)
      ·
        refine ⟨24073163234672331952293463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128390203918252437078898469 24073163234672331952293463)
        ·
          refine ⟨36109744852008497928440195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24073163234672331952293463 36109744852008497928440195)
          ·
            refine ⟨54164617278012746892660293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36109744852008497928440195 54164617278012746892660293)
            ·
              refine ⟨10155865739627390042373805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54164617278012746892660293 10155865739627390042373805)
              ·
                refine ⟨3808449652360271265890177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10155865739627390042373805 3808449652360271265890177)
                ·
                  refine ⟨2856337239270203449417633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3808449652360271265890177 2856337239270203449417633)
                  ·
                    refine ⟨2142252929452652587063225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2856337239270203449417633 2142252929452652587063225)
                    ·
                      refine ⟨1606689697089489440297419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2142252929452652587063225 1606689697089489440297419)
                      ·
                        rfl

theorem cell23_3129017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_3129017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129017 prefixEnd_3129017 := by exact prefixLift 3129017
  have htrace : WordTrace (prefixWord ++ tailWord_3129017) baseStart_3129017 baseEnd_3129017 := by
    simpa [prefixWord, tailWord_3129017, baseEnd_3129017] using wordTrace_append hprefix tailTrace_3129017
  have hstable : (prefixWord ++ tailWord_3129017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129017).length < 2 ^ (prefixWord ++ tailWord_3129017).sum := by decide
  have hdescent : baseEnd_3129017 < baseStart_3129017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129073 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_3129073 : Nat := 118140960795 + 3129073 * 2 ^ 59
def prefixEnd_3129073 : Nat := 4983230072969 + 3 ^ 40 * 3129073 * 2
def baseEnd_3129073 : Nat := 1606718452006141221197161

theorem tailTrace_3129073 : CollatzResearch.WordTrace tailWord_3129073 prefixEnd_3129073 1606718452006141221197161 := by
  unfold tailWord_3129073
  simp only [CollatzResearch.WordTrace]
  refine ⟨114126668192910398967503873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76084445461940265978335915 114126668192910398967503873)
  ·
    refine ⟨85595001144682799225627905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114126668192910398967503873 85595001144682799225627905)
    ·
      refine ⟨64196250858512099419220929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85595001144682799225627905 64196250858512099419220929)
      ·
        refine ⟨48147188143884074564415697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64196250858512099419220929 48147188143884074564415697)
        ·
          refine ⟨36110391107913055923311773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48147188143884074564415697 36110391107913055923311773)
          ·
            refine ⟨13541396665467395971241915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36110391107913055923311773 13541396665467395971241915)
            ·
              refine ⟨20312094998201093956862873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13541396665467395971241915 20312094998201093956862873)
              ·
                refine ⟨15234071248650820467647155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20312094998201093956862873 15234071248650820467647155)
                ·
                  refine ⟨22851106872976230701470733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15234071248650820467647155 22851106872976230701470733)
                  ·
                    refine ⟨8569165077366086513051525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22851106872976230701470733 8569165077366086513051525)
                    ·
                      refine ⟨1606718452006141221197161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8569165077366086513051525 1606718452006141221197161)
                      ·
                        rfl

theorem cell23_3129073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_3129073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129073 prefixEnd_3129073 := by exact prefixLift 3129073
  have htrace : WordTrace (prefixWord ++ tailWord_3129073) baseStart_3129073 baseEnd_3129073 := by
    simpa [prefixWord, tailWord_3129073, baseEnd_3129073] using wordTrace_append hprefix tailTrace_3129073
  have hstable : (prefixWord ++ tailWord_3129073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129073).length < 2 ^ (prefixWord ++ tailWord_3129073).sum := by decide
  have hdescent : baseEnd_3129073 < baseStart_3129073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129083 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 5, 4]
def baseStart_3129083 : Nat := 118140960795 + 3129083 * 2 ^ 59
def prefixEnd_3129083 : Nat := 4983230072969 + 3 ^ 40 * 3129083 * 2
def baseEnd_3129083 : Nat := 535574528937562060690705

theorem tailTrace_3129083 : CollatzResearch.WordTrace tailWord_3129083 prefixEnd_3129083 535574528937562060690705 := by
  unfold tailWord_3129083
  simp only [CollatzResearch.WordTrace]
  refine ⟨114127032922874170675367903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76084688615249447116911935 114127032922874170675367903)
  ·
    refine ⟨171190549384311256013051855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114127032922874170675367903 171190549384311256013051855)
    ·
      refine ⟨256785824076466884019577783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171190549384311256013051855 256785824076466884019577783)
      ·
        refine ⟨385178736114700326029366675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256785824076466884019577783 385178736114700326029366675)
        ·
          refine ⟨577768104172050489044050013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385178736114700326029366675 577768104172050489044050013)
          ·
            refine ⟨216663039064518933391518755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 577768104172050489044050013 216663039064518933391518755)
            ·
              refine ⟨324994558596778400087278133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216663039064518933391518755 324994558596778400087278133)
              ·
                refine ⟨30468239868447975008182325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 324994558596778400087278133 30468239868447975008182325)
                ·
                  refine ⟨2856397487666997657017093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30468239868447975008182325 2856397487666997657017093)
                  ·
                    refine ⟨535574528937562060690705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2856397487666997657017093 535574528937562060690705)
                    ·
                      rfl

theorem cell23_3129083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 4].length) (baseStart_3129083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129083 prefixEnd_3129083 := by exact prefixLift 3129083
  have htrace : WordTrace (prefixWord ++ tailWord_3129083) baseStart_3129083 baseEnd_3129083 := by
    simpa [prefixWord, tailWord_3129083, baseEnd_3129083] using wordTrace_append hprefix tailTrace_3129083
  have hstable : (prefixWord ++ tailWord_3129083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129083).length < 2 ^ (prefixWord ++ tailWord_3129083).sum := by decide
  have hdescent : baseEnd_3129083 < baseStart_3129083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129090 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3129090 : Nat := 118140960795 + 3129090 * 2 ^ 59
def prefixEnd_3129090 : Nat := 4983230072969 + 3 ^ 40 * 3129090 * 2
def baseEnd_3129090 : Nat := 1606727181177267654684583

theorem tailTrace_3129090 : CollatzResearch.WordTrace tailWord_3129090 prefixEnd_3129090 1606727181177267654684583 := by
  unfold tailWord_3129090
  simp only [CollatzResearch.WordTrace]
  refine ⟨28531822058462202717718181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76084858822565873913915149 28531822058462202717718181)
  ·
    refine ⟨5349716635961663009572159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28531822058462202717718181 5349716635961663009572159)
    ·
      refine ⟨8024574953942494514358239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5349716635961663009572159 8024574953942494514358239)
      ·
        refine ⟨12036862430913741771537359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8024574953942494514358239 12036862430913741771537359)
        ·
          refine ⟨18055293646370612657306039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12036862430913741771537359 18055293646370612657306039)
          ·
            refine ⟨27082940469555918985959059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18055293646370612657306039 27082940469555918985959059)
            ·
              refine ⟨40624410704333878478938589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27082940469555918985959059 40624410704333878478938589)
              ·
                refine ⟨15234154014125204429601971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40624410704333878478938589 15234154014125204429601971)
                ·
                  refine ⟨22851231021187806644402957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15234154014125204429601971 22851231021187806644402957)
                  ·
                    refine ⟨8569211632945427491651109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22851231021187806644402957 8569211632945427491651109)
                    ·
                      refine ⟨1606727181177267654684583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8569211632945427491651109 1606727181177267654684583)
                      ·
                        rfl

theorem cell23_3129090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3129090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129090 prefixEnd_3129090 := by exact prefixLift 3129090
  have htrace : WordTrace (prefixWord ++ tailWord_3129090) baseStart_3129090 baseEnd_3129090 := by
    simpa [prefixWord, tailWord_3129090, baseEnd_3129090] using wordTrace_append hprefix tailTrace_3129090
  have hstable : (prefixWord ++ tailWord_3129090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129090).length < 2 ^ (prefixWord ++ tailWord_3129090).sum := by decide
  have hdescent : baseEnd_3129090 < baseStart_3129090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129108 : List Nat := [2, 4, 4, 1, 1, 1, 3, 2, 5]
def baseStart_3129108 : Nat := 118140960795 + 3129108 * 2 ^ 59
def prefixEnd_3129108 : Nat := 4983230072969 + 3 ^ 40 * 3129108 * 2
def baseEnd_3129108 : Nat := 178526269314338731584389

theorem tailTrace_3129108 : CollatzResearch.WordTrace tailWord_3129108 prefixEnd_3129108 178526269314338731584389 := by
  unfold tailWord_3129108
  simp only [CollatzResearch.WordTrace]
  refine ⟨57063972373891799972513989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76085296498522399963351985 57063972373891799972513989)
  ·
    refine ⟨10699494820104712494846373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57063972373891799972513989 10699494820104712494846373)
    ·
      refine ⟨2006155278769633592783695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10699494820104712494846373 2006155278769633592783695)
      ·
        refine ⟨3009232918154450389175543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006155278769633592783695 3009232918154450389175543)
        ·
          refine ⟨4513849377231675583763315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009232918154450389175543 4513849377231675583763315)
          ·
            refine ⟨6770774065847513375644973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4513849377231675583763315 6770774065847513375644973)
            ·
              refine ⟨2539040274692817515866865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6770774065847513375644973 2539040274692817515866865)
              ·
                refine ⟨1904280206019613136900149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2539040274692817515866865 1904280206019613136900149)
                ·
                  refine ⟨178526269314338731584389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1904280206019613136900149 178526269314338731584389)
                  ·
                    rfl

theorem cell23_3129108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_3129108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129108 prefixEnd_3129108 := by exact prefixLift 3129108
  have htrace : WordTrace (prefixWord ++ tailWord_3129108) baseStart_3129108 baseEnd_3129108 := by
    simpa [prefixWord, tailWord_3129108, baseEnd_3129108] using wordTrace_append hprefix tailTrace_3129108
  have hstable : (prefixWord ++ tailWord_3129108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129108).length < 2 ^ (prefixWord ++ tailWord_3129108).sum := by decide
  have hdescent : baseEnd_3129108 < baseStart_3129108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129193 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 6]
def baseStart_3129193 : Nat := 118140960795 + 3129193 * 2 ^ 59
def prefixEnd_3129193 : Nat := 4983230072969 + 3 ^ 40 * 3129193 * 2
def baseEnd_3129193 : Nat := 1606780069684680751696609

theorem tailTrace_3129193 : CollatzResearch.WordTrace tailWord_3129193 prefixEnd_3129193 1606780069684680751696609 := by
  unfold tailWord_3129193
  simp only [CollatzResearch.WordTrace]
  refine ⟨114131044952475659461872233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76087363301650439641248155 114131044952475659461872233)
  ·
    refine ⟨85598283714356744596404175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114131044952475659461872233 85598283714356744596404175)
    ·
      refine ⟨128397425571535116894606263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85598283714356744596404175 128397425571535116894606263)
      ·
        refine ⟨192596138357302675341909395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128397425571535116894606263 192596138357302675341909395)
        ·
          refine ⟨288894207535954013012864093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192596138357302675341909395 288894207535954013012864093)
          ·
            refine ⟨108335327825982754879824035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288894207535954013012864093 108335327825982754879824035)
            ·
              refine ⟨162502991738974132319736053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108335327825982754879824035 162502991738974132319736053)
              ·
                refine ⟨15234655475528824904975255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162502991738974132319736053 15234655475528824904975255)
                ·
                  refine ⟨22851983213293237357462883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15234655475528824904975255 22851983213293237357462883)
                  ·
                    refine ⟨34277974819939856036194325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22851983213293237357462883 34277974819939856036194325)
                    ·
                      refine ⟨1606780069684680751696609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34277974819939856036194325 1606780069684680751696609)
                      ·
                        rfl

theorem cell23_3129193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_3129193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129193 prefixEnd_3129193 := by exact prefixLift 3129193
  have htrace : WordTrace (prefixWord ++ tailWord_3129193) baseStart_3129193 baseEnd_3129193 := by
    simpa [prefixWord, tailWord_3129193, baseEnd_3129193] using wordTrace_append hprefix tailTrace_3129193
  have hstable : (prefixWord ++ tailWord_3129193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129193).length < 2 ^ (prefixWord ++ tailWord_3129193).sum := by decide
  have hdescent : baseEnd_3129193 < baseStart_3129193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129210 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_3129210 : Nat := 118140960795 + 3129210 * 2 ^ 59
def prefixEnd_3129210 : Nat := 4983230072969 + 3 ^ 40 * 3129210 * 2
def baseEnd_3129210 : Nat := 1606788798855807185184031

theorem tailTrace_3129210 : CollatzResearch.WordTrace tailWord_3129210 prefixEnd_3129210 1606788798855807185184031 := by
  unfold tailWord_3129210
  simp only [CollatzResearch.WordTrace]
  refine ⟨28532916248353517841310271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76087776662276047576827389 28532916248353517841310271)
  ·
    refine ⟨42799374372530276761965407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28532916248353517841310271 42799374372530276761965407)
    ·
      refine ⟨64199061558795415142948111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42799374372530276761965407 64199061558795415142948111)
      ·
        refine ⟨96298592338193122714422167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64199061558795415142948111 96298592338193122714422167)
        ·
          refine ⟨144447888507289684071633251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96298592338193122714422167 144447888507289684071633251)
          ·
            refine ⟨216671832760934526107449877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144447888507289684071633251 216671832760934526107449877)
            ·
              refine ⟨10156492160668805911286713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 216671832760934526107449877 10156492160668805911286713)
              ·
                refine ⟨7617369120501604433465035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10156492160668805911286713 7617369120501604433465035)
                ·
                  refine ⟨11426053680752406650197553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7617369120501604433465035 11426053680752406650197553)
                  ·
                    refine ⟨8569540260564304987648165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11426053680752406650197553 8569540260564304987648165)
                    ·
                      refine ⟨1606788798855807185184031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8569540260564304987648165 1606788798855807185184031)
                      ·
                        rfl

theorem cell23_3129210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_3129210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129210 prefixEnd_3129210 := by exact prefixLift 3129210
  have htrace : WordTrace (prefixWord ++ tailWord_3129210) baseStart_3129210 baseEnd_3129210 := by
    simpa [prefixWord, tailWord_3129210, baseEnd_3129210] using wordTrace_append hprefix tailTrace_3129210
  have hstable : (prefixWord ++ tailWord_3129210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129210).length < 2 ^ (prefixWord ++ tailWord_3129210).sum := by decide
  have hdescent : baseEnd_3129210 < baseStart_3129210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129233 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 1, 9]
def baseStart_3129233 : Nat := 118140960795 + 3129233 * 2 ^ 59
def prefixEnd_3129233 : Nat := 4983230072969 + 3 ^ 40 * 3129233 * 2
def baseEnd_3129233 : Nat := 535600202970286865065475

theorem tailTrace_3129233 : CollatzResearch.WordTrace tailWord_3129233 prefixEnd_3129233 535600202970286865065475 := by
  unfold tailWord_3129233
  simp only [CollatzResearch.WordTrace]
  refine ⟨114132503872330746293328353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76088335914887164195552235 114132503872330746293328353)
  ·
    refine ⟨85599377904248059719996265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114132503872330746293328353 85599377904248059719996265)
    ·
      refine ⟨64199533428186044789997199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85599377904248059719996265 64199533428186044789997199)
      ·
        refine ⟨96299300142279067184995799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64199533428186044789997199 96299300142279067184995799)
        ·
          refine ⟨144448950213418600777493699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96299300142279067184995799 144448950213418600777493699)
          ·
            refine ⟨216673425320127901166240549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144448950213418600777493699 216673425320127901166240549)
            ·
              refine ⟨40626267247523981468670103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216673425320127901166240549 40626267247523981468670103)
              ·
                refine ⟨60939400871285972203005155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40626267247523981468670103 60939400871285972203005155)
                ·
                  refine ⟨91409101306928958304507733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60939400871285972203005155 91409101306928958304507733)
                  ·
                    refine ⟨535600202970286865065475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 91409101306928958304507733 535600202970286865065475)
                    ·
                      rfl

theorem cell23_3129233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_3129233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129233 prefixEnd_3129233 := by exact prefixLift 3129233
  have htrace : WordTrace (prefixWord ++ tailWord_3129233) baseStart_3129233 baseEnd_3129233 := by
    simpa [prefixWord, tailWord_3129233, baseEnd_3129233] using wordTrace_append hprefix tailTrace_3129233
  have hstable : (prefixWord ++ tailWord_3129233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129233).length < 2 ^ (prefixWord ++ tailWord_3129233).sum := by decide
  have hdescent : baseEnd_3129233 < baseStart_3129233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129244 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3129244 : Nat := 118140960795 + 3129244 * 2 ^ 59
def prefixEnd_3129244 : Nat := 4983230072969 + 3 ^ 40 * 3129244 * 2
def baseEnd_3129244 : Nat := 1606806257198060052158875

theorem tailTrace_3129244 : CollatzResearch.WordTrace tailWord_3129244 prefixEnd_3129244 1606806257198060052158875 := by
  unfold tailWord_3129244
  simp only [CollatzResearch.WordTrace]
  refine ⟨57066452537645447585989393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76088603383527263447985857 57066452537645447585989393)
  ·
    refine ⟨42799839403234085689492045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57066452537645447585989393 42799839403234085689492045)
    ·
      refine ⟨16049939776212782133559517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42799839403234085689492045 16049939776212782133559517)
      ·
        refine ⟨6018727416079793300084819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16049939776212782133559517 6018727416079793300084819)
        ·
          refine ⟨9028091124119689950127229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6018727416079793300084819 9028091124119689950127229)
          ·
            refine ⟨3385534171544883731297711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9028091124119689950127229 3385534171544883731297711)
            ·
              refine ⟨5078301257317325596946567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3385534171544883731297711 5078301257317325596946567)
              ·
                refine ⟨7617451885975988395419851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078301257317325596946567 7617451885975988395419851)
                ·
                  refine ⟨11426177828963982593129777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7617451885975988395419851 11426177828963982593129777)
                  ·
                    refine ⟨8569633371722986944847333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11426177828963982593129777 8569633371722986944847333)
                    ·
                      refine ⟨1606806257198060052158875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8569633371722986944847333 1606806257198060052158875)
                      ·
                        rfl

theorem cell23_3129244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3129244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129244 prefixEnd_3129244 := by exact prefixLift 3129244
  have htrace : WordTrace (prefixWord ++ tailWord_3129244) baseStart_3129244 baseEnd_3129244 := by
    simpa [prefixWord, tailWord_3129244, baseEnd_3129244] using wordTrace_append hprefix tailTrace_3129244
  have hstable : (prefixWord ++ tailWord_3129244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129244).length < 2 ^ (prefixWord ++ tailWord_3129244).sum := by decide
  have hdescent : baseEnd_3129244 < baseStart_3129244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129325 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3129325 : Nat := 118140960795 + 3129325 * 2 ^ 59
def prefixEnd_3129325 : Nat := 4983230072969 + 3 ^ 40 * 3129325 * 2
def baseEnd_3129325 : Nat := 1606847849131074235246003

theorem tailTrace_3129325 : CollatzResearch.WordTrace tailWord_3129325 prefixEnd_3129325 1606847849131074235246003 := by
  unfold tailWord_3129325
  simp only [CollatzResearch.WordTrace]
  refine ⟨114135859387997446005677429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76090572925331630670451619 114135859387997446005677429)
  ·
    refine ⟨10700236817624760563032259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114135859387997446005677429 10700236817624760563032259)
    ·
      refine ⟨16050355226437140844548389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10700236817624760563032259 16050355226437140844548389)
      ·
        refine ⟨3009441604956963908352823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16050355226437140844548389 3009441604956963908352823)
        ·
          refine ⟨4514162407435445862529235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009441604956963908352823 4514162407435445862529235)
          ·
            refine ⟨6771243611153168793793853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514162407435445862529235 6771243611153168793793853)
            ·
              refine ⟨2539216354182438297672695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6771243611153168793793853 2539216354182438297672695)
              ·
                refine ⟨3808824531273657446509043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539216354182438297672695 3808824531273657446509043)
                ·
                  refine ⟨5713236796910486169763565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3808824531273657446509043 5713236796910486169763565)
                  ·
                    refine ⟨2142463798841432313661337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5713236796910486169763565 2142463798841432313661337)
                    ·
                      refine ⟨1606847849131074235246003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2142463798841432313661337 1606847849131074235246003)
                      ·
                        rfl

theorem cell23_3129325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3129325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129325 prefixEnd_3129325 := by exact prefixLift 3129325
  have htrace : WordTrace (prefixWord ++ tailWord_3129325) baseStart_3129325 baseEnd_3129325 := by
    simpa [prefixWord, tailWord_3129325, baseEnd_3129325] using wordTrace_append hprefix tailTrace_3129325
  have hstable : (prefixWord ++ tailWord_3129325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129325).length < 2 ^ (prefixWord ++ tailWord_3129325).sum := by decide
  have hdescent : baseEnd_3129325 < baseStart_3129325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129327 : List Nat := [1, 1, 2, 1, 4, 2, 2, 5, 5]
def baseStart_3129327 : Nat := 118140960795 + 3129327 * 2 ^ 59
def prefixEnd_3129327 : Nat := 4983230072969 + 3 ^ 40 * 3129327 * 2
def baseEnd_3129327 : Nat := 178538764010264803046777

theorem tailTrace_3129327 : CollatzResearch.WordTrace tailWord_3129327 prefixEnd_3129327 178538764010264803046777 := by
  unfold tailWord_3129327
  simp only [CollatzResearch.WordTrace]
  refine ⟨114135932333990200347250235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76090621555993466898166823 114135932333990200347250235)
  ·
    refine ⟨171203898500985300520875353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114135932333990200347250235 171203898500985300520875353)
    ·
      refine ⟨128402923875738975390656515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171203898500985300520875353 128402923875738975390656515)
      ·
        refine ⟨192604385813608463085984773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128402923875738975390656515 192604385813608463085984773)
        ·
          refine ⟨36113322340051586828622145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192604385813608463085984773 36113322340051586828622145)
          ·
            refine ⟨27084991755038690121466609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36113322340051586828622145 27084991755038690121466609)
            ·
              refine ⟨20313743816279017591099957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27084991755038690121466609 20313743816279017591099957)
              ·
                refine ⟨1904413482776157899165621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20313743816279017591099957 1904413482776157899165621)
                ·
                  refine ⟨178538764010264803046777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1904413482776157899165621 178538764010264803046777)
                  ·
                    rfl

theorem cell23_3129327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 5].length) (baseStart_3129327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129327 prefixEnd_3129327 := by exact prefixLift 3129327
  have htrace : WordTrace (prefixWord ++ tailWord_3129327) baseStart_3129327 baseEnd_3129327 := by
    simpa [prefixWord, tailWord_3129327, baseEnd_3129327] using wordTrace_append hprefix tailTrace_3129327
  have hstable : (prefixWord ++ tailWord_3129327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129327).length < 2 ^ (prefixWord ++ tailWord_3129327).sum := by decide
  have hdescent : baseEnd_3129327 < baseStart_3129327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129354 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_3129354 : Nat := 118140960795 + 3129354 * 2 ^ 59
def prefixEnd_3129354 : Nat := 4983230072969 + 3 ^ 40 * 3129354 * 2
def baseEnd_3129354 : Nat := 1606862740070054621783369

theorem tailTrace_3129354 : CollatzResearch.WordTrace tailWord_3129354 prefixEnd_3129354 1606862740070054621783369 := by
  unfold tailWord_3129354
  simp only [CollatzResearch.WordTrace]
  refine ⟨28534229276223095989620779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76091278069928255972322077 28534229276223095989620779)
  ·
    refine ⟨42801343914334643984431169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28534229276223095989620779 42801343914334643984431169)
    ·
      refine ⟨32101007935750982988323377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42801343914334643984431169 32101007935750982988323377)
      ·
        refine ⟨24075755951813237241242533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32101007935750982988323377 24075755951813237241242533)
        ·
          refine ⟨4514204240964981982732975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24075755951813237241242533 4514204240964981982732975)
          ·
            refine ⟨6771306361447472974099463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514204240964981982732975 6771306361447472974099463)
            ·
              refine ⟨10156959542171209461149195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6771306361447472974099463 10156959542171209461149195)
              ·
                refine ⟨15235439313256814191723793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10156959542171209461149195 15235439313256814191723793)
                ·
                  refine ⟨11426579484942610643792845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15235439313256814191723793 11426579484942610643792845)
                  ·
                    refine ⟨4284967306853478991422317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11426579484942610643792845 4284967306853478991422317)
                    ·
                      refine ⟨1606862740070054621783369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4284967306853478991422317 1606862740070054621783369)
                      ·
                        rfl

theorem cell23_3129354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_3129354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129354 prefixEnd_3129354 := by exact prefixLift 3129354
  have htrace : WordTrace (prefixWord ++ tailWord_3129354) baseStart_3129354 baseEnd_3129354 := by
    simpa [prefixWord, tailWord_3129354, baseEnd_3129354] using wordTrace_append hprefix tailTrace_3129354
  have hstable : (prefixWord ++ tailWord_3129354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129354).length < 2 ^ (prefixWord ++ tailWord_3129354).sum := by decide
  have hdescent : baseEnd_3129354 < baseStart_3129354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129360 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 4]
def baseStart_3129360 : Nat := 118140960795 + 3129360 * 2 ^ 59
def prefixEnd_3129360 : Nat := 4983230072969 + 3 ^ 40 * 3129360 * 2
def baseEnd_3129360 : Nat := 1606865820953981598308341

theorem tailTrace_3129360 : CollatzResearch.WordTrace tailWord_3129360 prefixEnd_3129360 1606865820953981598308341 := by
  unfold tailWord_3129360
  simp only [CollatzResearch.WordTrace]
  refine ⟨57068567971435323491600767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76091423961913764655467689 57068567971435323491600767)
  ·
    refine ⟨85602851957152985237401151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57068567971435323491600767 85602851957152985237401151)
    ·
      refine ⟨128404277935729477856101727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85602851957152985237401151 128404277935729477856101727)
      ·
        refine ⟨192606416903594216784152591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128404277935729477856101727 192606416903594216784152591)
        ·
          refine ⟨288909625355391325176228887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192606416903594216784152591 288909625355391325176228887)
          ·
            refine ⟨433364438033086987764343331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288909625355391325176228887 433364438033086987764343331)
            ·
              refine ⟨650046657049630481646514997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433364438033086987764343331 650046657049630481646514997)
              ·
                refine ⟨60941874098402857654360781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 650046657049630481646514997 60941874098402857654360781)
                ·
                  refine ⟨22853202786901071620385293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60941874098402857654360781 22853202786901071620385293)
                  ·
                    refine ⟨8569951045087901857644485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22853202786901071620385293 8569951045087901857644485)
                    ·
                      refine ⟨1606865820953981598308341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8569951045087901857644485 1606865820953981598308341)
                      ·
                        rfl

theorem cell23_3129360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_3129360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129360 prefixEnd_3129360 := by exact prefixLift 3129360
  have htrace : WordTrace (prefixWord ++ tailWord_3129360) baseStart_3129360 baseEnd_3129360 := by
    simpa [prefixWord, tailWord_3129360, baseEnd_3129360] using wordTrace_append hprefix tailTrace_3129360
  have hstable : (prefixWord ++ tailWord_3129360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129360).length < 2 ^ (prefixWord ++ tailWord_3129360).sum := by decide
  have hdescent : baseEnd_3129360 < baseStart_3129360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129394 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2]
def baseStart_3129394 : Nat := 118140960795 + 3129394 * 2 ^ 59
def prefixEnd_3129394 : Nat := 4983230072969 + 3 ^ 40 * 3129394 * 2
def baseEnd_3129394 : Nat := 1606883279296234465283185

theorem tailTrace_3129394 : CollatzResearch.WordTrace tailWord_3129394 prefixEnd_3129394 1606883279296234465283185 := by
  unfold tailWord_3129394
  simp only [CollatzResearch.WordTrace]
  refine ⟨28534594006186867697484809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76092250683164980526626157 28534594006186867697484809)
  ·
    refine ⟨21400945504640150773113607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28534594006186867697484809 21400945504640150773113607)
    ·
      refine ⟨32101418256960226159670411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21400945504640150773113607 32101418256960226159670411)
      ·
        refine ⟨48152127385440339239505617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32101418256960226159670411 48152127385440339239505617)
        ·
          refine ⟨36114095539080254429629213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48152127385440339239505617 36114095539080254429629213)
          ·
            refine ⟨13542785827155095411110955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36114095539080254429629213 13542785827155095411110955)
            ·
              refine ⟨20314178740732643116666433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13542785827155095411110955 20314178740732643116666433)
              ·
                refine ⟨15235634055549482337499825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20314178740732643116666433 15235634055549482337499825)
                ·
                  refine ⟨11426725541662111753124869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15235634055549482337499825 11426725541662111753124869)
                  ·
                    refine ⟨2142511039061645953710913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11426725541662111753124869 2142511039061645953710913)
                    ·
                      refine ⟨1606883279296234465283185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2142511039061645953710913 1606883279296234465283185)
                      ·
                        rfl

theorem cell23_3129394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_3129394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129394 prefixEnd_3129394 := by exact prefixLift 3129394
  have htrace : WordTrace (prefixWord ++ tailWord_3129394) baseStart_3129394 baseEnd_3129394 := by
    simpa [prefixWord, tailWord_3129394, baseEnd_3129394] using wordTrace_append hprefix tailTrace_3129394
  have hstable : (prefixWord ++ tailWord_3129394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129394).length < 2 ^ (prefixWord ++ tailWord_3129394).sum := by decide
  have hdescent : baseEnd_3129394 < baseStart_3129394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129404 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 3, 4]
def baseStart_3129404 : Nat := 118140960795 + 3129404 * 2 ^ 59
def prefixEnd_3129404 : Nat := 4983230072969 + 3 ^ 40 * 3129404 * 2
def baseEnd_3129404 : Nat := 535629471367593142052713

theorem tailTrace_3129404 : CollatzResearch.WordTrace tailWord_3129404 prefixEnd_3129404 535629471367593142052713 := by
  unfold tailWord_3129404
  simp only [CollatzResearch.WordTrace]
  refine ⟨57069370377355621248901633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76092493836474161665202177 57069370377355621248901633)
  ·
    refine ⟨42802027783016715936676225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57069370377355621248901633 42802027783016715936676225)
    ·
      refine ⟨32101520837262536952507169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42802027783016715936676225 32101520837262536952507169)
      ·
        refine ⟨24076140627946902714380377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32101520837262536952507169 24076140627946902714380377)
        ·
          refine ⟨18057105470960177035785283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24076140627946902714380377 18057105470960177035785283)
          ·
            refine ⟨27085658206440265553677925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18057105470960177035785283 27085658206440265553677925)
            ·
              refine ⟨5078560913707549791314611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27085658206440265553677925 5078560913707549791314611)
              ·
                refine ⟨7617841370561324686971917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078560913707549791314611 7617841370561324686971917)
                ·
                  refine ⟨2856690513960496757614469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7617841370561324686971917 2856690513960496757614469)
                  ·
                    refine ⟨535629471367593142052713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2856690513960496757614469 535629471367593142052713)
                    ·
                      rfl

theorem cell23_3129404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_3129404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129404 prefixEnd_3129404 := by exact prefixLift 3129404
  have htrace : WordTrace (prefixWord ++ tailWord_3129404) baseStart_3129404 baseEnd_3129404 := by
    simpa [prefixWord, tailWord_3129404, baseEnd_3129404] using wordTrace_append hprefix tailTrace_3129404
  have hstable : (prefixWord ++ tailWord_3129404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129404).length < 2 ^ (prefixWord ++ tailWord_3129404).sum := by decide
  have hdescent : baseEnd_3129404 < baseStart_3129404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129444 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_3129444 : Nat := 118140960795 + 3129444 * 2 ^ 59
def prefixEnd_3129444 : Nat := 4983230072969 + 3 ^ 40 * 3129444 * 2
def baseEnd_3129444 : Nat := 1606908953328959269657955

theorem tailTrace_3129444 : CollatzResearch.WordTrace tailWord_3129444 prefixEnd_3129444 1606908953328959269657955 := by
  unfold tailWord_3129444
  simp only [CollatzResearch.WordTrace]
  refine ⟨57070099837283164664629693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76093466449710886219506257 57070099837283164664629693)
  ·
    refine ⟨21401287438981186749236135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57070099837283164664629693 21401287438981186749236135)
    ·
      refine ⟨32101931158471780123854203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21401287438981186749236135 32101931158471780123854203)
      ·
        refine ⟨48152896737707670185781305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32101931158471780123854203 48152896737707670185781305)
        ·
          refine ⟨36114672553280752639335979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48152896737707670185781305 36114672553280752639335979)
          ·
            refine ⟨54172008829921128959003969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36114672553280752639335979 54172008829921128959003969)
            ·
              refine ⟨40629006622440846719252977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54172008829921128959003969 40629006622440846719252977)
              ·
                refine ⟨30471754966830635039439733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40629006622440846719252977 30471754966830635039439733)
                ·
                  refine ⟨2856727028140372034947475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30471754966830635039439733 2856727028140372034947475)
                  ·
                    refine ⟨4285090542210558052421213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2856727028140372034947475 4285090542210558052421213)
                    ·
                      refine ⟨1606908953328959269657955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4285090542210558052421213 1606908953328959269657955)
                      ·
                        rfl

theorem cell23_3129444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_3129444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129444 prefixEnd_3129444 := by exact prefixLift 3129444
  have htrace : WordTrace (prefixWord ++ tailWord_3129444) baseStart_3129444 baseEnd_3129444 := by
    simpa [prefixWord, tailWord_3129444, baseEnd_3129444] using wordTrace_append hprefix tailTrace_3129444
  have hstable : (prefixWord ++ tailWord_3129444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129444).length < 2 ^ (prefixWord ++ tailWord_3129444).sum := by decide
  have hdescent : baseEnd_3129444 < baseStart_3129444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129498 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 1, 5]
def baseStart_3129498 : Nat := 118140960795 + 3129498 * 2 ^ 59
def prefixEnd_3129498 : Nat := 4983230072969 + 3 ^ 40 * 3129498 * 2
def baseEnd_3129498 : Nat := 535645560428100686127569

theorem tailTrace_3129498 : CollatzResearch.WordTrace tailWord_3129498 prefixEnd_3129498 535645560428100686127569 := by
  unfold tailWord_3129498
  simp only [CollatzResearch.WordTrace]
  refine ⟨28535542304092674137931287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76094779477580464367816765 28535542304092674137931287)
  ·
    refine ⟨42803313456139011206896931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28535542304092674137931287 42803313456139011206896931)
    ·
      refine ⟨64204970184208516810345397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42803313456139011206896931 64204970184208516810345397)
      ·
        refine ⟨6019215954769548450969881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64204970184208516810345397 6019215954769548450969881)
        ·
          refine ⟨4514411966077161338227411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6019215954769548450969881 4514411966077161338227411)
          ·
            refine ⟨6771617949115742007341117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514411966077161338227411 6771617949115742007341117)
            ·
              refine ⟨2539356730918403252752919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6771617949115742007341117 2539356730918403252752919)
              ·
                refine ⟨3809035096377604879129379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539356730918403252752919 3809035096377604879129379)
                ·
                  refine ⟨5713552644566407318694069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3809035096377604879129379 5713552644566407318694069)
                  ·
                    refine ⟨535645560428100686127569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5713552644566407318694069 535645560428100686127569)
                    ·
                      rfl

theorem cell23_3129498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_3129498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129498 prefixEnd_3129498 := by exact prefixLift 3129498
  have htrace : WordTrace (prefixWord ++ tailWord_3129498) baseStart_3129498 baseEnd_3129498 := by
    simpa [prefixWord, tailWord_3129498, baseEnd_3129498] using wordTrace_append hprefix tailTrace_3129498
  have hstable : (prefixWord ++ tailWord_3129498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129498).length < 2 ^ (prefixWord ++ tailWord_3129498).sum := by decide
  have hdescent : baseEnd_3129498 < baseStart_3129498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129504 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 5]
def baseStart_3129504 : Nat := 118140960795 + 3129504 * 2 ^ 59
def prefixEnd_3129504 : Nat := 4983230072969 + 3 ^ 40 * 3129504 * 2
def baseEnd_3129504 : Nat := 1606939762168229034907679

theorem tailTrace_3129504 : CollatzResearch.WordTrace tailWord_3129504 prefixEnd_3129504 1606939762168229034907679 := by
  unfold tailWord_3129504
  simp only [CollatzResearch.WordTrace]
  refine ⟨57071194027174479788221783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76094925369565973050962377 57071194027174479788221783)
  ·
    refine ⟨85606791040761719682332675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57071194027174479788221783 85606791040761719682332675)
    ·
      refine ⟨128410186561142579523499013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85606791040761719682332675 128410186561142579523499013)
      ·
        refine ⟨24076909980214233660656065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128410186561142579523499013 24076909980214233660656065)
        ·
          refine ⟨18057682485160675245492049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24076909980214233660656065 18057682485160675245492049)
          ·
            refine ⟨13543261863870506434119037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18057682485160675245492049 13543261863870506434119037)
            ·
              refine ⟨5078723198951439912794639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13543261863870506434119037 5078723198951439912794639)
              ·
                refine ⟨7618084798427159869191959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078723198951439912794639 7618084798427159869191959)
                ·
                  refine ⟨11427127197640739803787939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7618084798427159869191959 11427127197640739803787939)
                  ·
                    refine ⟨17140690796461109705681909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11427127197640739803787939 17140690796461109705681909)
                    ·
                      refine ⟨1606939762168229034907679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17140690796461109705681909 1606939762168229034907679)
                      ·
                        rfl

theorem cell23_3129504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_3129504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129504 prefixEnd_3129504 := by exact prefixLift 3129504
  have htrace : WordTrace (prefixWord ++ tailWord_3129504) baseStart_3129504 baseEnd_3129504 := by
    simpa [prefixWord, tailWord_3129504, baseEnd_3129504] using wordTrace_append hprefix tailTrace_3129504
  have hstable : (prefixWord ++ tailWord_3129504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129504).length < 2 ^ (prefixWord ++ tailWord_3129504).sum := by decide
  have hdescent : baseEnd_3129504 < baseStart_3129504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129547 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 5]
def baseStart_3129547 : Nat := 118140960795 + 3129547 * 2 ^ 59
def prefixEnd_3129547 : Nat := 4983230072969 + 3 ^ 40 * 3129547 * 2
def baseEnd_3129547 : Nat := 1606961841836372366669981

theorem tailTrace_3129547 : CollatzResearch.WordTrace tailWord_3129547 prefixEnd_3129547 1606961841836372366669981 := by
  unfold tailWord_3129547
  simp only [CollatzResearch.WordTrace]
  refine ⟨114143956393193177920258895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76095970928795451946839263 114143956393193177920258895)
  ·
    refine ⟨171215934589789766880388343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114143956393193177920258895 171215934589789766880388343)
    ·
      refine ⟨256823901884684650320582515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171215934589789766880388343 256823901884684650320582515)
      ·
        refine ⟨385235852827026975480873773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256823901884684650320582515 385235852827026975480873773)
        ·
          refine ⟨144463444810135115805327665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385235852827026975480873773 144463444810135115805327665)
          ·
            refine ⟨108347583607601336853995749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144463444810135115805327665 108347583607601336853995749)
            ·
              refine ⟨20315171926425250660124203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108347583607601336853995749 20315171926425250660124203)
              ·
                refine ⟨30472757889637875990186305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20315171926425250660124203 30472757889637875990186305)
                ·
                  refine ⟨22854568417228406992639729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30472757889637875990186305 22854568417228406992639729)
                  ·
                    refine ⟨17140926312921305244479797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22854568417228406992639729 17140926312921305244479797)
                    ·
                      refine ⟨1606961841836372366669981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17140926312921305244479797 1606961841836372366669981)
                      ·
                        rfl

theorem cell23_3129547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_3129547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129547 prefixEnd_3129547 := by exact prefixLift 3129547
  have htrace : WordTrace (prefixWord ++ tailWord_3129547) baseStart_3129547 baseEnd_3129547 := by
    simpa [prefixWord, tailWord_3129547, baseEnd_3129547] using wordTrace_append hprefix tailTrace_3129547
  have hstable : (prefixWord ++ tailWord_3129547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129547).length < 2 ^ (prefixWord ++ tailWord_3129547).sum := by decide
  have hdescent : baseEnd_3129547 < baseStart_3129547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129577 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_3129577 : Nat := 118140960795 + 3129577 * 2 ^ 59
def prefixEnd_3129577 : Nat := 4983230072969 + 3 ^ 40 * 3129577 * 2
def baseEnd_3129577 : Nat := 1606977246256007249294843

theorem tailTrace_3129577 : CollatzResearch.WordTrace tailWord_3129577 prefixEnd_3129577 1606977246256007249294843 := by
  unfold tailWord_3129577
  simp only [CollatzResearch.WordTrace]
  refine ⟨114145050583084493043850985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76096700388722995362567323 114145050583084493043850985)
  ·
    refine ⟨85608787937313369782888239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114145050583084493043850985 85608787937313369782888239)
    ·
      refine ⟨128413181905970054674332359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85608787937313369782888239 128413181905970054674332359)
      ·
        refine ⟨192619772858955082011498539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128413181905970054674332359 192619772858955082011498539)
        ·
          refine ⟨288929659288432623017247809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192619772858955082011498539 288929659288432623017247809)
          ·
            refine ⟨216697244466324467262935857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288929659288432623017247809 216697244466324467262935857)
            ·
              refine ⟨162522933349743350447201893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216697244466324467262935857 162522933349743350447201893)
              ·
                refine ⟨30473050003076878208850355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162522933349743350447201893 30473050003076878208850355)
                ·
                  refine ⟨45709575004615317313275533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30473050003076878208850355 45709575004615317313275533)
                  ·
                    refine ⟨17141090626730743992478325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45709575004615317313275533 17141090626730743992478325)
                    ·
                      refine ⟨1606977246256007249294843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17141090626730743992478325 1606977246256007249294843)
                      ·
                        rfl

theorem cell23_3129577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_3129577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129577 prefixEnd_3129577 := by exact prefixLift 3129577
  have htrace : WordTrace (prefixWord ++ tailWord_3129577) baseStart_3129577 baseEnd_3129577 := by
    simpa [prefixWord, tailWord_3129577, baseEnd_3129577] using wordTrace_append hprefix tailTrace_3129577
  have hstable : (prefixWord ++ tailWord_3129577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129577).length < 2 ^ (prefixWord ++ tailWord_3129577).sum := by decide
  have hdescent : baseEnd_3129577 < baseStart_3129577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129591 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 8, 2, 2]
def baseStart_3129591 : Nat := 118140960795 + 3129591 * 2 ^ 59
def prefixEnd_3129591 : Nat := 4983230072969 + 3 ^ 40 * 3129591 * 2
def baseEnd_3129591 : Nat := 1606984434985170194519779

theorem tailTrace_3129591 : CollatzResearch.WordTrace tailWord_3129591 prefixEnd_3129591 1606984434985170194519779 := by
  unfold tailWord_3129591
  simp only [CollatzResearch.WordTrace]
  refine ⟨114145561205033773434860627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76097040803355848956573751 114145561205033773434860627)
  ·
    refine ⟨171218341807550660152290941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114145561205033773434860627 171218341807550660152290941)
    ·
      refine ⟨64206878177831497557109103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171218341807550660152290941 64206878177831497557109103)
      ·
        refine ⟨96310317266747246335663655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64206878177831497557109103 96310317266747246335663655)
        ·
          refine ⟨144465475900120869503495483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96310317266747246335663655 144465475900120869503495483)
          ·
            refine ⟨216698213850181304255243225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144465475900120869503495483 216698213850181304255243225)
            ·
              refine ⟨162523660387635978191432419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216698213850181304255243225 162523660387635978191432419)
              ·
                refine ⟨243785490581453967287148629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162523660387635978191432419 243785490581453967287148629)
                ·
                  refine ⟨2856861217751413679146273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 243785490581453967287148629 2856861217751413679146273)
                  ·
                    refine ⟨2142645913313560259359705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2856861217751413679146273 2142645913313560259359705)
                    ·
                      refine ⟨1606984434985170194519779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2142645913313560259359705 1606984434985170194519779)
                      ·
                        rfl

theorem cell23_3129591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 2, 2].length) (baseStart_3129591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129591 prefixEnd_3129591 := by exact prefixLift 3129591
  have htrace : WordTrace (prefixWord ++ tailWord_3129591) baseStart_3129591 baseEnd_3129591 := by
    simpa [prefixWord, tailWord_3129591, baseEnd_3129591] using wordTrace_append hprefix tailTrace_3129591
  have hstable : (prefixWord ++ tailWord_3129591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129591).length < 2 ^ (prefixWord ++ tailWord_3129591).sum := by decide
  have hdescent : baseEnd_3129591 < baseStart_3129591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129608 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 4, 2, 2]
def baseStart_3129608 : Nat := 118140960795 + 3129608 * 2 ^ 59
def prefixEnd_3129608 : Nat := 4983230072969 + 3 ^ 40 * 3129608 * 2
def baseEnd_3129608 : Nat := 1606993164156296628007201

theorem tailTrace_3129608 : CollatzResearch.WordTrace tailWord_3129608 prefixEnd_3129608 1606993164156296628007201 := by
  unfold tailWord_3129608
  simp only [CollatzResearch.WordTrace]
  refine ⟨57073090622986092669114739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76097454163981456892152985 57073090622986092669114739)
  ·
    refine ⟨85609635934479139003672109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57073090622986092669114739 85609635934479139003672109)
    ·
      refine ⟨32103613475429677126377041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85609635934479139003672109 32103613475429677126377041)
      ·
        refine ⟨24077710106572257844782781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32103613475429677126377041 24077710106572257844782781)
        ·
          refine ⟨9029141289964596691793543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24077710106572257844782781 9029141289964596691793543)
          ·
            refine ⟨13543711934946895037690315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9029141289964596691793543 13543711934946895037690315)
            ·
              refine ⟨20315567902420342556535473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13543711934946895037690315 20315567902420342556535473)
              ·
                refine ⟨15236675926815256917401605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20315567902420342556535473 15236675926815256917401605)
                ·
                  refine ⟨2856876736277860672012801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15236675926815256917401605 2856876736277860672012801)
                  ·
                    refine ⟨2142657552208395504009601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2856876736277860672012801 2142657552208395504009601)
                    ·
                      refine ⟨1606993164156296628007201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2142657552208395504009601 1606993164156296628007201)
                      ·
                        rfl

theorem cell23_3129608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_3129608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129608 prefixEnd_3129608 := by exact prefixLift 3129608
  have htrace : WordTrace (prefixWord ++ tailWord_3129608) baseStart_3129608 baseEnd_3129608 := by
    simpa [prefixWord, tailWord_3129608, baseEnd_3129608] using wordTrace_append hprefix tailTrace_3129608
  have hstable : (prefixWord ++ tailWord_3129608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129608).length < 2 ^ (prefixWord ++ tailWord_3129608).sum := by decide
  have hdescent : baseEnd_3129608 < baseStart_3129608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129631 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 7]
def baseStart_3129631 : Nat := 118140960795 + 3129631 * 2 ^ 59
def prefixEnd_3129631 : Nat := 4983230072969 + 3 ^ 40 * 3129631 * 2
def baseEnd_3129631 : Nat := 178556108245705559779955

theorem tailTrace_3129631 : CollatzResearch.WordTrace tailWord_3129631 prefixEnd_3129631 178556108245705559779955 := by
  unfold tailWord_3129631
  simp only [CollatzResearch.WordTrace]
  refine ⟨114147020124888860266316747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76098013416592573510877831 114147020124888860266316747)
  ·
    refine ⟨171220530187333290399475121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114147020124888860266316747 171220530187333290399475121)
    ·
      refine ⟨128415397640499967799606341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171220530187333290399475121 128415397640499967799606341)
      ·
        refine ⟨24077887057593743962426189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128415397640499967799606341 24077887057593743962426189)
        ·
          refine ⟨9029207646597653985909821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24077887057593743962426189 9029207646597653985909821)
          ·
            refine ⟨3385952867474120244716183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9029207646597653985909821 3385952867474120244716183)
            ·
              refine ⟨5078929301211180367074275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3385952867474120244716183 5078929301211180367074275)
              ·
                refine ⟨7618393951816770550611413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078929301211180367074275 7618393951816770550611413)
                ·
                  refine ⟨178556108245705559779955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7618393951816770550611413 178556108245705559779955)
                  ·
                    rfl

theorem cell23_3129631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 7].length) (baseStart_3129631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129631 prefixEnd_3129631 := by exact prefixLift 3129631
  have htrace : WordTrace (prefixWord ++ tailWord_3129631) baseStart_3129631 baseEnd_3129631 := by
    simpa [prefixWord, tailWord_3129631, baseEnd_3129631] using wordTrace_append hprefix tailTrace_3129631
  have hstable : (prefixWord ++ tailWord_3129631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129631).length < 2 ^ (prefixWord ++ tailWord_3129631).sum := by decide
  have hdescent : baseEnd_3129631 < baseStart_3129631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129642 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_3129642 : Nat := 118140960795 + 3129642 * 2 ^ 59
def prefixEnd_3129642 : Nat := 4983230072969 + 3 ^ 40 * 3129642 * 2
def baseEnd_3129642 : Nat := 1607010622498549494982045

theorem tailTrace_3129642 : CollatzResearch.WordTrace tailWord_3129642 prefixEnd_3129642 1607010622498549494982045 := by
  unfold tailWord_3129642
  simp only [CollatzResearch.WordTrace]
  refine ⟨28536855331962252286241795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76098280885232672763311453 28536855331962252286241795)
  ·
    refine ⟨42805282997943378429362693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28536855331962252286241795 42805282997943378429362693)
    ·
      refine ⟨8025990562114383455505505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42805282997943378429362693 8025990562114383455505505)
      ·
        refine ⟨6019492921585787591629129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8025990562114383455505505 6019492921585787591629129)
        ·
          refine ⟨4514619691189340693721847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6019492921585787591629129 4514619691189340693721847)
          ·
            refine ⟨6771929536784011040582771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514619691189340693721847 6771929536784011040582771)
            ·
              refine ⟨10157894305176016560874157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6771929536784011040582771 10157894305176016560874157)
              ·
                refine ⟨3809210364441006210327809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10157894305176016560874157 3809210364441006210327809)
                ·
                  refine ⟨2856907773330754657745857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3809210364441006210327809 2856907773330754657745857)
                  ·
                    refine ⟨2142680829998065993309393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2856907773330754657745857 2142680829998065993309393)
                    ·
                      refine ⟨1607010622498549494982045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2142680829998065993309393 1607010622498549494982045)
                      ·
                        rfl

theorem cell23_3129642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_3129642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129642 prefixEnd_3129642 := by exact prefixLift 3129642
  have htrace : WordTrace (prefixWord ++ tailWord_3129642) baseStart_3129642 baseEnd_3129642 := by
    simpa [prefixWord, tailWord_3129642, baseEnd_3129642] using wordTrace_append hprefix tailTrace_3129642
  have hstable : (prefixWord ++ tailWord_3129642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129642).length < 2 ^ (prefixWord ++ tailWord_3129642).sum := by decide
  have hdescent : baseEnd_3129642 < baseStart_3129642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129681 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_3129681 : Nat := 118140960795 + 3129681 * 2 ^ 59
def prefixEnd_3129681 : Nat := 4983230072969 + 3 ^ 40 * 3129681 * 2
def baseEnd_3129681 : Nat := 1607030648244074842394365

theorem tailTrace_3129681 : CollatzResearch.WordTrace tailWord_3129681 prefixEnd_3129681 1607030648244074842394365 := by
  unfold tailWord_3129681
  simp only [CollatzResearch.WordTrace]
  refine ⟨114148843774707718805636897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76099229183138479203757931 114148843774707718805636897)
  ·
    refine ⟨85611632831030789104227673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114148843774707718805636897 85611632831030789104227673)
    ·
      refine ⟨64208724623273091828170755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85611632831030789104227673 64208724623273091828170755)
      ·
        refine ⟨96313086934909637742256133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64208724623273091828170755 96313086934909637742256133)
        ·
          refine ⟨18058703800295557076673025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96313086934909637742256133 18058703800295557076673025)
          ·
            refine ⟨13544027850221667807504769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18058703800295557076673025 13544027850221667807504769)
            ·
              refine ⟨10158020887666250855628577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13544027850221667807504769 10158020887666250855628577)
              ·
                refine ⟨7618515665749688141721433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10158020887666250855628577 7618515665749688141721433)
                ·
                  refine ⟨5713886749312266106291075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7618515665749688141721433 5713886749312266106291075)
                  ·
                    refine ⟨8570830123968399159436613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5713886749312266106291075 8570830123968399159436613)
                    ·
                      refine ⟨1607030648244074842394365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8570830123968399159436613 1607030648244074842394365)
                      ·
                        rfl

theorem cell23_3129681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_3129681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129681 prefixEnd_3129681 := by exact prefixLift 3129681
  have htrace : WordTrace (prefixWord ++ tailWord_3129681) baseStart_3129681 baseEnd_3129681 := by
    simpa [prefixWord, tailWord_3129681, baseEnd_3129681] using wordTrace_append hprefix tailTrace_3129681
  have hstable : (prefixWord ++ tailWord_3129681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129681).length < 2 ^ (prefixWord ++ tailWord_3129681).sum := by decide
  have hdescent : baseEnd_3129681 < baseStart_3129681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129698 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_3129698 : Nat := 118140960795 + 3129698 * 2 ^ 59
def prefixEnd_3129698 : Nat := 4983230072969 + 3 ^ 40 * 3129698 * 2
def baseEnd_3129698 : Nat := 1607039377415201275881787

theorem tailTrace_3129698 : CollatzResearch.WordTrace tailWord_3129698 prefixEnd_3129698 1607039377415201275881787 := by
  unfold tailWord_3129698
  simp only [CollatzResearch.WordTrace]
  refine ⟨28537365953911532677251437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76099642543764087139337165 28537365953911532677251437)
  ·
    refine ⟨10701512232716824753969289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28537365953911532677251437 10701512232716824753969289)
    ·
      refine ⟨8026134174537618565476967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10701512232716824753969289 8026134174537618565476967)
      ·
        refine ⟨12039201261806427848215451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8026134174537618565476967 12039201261806427848215451)
        ·
          refine ⟨18058801892709641772323177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12039201261806427848215451 18058801892709641772323177)
          ·
            refine ⟨13544101419532231329242383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18058801892709641772323177 13544101419532231329242383)
            ·
              refine ⟨20316152129298346993863575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13544101419532231329242383 20316152129298346993863575)
              ·
                refine ⟨30474228193947520490795363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20316152129298346993863575 30474228193947520490795363)
                ·
                  refine ⟨45711342290921280736193045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30474228193947520490795363 45711342290921280736193045)
                  ·
                    refine ⟨2142719169886935034509049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45711342290921280736193045 2142719169886935034509049)
                    ·
                      refine ⟨1607039377415201275881787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2142719169886935034509049 1607039377415201275881787)
                      ·
                        rfl

theorem cell23_3129698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_3129698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129698 prefixEnd_3129698 := by exact prefixLift 3129698
  have htrace : WordTrace (prefixWord ++ tailWord_3129698) baseStart_3129698 baseEnd_3129698 := by
    simpa [prefixWord, tailWord_3129698, baseEnd_3129698] using wordTrace_append hprefix tailTrace_3129698
  have hstable : (prefixWord ++ tailWord_3129698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129698).length < 2 ^ (prefixWord ++ tailWord_3129698).sum := by decide
  have hdescent : baseEnd_3129698 < baseStart_3129698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129708 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 3, 4]
def baseStart_3129708 : Nat := 118140960795 + 3129708 * 2 ^ 59
def prefixEnd_3129708 : Nat := 4983230072969 + 3 ^ 40 * 3129708 * 2
def baseEnd_3129708 : Nat := 535681504073915412252247

theorem tailTrace_3129708 : CollatzResearch.WordTrace tailWord_3129708 prefixEnd_3129708 535681504073915412252247 := by
  unfold tailWord_3129708
  simp only [CollatzResearch.WordTrace]
  refine ⟨57074914272804951208434889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76099885697073268277913185 57074914272804951208434889)
  ·
    refine ⟨42806185704603713406326167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57074914272804951208434889 42806185704603713406326167)
    ·
      refine ⟨64209278556905570109489251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42806185704603713406326167 64209278556905570109489251)
      ·
        refine ⟨96313917835358355164233877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64209278556905570109489251 96313917835358355164233877)
        ·
          refine ⟨4514714898532422898323463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96313917835358355164233877 4514714898532422898323463)
          ·
            refine ⟨6772072347798634347485195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514714898532422898323463 6772072347798634347485195)
            ·
              refine ⟨10158108521697951521227793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772072347798634347485195 10158108521697951521227793)
              ·
                refine ⟨7618581391273463640920845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10158108521697951521227793 7618581391273463640920845)
                ·
                  refine ⟨2856968021727548865345317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7618581391273463640920845 2856968021727548865345317)
                  ·
                    refine ⟨535681504073915412252247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2856968021727548865345317 535681504073915412252247)
                    ·
                      rfl

theorem cell23_3129708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_3129708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129708 prefixEnd_3129708 := by exact prefixLift 3129708
  have htrace : WordTrace (prefixWord ++ tailWord_3129708) baseStart_3129708 baseEnd_3129708 := by
    simpa [prefixWord, tailWord_3129708, baseEnd_3129708] using wordTrace_append hprefix tailTrace_3129708
  have hstable : (prefixWord ++ tailWord_3129708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129708).length < 2 ^ (prefixWord ++ tailWord_3129708).sum := by decide
  have hdescent : baseEnd_3129708 < baseStart_3129708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129725 : List Nat := [1, 4, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_3129725 : Nat := 118140960795 + 3129725 * 2 ^ 59
def prefixEnd_3129725 : Nat := 4983230072969 + 3 ^ 40 * 3129725 * 2
def baseEnd_3129725 : Nat := 535684413797624223414721

theorem tailTrace_3129725 : CollatzResearch.WordTrace tailWord_3129725 prefixEnd_3129725 535684413797624223414721 := by
  unfold tailWord_3129725
  simp only [CollatzResearch.WordTrace]
  refine ⟨114150448586548314320238629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76100299057698876213492419 114150448586548314320238629)
  ·
    refine ⟨21403209109977808935044743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114150448586548314320238629 21403209109977808935044743)
    ·
      refine ⟨32104813664966713402567115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21403209109977808935044743 32104813664966713402567115)
      ·
        refine ⟨48157220497450070103850673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32104813664966713402567115 48157220497450070103850673)
        ·
          refine ⟨36117915373087552577888005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48157220497450070103850673 36117915373087552577888005)
          ·
            refine ⟨6772109132453916108354001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36117915373087552577888005 6772109132453916108354001)
            ·
              refine ⟨5079081849340437081265501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6772109132453916108354001 5079081849340437081265501)
              ·
                refine ⟨1904655693502663905474563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5079081849340437081265501 1904655693502663905474563)
                ·
                  refine ⟨2856983540253995858211845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904655693502663905474563 2856983540253995858211845)
                  ·
                    refine ⟨535684413797624223414721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2856983540253995858211845 535684413797624223414721)
                    ·
                      rfl

theorem cell23_3129725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_3129725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129725 prefixEnd_3129725 := by exact prefixLift 3129725
  have htrace : WordTrace (prefixWord ++ tailWord_3129725) baseStart_3129725 baseEnd_3129725 := by
    simpa [prefixWord, tailWord_3129725, baseEnd_3129725] using wordTrace_append hprefix tailTrace_3129725
  have hstable : (prefixWord ++ tailWord_3129725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129725).length < 2 ^ (prefixWord ++ tailWord_3129725).sum := by decide
  have hdescent : baseEnd_3129725 < baseStart_3129725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129738 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 8]
def baseStart_3129738 : Nat := 118140960795 + 3129738 * 2 ^ 59
def prefixEnd_3129738 : Nat := 4983230072969 + 3 ^ 40 * 3129738 * 2
def baseEnd_3129738 : Nat := 178562212960153457709067

theorem tailTrace_3129738 : CollatzResearch.WordTrace tailWord_3129738 prefixEnd_3129738 178562212960153457709067 := by
  unfold tailWord_3129738
  simp only [CollatzResearch.WordTrace]
  refine ⟨28537730683875304385115467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76100615157000811693641245 28537730683875304385115467)
  ·
    refine ⟨42806596025812956577673201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28537730683875304385115467 42806596025812956577673201)
    ·
      refine ⟨32104947019359717433254901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42806596025812956577673201 32104947019359717433254901)
      ·
        refine ⟨3009838783064973509367647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32104947019359717433254901 3009838783064973509367647)
        ·
          refine ⟨4514758174597460264051471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009838783064973509367647 4514758174597460264051471)
          ·
            refine ⟨6772137261896190396077207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514758174597460264051471 6772137261896190396077207)
            ·
              refine ⟨10158205892844285594115811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772137261896190396077207 10158205892844285594115811)
              ·
                refine ⟨15237308839266428391173717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10158205892844285594115811 15237308839266428391173717)
                ·
                  refine ⟨178562212960153457709067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15237308839266428391173717 178562212960153457709067)
                  ·
                    rfl

theorem cell23_3129738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_3129738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129738 prefixEnd_3129738 := by exact prefixLift 3129738
  have htrace : WordTrace (prefixWord ++ tailWord_3129738) baseStart_3129738 baseEnd_3129738 := by
    simpa [prefixWord, tailWord_3129738, baseEnd_3129738] using wordTrace_append hprefix tailTrace_3129738
  have hstable : (prefixWord ++ tailWord_3129738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129738).length < 2 ^ (prefixWord ++ tailWord_3129738).sum := by decide
  have hdescent : baseEnd_3129738 < baseStart_3129738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129791 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 3]
def baseStart_3129791 : Nat := 118140960795 + 3129791 * 2 ^ 59
def prefixEnd_3129791 : Nat := 4983230072969 + 3 ^ 40 * 3129791 * 2
def baseEnd_3129791 : Nat := 1607087131116069412018859

theorem tailTrace_3129791 : CollatzResearch.WordTrace tailWord_3129791 prefixEnd_3129791 1607087131116069412018859 := by
  unfold tailWord_3129791
  simp only [CollatzResearch.WordTrace]
  refine ⟨114152855804309207592141227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76101903869539471728094151 114152855804309207592141227)
  ·
    refine ⟨171229283706463811388211841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114152855804309207592141227 171229283706463811388211841)
    ·
      refine ⟨128421962779847858541158881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171229283706463811388211841 128421962779847858541158881)
      ·
        refine ⟨96316472084885893905869161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128421962779847858541158881 96316472084885893905869161)
        ·
          refine ⟨72237354063664420429401871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96316472084885893905869161 72237354063664420429401871)
          ·
            refine ⟨108356031095496630644102807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72237354063664420429401871 108356031095496630644102807)
            ·
              refine ⟨162534046643244945966154211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108356031095496630644102807 162534046643244945966154211)
              ·
                refine ⟨243801069964867418949231317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162534046643244945966154211 243801069964867418949231317)
                ·
                  refine ⟨5714087577301580131622609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 243801069964867418949231317 5714087577301580131622609)
                  ·
                    refine ⟨4285565682976185098716957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5714087577301580131622609 4285565682976185098716957)
                    ·
                      refine ⟨1607087131116069412018859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4285565682976185098716957 1607087131116069412018859)
                      ·
                        rfl

theorem cell23_3129791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_3129791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129791 prefixEnd_3129791 := by exact prefixLift 3129791
  have htrace : WordTrace (prefixWord ++ tailWord_3129791) baseStart_3129791 baseEnd_3129791 := by
    simpa [prefixWord, tailWord_3129791, baseEnd_3129791] using wordTrace_append hprefix tailTrace_3129791
  have hstable : (prefixWord ++ tailWord_3129791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129791).length < 2 ^ (prefixWord ++ tailWord_3129791).sum := by decide
  have hdescent : baseEnd_3129791 < baseStart_3129791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129838 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_3129838 : Nat := 118140960795 + 3129838 * 2 ^ 59
def prefixEnd_3129838 : Nat := 4983230072969 + 3 ^ 40 * 3129838 * 2
def baseEnd_3129838 : Nat := 1607111264706830728131143

theorem tailTrace_3129838 : CollatzResearch.WordTrace tailWord_3129838 prefixEnd_3129838 1607111264706830728131143 := by
  unfold tailWord_3129838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14269321254392366827387771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76103046690092623079401445 14269321254392366827387771)
  ·
    refine ⟨21403981881588550241081657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14269321254392366827387771 21403981881588550241081657)
    ·
      refine ⟨16052986411191412680811243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21403981881588550241081657 16052986411191412680811243)
      ·
        refine ⟨24079479616787119021216865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16052986411191412680811243 24079479616787119021216865)
        ·
          refine ⟨18059609712590339265912649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24079479616787119021216865 18059609712590339265912649)
          ·
            refine ⟨13544707284442754449434487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18059609712590339265912649 13544707284442754449434487)
            ·
              refine ⟨20317060926664131674151731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13544707284442754449434487 20317060926664131674151731)
              ·
                refine ⟨30475591389996197511227597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20317060926664131674151731 30475591389996197511227597)
                ·
                  refine ⟨11428346771248574066710349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30475591389996197511227597 11428346771248574066710349)
                  ·
                    refine ⟨4285630039218215275016381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11428346771248574066710349 4285630039218215275016381)
                    ·
                      refine ⟨1607111264706830728131143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4285630039218215275016381 1607111264706830728131143)
                      ·
                        rfl

theorem cell23_3129838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_3129838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129838 prefixEnd_3129838 := by exact prefixLift 3129838
  have htrace : WordTrace (prefixWord ++ tailWord_3129838) baseStart_3129838 baseEnd_3129838 := by
    simpa [prefixWord, tailWord_3129838, baseEnd_3129838] using wordTrace_append hprefix tailTrace_3129838
  have hstable : (prefixWord ++ tailWord_3129838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129838).length < 2 ^ (prefixWord ++ tailWord_3129838).sum := by decide
  have hdescent : baseEnd_3129838 < baseStart_3129838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129842 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 1, 1, 5]
def baseStart_3129842 : Nat := 118140960795 + 3129842 * 2 ^ 59
def prefixEnd_3129842 : Nat := 4983230072969 + 3 ^ 40 * 3129842 * 2
def baseEnd_3129842 : Nat := 1607113318629448712481125

theorem tailTrace_3129842 : CollatzResearch.WordTrace tailWord_3129842 prefixEnd_3129842 1607113318629448712481125 := by
  unfold tailWord_3129842
  simp only [CollatzResearch.WordTrace]
  refine ⟨28538678981781110825561945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76103143951416295534831853 28538678981781110825561945)
  ·
    refine ⟨21404009236335833119171459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28538678981781110825561945 21404009236335833119171459)
    ·
      refine ⟨32106013854503749678757189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21404009236335833119171459 32106013854503749678757189)
      ·
        refine ⟨6019877597719453064766973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32106013854503749678757189 6019877597719453064766973)
        ·
          refine ⟨2257454099144794899287615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6019877597719453064766973 2257454099144794899287615)
          ·
            refine ⟨3386181148717192348931423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257454099144794899287615 3386181148717192348931423)
            ·
              refine ⟨5079271723075788523397135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3386181148717192348931423 5079271723075788523397135)
              ·
                refine ⟨7618907584613682785095703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079271723075788523397135 7618907584613682785095703)
                ·
                  refine ⟨11428361376920524177643555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7618907584613682785095703 11428361376920524177643555)
                  ·
                    refine ⟨17142542065380786266465333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11428361376920524177643555 17142542065380786266465333)
                    ·
                      refine ⟨1607113318629448712481125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17142542065380786266465333 1607113318629448712481125)
                      ·
                        rfl

theorem cell23_3129842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_3129842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129842 prefixEnd_3129842 := by exact prefixLift 3129842
  have htrace : WordTrace (prefixWord ++ tailWord_3129842) baseStart_3129842 baseEnd_3129842 := by
    simpa [prefixWord, tailWord_3129842, baseEnd_3129842] using wordTrace_append hprefix tailTrace_3129842
  have hstable : (prefixWord ++ tailWord_3129842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129842).length < 2 ^ (prefixWord ++ tailWord_3129842).sum := by decide
  have hdescent : baseEnd_3129842 < baseStart_3129842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129855 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 2, 1, 3]
def baseStart_3129855 : Nat := 118140960795 + 3129855 * 2 ^ 59
def prefixEnd_3129855 : Nat := 4983230072969 + 3 ^ 40 * 3129855 * 2
def baseEnd_3129855 : Nat := 1607119993877957161618565

theorem tailTrace_3129855 : CollatzResearch.WordTrace tailWord_3129855 prefixEnd_3129855 1607119993877957161618565 := by
  unfold tailWord_3129855
  simp only [CollatzResearch.WordTrace]
  refine ⟨114155190076077346522471019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76103460050718231014980679 114155190076077346522471019)
  ·
    refine ⟨171232785114116019783706529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114155190076077346522471019 171232785114116019783706529)
    ·
      refine ⟨128424588835587014837779897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171232785114116019783706529 128424588835587014837779897)
      ·
        refine ⟨96318441626690261128334923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128424588835587014837779897 96318441626690261128334923)
        ·
          refine ⟨144477662440035391692502385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96318441626690261128334923 144477662440035391692502385)
          ·
            refine ⟨108358246830026543769376789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144477662440035391692502385 108358246830026543769376789)
            ·
              refine ⟨5079292820157494239189537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108358246830026543769376789 5079292820157494239189537)
              ·
                refine ⟨3809469615118120679392153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5079292820157494239189537 3809469615118120679392153)
                ·
                  refine ⟨2857102211338590509544115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3809469615118120679392153 2857102211338590509544115)
                  ·
                    refine ⟨4285653317007885764316173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2857102211338590509544115 4285653317007885764316173)
                    ·
                      refine ⟨1607119993877957161618565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4285653317007885764316173 1607119993877957161618565)
                      ·
                        rfl

theorem cell23_3129855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_3129855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129855 prefixEnd_3129855 := by exact prefixLift 3129855
  have htrace : WordTrace (prefixWord ++ tailWord_3129855) baseStart_3129855 baseEnd_3129855 := by
    simpa [prefixWord, tailWord_3129855, baseEnd_3129855] using wordTrace_append hprefix tailTrace_3129855
  have hstable : (prefixWord ++ tailWord_3129855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129855).length < 2 ^ (prefixWord ++ tailWord_3129855).sum := by decide
  have hdescent : baseEnd_3129855 < baseStart_3129855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129861 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_3129861 : Nat := 118140960795 + 3129861 * 2 ^ 59
def prefixEnd_3129861 : Nat := 4983230072969 + 3 ^ 40 * 3129861 * 2
def baseEnd_3129861 : Nat := 1607123074761884138143537

theorem tailTrace_3129861 : CollatzResearch.WordTrace tailWord_3129861 prefixEnd_3129861 1607123074761884138143537 := by
  unfold tailWord_3129861
  simp only [CollatzResearch.WordTrace]
  refine ⟨114155408914055609547189437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76103605942703739698126291 114155408914055609547189437)
  ·
    refine ⟨42808278342770853580196039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114155408914055609547189437 42808278342770853580196039)
    ·
      refine ⟨64212417514156280370294059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42808278342770853580196039 64212417514156280370294059)
      ·
        refine ⟨96318626271234420555441089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64212417514156280370294059 96318626271234420555441089)
        ·
          refine ⟨72238969703425815416580817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96318626271234420555441089 72238969703425815416580817)
          ·
            refine ⟨54179227277569361562435613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72238969703425815416580817 54179227277569361562435613)
            ·
              refine ⟨20317210229088510585913355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54179227277569361562435613 20317210229088510585913355)
              ·
                refine ⟨30475815343632765878870033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20317210229088510585913355 30475815343632765878870033)
                ·
                  refine ⟨22856861507724574409152525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30475815343632765878870033 22856861507724574409152525)
                  ·
                    refine ⟨8571323065396715403432197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22856861507724574409152525 8571323065396715403432197)
                    ·
                      refine ⟨1607123074761884138143537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8571323065396715403432197 1607123074761884138143537)
                      ·
                        rfl

theorem cell23_3129861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_3129861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129861 prefixEnd_3129861 := by exact prefixLift 3129861
  have htrace : WordTrace (prefixWord ++ tailWord_3129861) baseStart_3129861 baseEnd_3129861 := by
    simpa [prefixWord, tailWord_3129861, baseEnd_3129861] using wordTrace_append hprefix tailTrace_3129861
  have hstable : (prefixWord ++ tailWord_3129861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129861).length < 2 ^ (prefixWord ++ tailWord_3129861).sum := by decide
  have hdescent : baseEnd_3129861 < baseStart_3129861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129862 : List Nat := [6, 2, 1, 1, 1, 1, 3, 8]
def baseStart_3129862 : Nat := 118140960795 + 3129862 * 2 ^ 59
def prefixEnd_3129862 : Nat := 4983230072969 + 3 ^ 40 * 3129862 * 2
def baseEnd_3129862 : Nat := 59523095860834764230779

theorem tailTrace_3129862 : CollatzResearch.WordTrace tailWord_3129862 prefixEnd_3129862 59523095860834764230779 := by
  unfold tailWord_3129862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567357668345374584936745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76103630258034657811983893 3567357668345374584936745)
  ·
    refine ⟨2675518251259030938702559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3567357668345374584936745 2675518251259030938702559)
    ·
      refine ⟨4013277376888546408053839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2675518251259030938702559 4013277376888546408053839)
      ·
        refine ⟨6019916065332819612080759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4013277376888546408053839 6019916065332819612080759)
        ·
          refine ⟨9029874097999229418121139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6019916065332819612080759 9029874097999229418121139)
          ·
            refine ⟨13544811146998844127181709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9029874097999229418121139 13544811146998844127181709)
            ·
              refine ⟨5079304180124566547693141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13544811146998844127181709 5079304180124566547693141)
              ·
                refine ⟨59523095860834764230779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5079304180124566547693141 59523095860834764230779)
                ·
                  rfl

theorem cell23_3129862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_3129862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129862 prefixEnd_3129862 := by exact prefixLift 3129862
  have htrace : WordTrace (prefixWord ++ tailWord_3129862) baseStart_3129862 baseEnd_3129862 := by
    simpa [prefixWord, tailWord_3129862, baseEnd_3129862] using wordTrace_append hprefix tailTrace_3129862
  have hstable : (prefixWord ++ tailWord_3129862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129862).length < 2 ^ (prefixWord ++ tailWord_3129862).sum := by decide
  have hdescent : baseEnd_3129862 < baseStart_3129862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129931 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 1, 7]
def baseStart_3129931 : Nat := 118140960795 + 3129931 * 2 ^ 59
def prefixEnd_3129931 : Nat := 4983230072969 + 3 ^ 40 * 3129931 * 2
def baseEnd_3129931 : Nat := 535719672802566288089405

theorem tailTrace_3129931 : CollatzResearch.WordTrace tailWord_3129931 prefixEnd_3129931 535719672802566288089405 := by
  unfold tailWord_3129931
  simp only [CollatzResearch.WordTrace]
  refine ⟨114157962023802011502237647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76105308015868007668158431 114157962023802011502237647)
  ·
    refine ⟨171236943035703017253356471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114157962023802011502237647 171236943035703017253356471)
    ·
      refine ⟨256855414553554525880034707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171236943035703017253356471 256855414553554525880034707)
      ·
        refine ⟨385283121830331788820052061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256855414553554525880034707 385283121830331788820052061)
        ·
          refine ⟨144481170686374420807519523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385283121830331788820052061 144481170686374420807519523)
          ·
            refine ⟨216721756029561631211279285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144481170686374420807519523 216721756029561631211279285)
            ·
              refine ⟨20317664627771402926057433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216721756029561631211279285 20317664627771402926057433)
              ·
                refine ⟨15238248470828552194543075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20317664627771402926057433 15238248470828552194543075)
                ·
                  refine ⟨22857372706242828291814613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15238248470828552194543075 22857372706242828291814613)
                  ·
                    refine ⟨535719672802566288089405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22857372706242828291814613 535719672802566288089405)
                    ·
                      rfl

theorem cell23_3129931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 7].length) (baseStart_3129931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129931 prefixEnd_3129931 := by exact prefixLift 3129931
  have htrace : WordTrace (prefixWord ++ tailWord_3129931) baseStart_3129931 baseEnd_3129931 := by
    simpa [prefixWord, tailWord_3129931, baseEnd_3129931] using wordTrace_append hprefix tailTrace_3129931
  have hstable : (prefixWord ++ tailWord_3129931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129931).length < 2 ^ (prefixWord ++ tailWord_3129931).sum := by decide
  have hdescent : baseEnd_3129931 < baseStart_3129931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129965 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_3129965 : Nat := 118140960795 + 3129965 * 2 ^ 59
def prefixEnd_3129965 : Nat := 4983230072969 + 3 ^ 40 * 3129965 * 2
def baseEnd_3129965 : Nat := 535725492249983910414353

theorem tailTrace_3129965 : CollatzResearch.WordTrace tailWord_3129965 prefixEnd_3129965 535725492249983910414353 := by
  unfold tailWord_3129965
  simp only [CollatzResearch.WordTrace]
  refine ⟨114159202105678835308975349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76106134737119223539316899 114159202105678835308975349)
  ·
    refine ⟨10702425197407390810216439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114159202105678835308975349 10702425197407390810216439)
    ·
      refine ⟨16053637796111086215324659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10702425197407390810216439 16053637796111086215324659)
      ·
        refine ⟨24080456694166629322986989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16053637796111086215324659 24080456694166629322986989)
        ·
          refine ⟨9030171260312485996120121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24080456694166629322986989 9030171260312485996120121)
          ·
            refine ⟨6772628445234364497090091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9030171260312485996120121 6772628445234364497090091)
            ·
              refine ⟨10158942667851546745635137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772628445234364497090091 10158942667851546745635137)
              ·
                refine ⟨7619207000888660059226353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10158942667851546745635137 7619207000888660059226353)
                ·
                  refine ⟨5714405250666495044419765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7619207000888660059226353 5714405250666495044419765)
                  ·
                    refine ⟨535725492249983910414353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5714405250666495044419765 535725492249983910414353)
                    ·
                      rfl

theorem cell23_3129965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_3129965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129965 prefixEnd_3129965 := by exact prefixLift 3129965
  have htrace : WordTrace (prefixWord ++ tailWord_3129965) baseStart_3129965 baseEnd_3129965 := by
    simpa [prefixWord, tailWord_3129965, baseEnd_3129965] using wordTrace_append hprefix tailTrace_3129965
  have hstable : (prefixWord ++ tailWord_3129965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129965).length < 2 ^ (prefixWord ++ tailWord_3129965).sum := by decide
  have hdescent : baseEnd_3129965 < baseStart_3129965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129971 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 5]
def baseStart_3129971 : Nat := 118140960795 + 3129971 * 2 ^ 59
def prefixEnd_3129971 : Nat := 4983230072969 + 3 ^ 40 * 3129971 * 2
def baseEnd_3129971 : Nat := 1607179557633878707768031

theorem tailTrace_3129971 : CollatzResearch.WordTrace tailWord_3129971 prefixEnd_3129971 1607179557633878707768031 := by
  unfold tailWord_3129971
  simp only [CollatzResearch.WordTrace]
  refine ⟨114159420943657098333693767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76106280629104732222462511 114159420943657098333693767)
  ·
    refine ⟨171239131415485647500540651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114159420943657098333693767 171239131415485647500540651)
    ·
      refine ⟨256858697123228471250810977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171239131415485647500540651 256858697123228471250810977)
      ·
        refine ⟨192644022842421353438108233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256858697123228471250810977 192644022842421353438108233)
        ·
          refine ⟨144483017131816015078581175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192644022842421353438108233 144483017131816015078581175)
          ·
            refine ⟨216724525697724022617871763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144483017131816015078581175 216724525697724022617871763)
            ·
              refine ⟨325086788546586033926807645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216724525697724022617871763 325086788546586033926807645)
              ·
                refine ⟨121907545704969762722552867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325086788546586033926807645 121907545704969762722552867)
                ·
                  refine ⟨182861318557454644083829301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121907545704969762722552867 182861318557454644083829301)
                  ·
                    refine ⟨17143248614761372882858997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 182861318557454644083829301 17143248614761372882858997)
                    ·
                      refine ⟨1607179557633878707768031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17143248614761372882858997 1607179557633878707768031)
                      ·
                        rfl

theorem cell23_3129971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_3129971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129971 prefixEnd_3129971 := by exact prefixLift 3129971
  have htrace : WordTrace (prefixWord ++ tailWord_3129971) baseStart_3129971 baseEnd_3129971 := by
    simpa [prefixWord, tailWord_3129971, baseEnd_3129971] using wordTrace_append hprefix tailTrace_3129971
  have hstable : (prefixWord ++ tailWord_3129971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129971).length < 2 ^ (prefixWord ++ tailWord_3129971).sum := by decide
  have hdescent : baseEnd_3129971 < baseStart_3129971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129985 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_3129985 : Nat := 118140960795 + 3129985 * 2 ^ 59
def prefixEnd_3129985 : Nat := 4983230072969 + 3 ^ 40 * 3129985 * 2
def baseEnd_3129985 : Nat := 1607186746363041652992967

theorem tailTrace_3129985 : CollatzResearch.WordTrace tailWord_3129985 prefixEnd_3129985 1607186746363041652992967 := by
  unfold tailWord_3129985
  simp only [CollatzResearch.WordTrace]
  refine ⟨114159931565606378724703409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76106621043737585816468939 114159931565606378724703409)
  ·
    refine ⟨85619948674204784043527557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114159931565606378724703409 85619948674204784043527557)
    ·
      refine ⟨16053740376413397008161417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85619948674204784043527557 16053740376413397008161417)
      ·
        refine ⟨12040305282310047756121063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16053740376413397008161417 12040305282310047756121063)
        ·
          refine ⟨18060457923465071634181595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12040305282310047756121063 18060457923465071634181595)
          ·
            refine ⟨27090686885197607451272393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18060457923465071634181595 27090686885197607451272393)
            ·
              refine ⟨20318015163898205588454295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27090686885197607451272393 20318015163898205588454295)
              ·
                refine ⟨30477022745847308382681443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20318015163898205588454295 30477022745847308382681443)
                ·
                  refine ⟨45715534118770962574022165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30477022745847308382681443 45715534118770962574022165)
                  ·
                    refine ⟨2142915661817388870657289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45715534118770962574022165 2142915661817388870657289)
                    ·
                      refine ⟨1607186746363041652992967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2142915661817388870657289 1607186746363041652992967)
                      ·
                        rfl

theorem cell23_3129985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_3129985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3129985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3129985 prefixEnd_3129985 := by exact prefixLift 3129985
  have htrace : WordTrace (prefixWord ++ tailWord_3129985) baseStart_3129985 baseEnd_3129985 := by
    simpa [prefixWord, tailWord_3129985, baseEnd_3129985] using wordTrace_append hprefix tailTrace_3129985
  have hstable : (prefixWord ++ tailWord_3129985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129985).length < 2 ^ (prefixWord ++ tailWord_3129985).sum := by decide
  have hdescent : baseEnd_3129985 < baseStart_3129985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130002 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_3130002 : Nat := 118140960795 + 3130002 * 2 ^ 59
def prefixEnd_3130002 : Nat := 4983230072969 + 3 ^ 40 * 3130002 * 2
def baseEnd_3130002 : Nat := 1607195475534168086480389

theorem tailTrace_3130002 : CollatzResearch.WordTrace tailWord_3130002 prefixEnd_3130002 1607195475534168086480389 := by
  unfold tailWord_3130002
  simp only [CollatzResearch.WordTrace]
  refine ⟨28540137901636197657018065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76107034404363193752048173 28540137901636197657018065)
  ·
    refine ⟨21405103426227148242763549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28540137901636197657018065 21405103426227148242763549)
    ·
      refine ⟨8026913784835180591036331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21405103426227148242763549 8026913784835180591036331)
      ·
        refine ⟨12040370677252770886554497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8026913784835180591036331 12040370677252770886554497)
        ·
          refine ⟨9030278007939578164915873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12040370677252770886554497 9030278007939578164915873)
          ·
            refine ⟨6772708505954683623686905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9030278007939578164915873 6772708505954683623686905)
            ·
              refine ⟨5079531379466012717765179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6772708505954683623686905 5079531379466012717765179)
              ·
                refine ⟨7619297069199019076647769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079531379466012717765179 7619297069199019076647769)
                ·
                  refine ⟨5714472801899264307485827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7619297069199019076647769 5714472801899264307485827)
                  ·
                    refine ⟨8571709202848896461228741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5714472801899264307485827 8571709202848896461228741)
                    ·
                      refine ⟨1607195475534168086480389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8571709202848896461228741 1607195475534168086480389)
                      ·
                        rfl

theorem cell23_3130002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_3130002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130002 prefixEnd_3130002 := by exact prefixLift 3130002
  have htrace : WordTrace (prefixWord ++ tailWord_3130002) baseStart_3130002 baseEnd_3130002 := by
    simpa [prefixWord, tailWord_3130002, baseEnd_3130002] using wordTrace_append hprefix tailTrace_3130002
  have hstable : (prefixWord ++ tailWord_3130002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130002).length < 2 ^ (prefixWord ++ tailWord_3130002).sum := by decide
  have hdescent : baseEnd_3130002 < baseStart_3130002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130029 : List Nat := [1, 5, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3130029 : Nat := 118140960795 + 3130029 * 2 ^ 59
def prefixEnd_3130029 : Nat := 4983230072969 + 3 ^ 40 * 3130029 * 2
def baseEnd_3130029 : Nat := 535736446503946493614255

theorem tailTrace_3130029 : CollatzResearch.WordTrace tailWord_3130029 prefixEnd_3130029 535736446503946493614255 := by
  unfold tailWord_3130029
  simp only [CollatzResearch.WordTrace]
  refine ⟨114161536377446974239305141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76107690918297982826203427 114161536377446974239305141)
  ·
    refine ⟨10702644035385653834934857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114161536377446974239305141 10702644035385653834934857)
    ·
      refine ⟨8026983026539240376201143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10702644035385653834934857 8026983026539240376201143)
      ·
        refine ⟨12040474539808860564301715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8026983026539240376201143 12040474539808860564301715)
        ·
          refine ⟨18060711809713290846452573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12040474539808860564301715 18060711809713290846452573)
          ·
            refine ⟨6772766928642484067419715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18060711809713290846452573 6772766928642484067419715)
            ·
              refine ⟨10159150392963726101129573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772766928642484067419715 10159150392963726101129573)
              ·
                refine ⟨1904840698680698643961795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10159150392963726101129573 1904840698680698643961795)
                ·
                  refine ⟨2857261048021047965942693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904840698680698643961795 2857261048021047965942693)
                  ·
                    refine ⟨535736446503946493614255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2857261048021047965942693 535736446503946493614255)
                    ·
                      rfl

theorem cell23_3130029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3130029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130029 prefixEnd_3130029 := by exact prefixLift 3130029
  have htrace : WordTrace (prefixWord ++ tailWord_3130029) baseStart_3130029 baseEnd_3130029 := by
    simpa [prefixWord, tailWord_3130029, baseEnd_3130029] using wordTrace_append hprefix tailTrace_3130029
  have hstable : (prefixWord ++ tailWord_3130029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130029).length < 2 ^ (prefixWord ++ tailWord_3130029).sum := by decide
  have hdescent : baseEnd_3130029 < baseStart_3130029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130052 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3130052 : Nat := 118140960795 + 3130052 * 2 ^ 59
def prefixEnd_3130052 : Nat := 4983230072969 + 3 ^ 40 * 3130052 * 2
def baseEnd_3130052 : Nat := 1607221149566892890855159

theorem tailTrace_3130052 : CollatzResearch.WordTrace tailWord_3130052 prefixEnd_3130052 1607221149566892890855159 := by
  unfold tailWord_3130052
  simp only [CollatzResearch.WordTrace]
  refine ⟨57081187628181824583696205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76108250170909099444928273 57081187628181824583696205)
  ·
    refine ⟨21405445360568184218886077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57081187628181824583696205 21405445360568184218886077)
    ·
      refine ⟨8027042010213069082082279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21405445360568184218886077 8027042010213069082082279)
      ·
        refine ⟨12040563015319603623123419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8027042010213069082082279 12040563015319603623123419)
        ·
          refine ⟨18060844522979405434685129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12040563015319603623123419 18060844522979405434685129)
          ·
            refine ⟨13545633392234554076013847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18060844522979405434685129 13545633392234554076013847)
            ·
              refine ⟨20318450088351831114020771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13545633392234554076013847 20318450088351831114020771)
              ·
                refine ⟨30477675132527746671031157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20318450088351831114020771 30477675132527746671031157)
                ·
                  refine ⟨2857282043674476250409171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30477675132527746671031157 2857282043674476250409171)
                  ·
                    refine ⟨4285923065511714375613757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2857282043674476250409171 4285923065511714375613757)
                    ·
                      refine ⟨1607221149566892890855159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4285923065511714375613757 1607221149566892890855159)
                      ·
                        rfl

theorem cell23_3130052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3130052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130052 prefixEnd_3130052 := by exact prefixLift 3130052
  have htrace : WordTrace (prefixWord ++ tailWord_3130052) baseStart_3130052 baseEnd_3130052 := by
    simpa [prefixWord, tailWord_3130052, baseEnd_3130052] using wordTrace_append hprefix tailTrace_3130052
  have hstable : (prefixWord ++ tailWord_3130052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130052).length < 2 ^ (prefixWord ++ tailWord_3130052).sum := by decide
  have hdescent : baseEnd_3130052 < baseStart_3130052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130062 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2]
def baseStart_3130062 : Nat := 118140960795 + 3130062 * 2 ^ 59
def prefixEnd_3130062 : Nat := 4983230072969 + 3 ^ 40 * 3130062 * 2
def baseEnd_3130062 : Nat := 1607226284373437851730113

theorem tailTrace_3130062 : CollatzResearch.WordTrace tailWord_3130062 prefixEnd_3130062 1607226284373437851730113 := by
  unfold tailWord_3130062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14270342498290927609407055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76108493324218280583504293 14270342498290927609407055)
  ·
    refine ⟨21405513747436391414110583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14270342498290927609407055 21405513747436391414110583)
    ·
      refine ⟨32108270621154587121165875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21405513747436391414110583 32108270621154587121165875)
      ·
        refine ⟨48162405931731880681748813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32108270621154587121165875 48162405931731880681748813)
        ·
          refine ⟨18060902224399455255655805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48162405931731880681748813 18060902224399455255655805)
          ·
            refine ⟨6772838334149795720870927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18060902224399455255655805 6772838334149795720870927)
            ·
              refine ⟨10159257501224693581306391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772838334149795720870927 10159257501224693581306391)
              ·
                refine ⟨15238886251837040371959587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10159257501224693581306391 15238886251837040371959587)
                ·
                  refine ⟨22858329377755560557939381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15238886251837040371959587 22858329377755560557939381)
                  ·
                    refine ⟨2142968379164583802306817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22858329377755560557939381 2142968379164583802306817)
                    ·
                      refine ⟨1607226284373437851730113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2142968379164583802306817 1607226284373437851730113)
                      ·
                        rfl

theorem cell23_3130062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_3130062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130062 prefixEnd_3130062 := by exact prefixLift 3130062
  have htrace : WordTrace (prefixWord ++ tailWord_3130062) baseStart_3130062 baseEnd_3130062 := by
    simpa [prefixWord, tailWord_3130062, baseEnd_3130062] using wordTrace_append hprefix tailTrace_3130062
  have hstable : (prefixWord ++ tailWord_3130062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130062).length < 2 ^ (prefixWord ++ tailWord_3130062).sum := by decide
  have hdescent : baseEnd_3130062 < baseStart_3130062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130072 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 1, 5]
def baseStart_3130072 : Nat := 118140960795 + 3130072 * 2 ^ 59
def prefixEnd_3130072 : Nat := 4983230072969 + 3 ^ 40 * 3130072 * 2
def baseEnd_3130072 : Nat := 535743806393327604201689

theorem tailTrace_3130072 : CollatzResearch.WordTrace tailWord_3130072 prefixEnd_3130072 535743806393327604201689 := by
  unfold tailWord_3130072
  simp only [CollatzResearch.WordTrace]
  refine ⟨57081552358145596291560235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76108736477527461722080313 57081552358145596291560235)
  ·
    refine ⟨85622328537218394437340353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57081552358145596291560235 85622328537218394437340353)
    ·
      refine ⟨64216746402913795828005265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85622328537218394437340353 64216746402913795828005265)
      ·
        refine ⟨48162559802185346871003949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64216746402913795828005265 48162559802185346871003949)
        ·
          refine ⟨18060959925819505076626481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48162559802185346871003949 18060959925819505076626481)
          ·
            refine ⟨13545719944364628807469861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18060959925819505076626481 13545719944364628807469861)
            ·
              refine ⟨2539822489568367901400599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13545719944364628807469861 2539822489568367901400599)
              ·
                refine ⟨3809733734352551852100899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539822489568367901400599 3809733734352551852100899)
                ·
                  refine ⟨5714600601528827778151349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3809733734352551852100899 5714600601528827778151349)
                  ·
                    refine ⟨535743806393327604201689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5714600601528827778151349 535743806393327604201689)
                    ·
                      rfl

theorem cell23_3130072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_3130072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130072 prefixEnd_3130072 := by exact prefixLift 3130072
  have htrace : WordTrace (prefixWord ++ tailWord_3130072) baseStart_3130072 baseEnd_3130072 := by
    simpa [prefixWord, tailWord_3130072, baseEnd_3130072] using wordTrace_append hprefix tailTrace_3130072
  have hstable : (prefixWord ++ tailWord_3130072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130072).length < 2 ^ (prefixWord ++ tailWord_3130072).sum := by decide
  have hdescent : baseEnd_3130072 < baseStart_3130072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130095 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 5]
def baseStart_3130095 : Nat := 118140960795 + 3130095 * 2 ^ 59
def prefixEnd_3130095 : Nat := 4983230072969 + 3 ^ 40 * 3130095 * 2
def baseEnd_3130095 : Nat := 1607243229235036222617461

theorem tailTrace_3130095 : CollatzResearch.WordTrace tailWord_3130095 prefixEnd_3130095 1607243229235036222617461 := by
  unfold tailWord_3130095
  simp only [CollatzResearch.WordTrace]
  refine ⟨114163943595207867511207739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76109295730138578340805159 114163943595207867511207739)
  ·
    refine ⟨171245915392811801266811609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114163943595207867511207739 171245915392811801266811609)
    ·
      refine ⟨128434436544608850950108707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171245915392811801266811609 128434436544608850950108707)
      ·
        refine ⟨192651654816913276425163061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128434436544608850950108707 192651654816913276425163061)
        ·
          refine ⟨18061092639085619664859037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192651654816913276425163061 18061092639085619664859037)
          ·
            refine ⟨6772909739657107374322139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18061092639085619664859037 6772909739657107374322139)
            ·
              refine ⟨10159364609485661061483209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772909739657107374322139 10159364609485661061483209)
              ·
                refine ⟨7619523457114245796112407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10159364609485661061483209 7619523457114245796112407)
                ·
                  refine ⟨11429285185671368694168611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7619523457114245796112407 11429285185671368694168611)
                  ·
                    refine ⟨17143927778507053041252917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11429285185671368694168611 17143927778507053041252917)
                    ·
                      refine ⟨1607243229235036222617461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17143927778507053041252917 1607243229235036222617461)
                      ·
                        rfl

theorem cell23_3130095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_3130095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130095 prefixEnd_3130095 := by exact prefixLift 3130095
  have htrace : WordTrace (prefixWord ++ tailWord_3130095) baseStart_3130095 baseEnd_3130095 := by
    simpa [prefixWord, tailWord_3130095, baseEnd_3130095] using wordTrace_append hprefix tailTrace_3130095
  have hstable : (prefixWord ++ tailWord_3130095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130095).length < 2 ^ (prefixWord ++ tailWord_3130095).sum := by decide
  have hdescent : baseEnd_3130095 < baseStart_3130095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130143 : List Nat := [1, 1, 2, 4, 2, 3, 3, 2, 1, 2, 2]
def baseStart_3130143 : Nat := 118140960795 + 3130143 * 2 ^ 59
def prefixEnd_3130143 : Nat := 4983230072969 + 3 ^ 40 * 3130143 * 2
def baseEnd_3130143 : Nat := 1607267876306452034817241

theorem tailTrace_3130143 : CollatzResearch.WordTrace tailWord_3130143 prefixEnd_3130143 1607267876306452034817241 := by
  unfold tailWord_3130143
  simp only [CollatzResearch.WordTrace]
  refine ⟨114165694299033971708955083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76110462866022647805970055 114165694299033971708955083)
  ·
    refine ⟨171248541448550957563432625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114165694299033971708955083 171248541448550957563432625)
    ·
      refine ⟨128436406086413218172574469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171248541448550957563432625 128436406086413218172574469)
      ·
        refine ⟨24081826141202478407357713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128436406086413218172574469 24081826141202478407357713)
        ·
          refine ⟨18061369605901858805518285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24081826141202478407357713 18061369605901858805518285)
          ·
            refine ⟨6773013602213197052069357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18061369605901858805518285 6773013602213197052069357)
            ·
              refine ⟨2539880100829948894526009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6773013602213197052069357 2539880100829948894526009)
              ·
                refine ⟨1904910075622461670894507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2539880100829948894526009 1904910075622461670894507)
                ·
                  refine ⟨2857365113433692506341761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904910075622461670894507 2857365113433692506341761)
                  ·
                    refine ⟨2143023835075269379756321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2857365113433692506341761 2143023835075269379756321)
                    ·
                      refine ⟨1607267876306452034817241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2143023835075269379756321 1607267876306452034817241)
                      ·
                        rfl

theorem cell23_3130143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_3130143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130143 prefixEnd_3130143 := by exact prefixLift 3130143
  have htrace : WordTrace (prefixWord ++ tailWord_3130143) baseStart_3130143 baseEnd_3130143 := by
    simpa [prefixWord, tailWord_3130143, baseEnd_3130143] using wordTrace_append hprefix tailTrace_3130143
  have hstable : (prefixWord ++ tailWord_3130143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130143).length < 2 ^ (prefixWord ++ tailWord_3130143).sum := by decide
  have hdescent : baseEnd_3130143 < baseStart_3130143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130185 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 5]
def baseStart_3130185 : Nat := 118140960795 + 3130185 * 2 ^ 59
def prefixEnd_3130185 : Nat := 4983230072969 + 3 ^ 40 * 3130185 * 2
def baseEnd_3130185 : Nat := 1607289442493940870492047

theorem tailTrace_3130185 : CollatzResearch.WordTrace tailWord_3130185 prefixEnd_3130185 1607289442493940870492047 := by
  unfold tailWord_3130185
  simp only [CollatzResearch.WordTrace]
  refine ⟨114167226164881812881984009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76111484109921208587989339 114167226164881812881984009)
  ·
    refine ⟨85625419623661359661488007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114167226164881812881984009 85625419623661359661488007)
    ·
      refine ⟨128438129435492039492232011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85625419623661359661488007 128438129435492039492232011)
      ·
        refine ⟨192657194153238059238348017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128438129435492039492232011 192657194153238059238348017)
        ·
          refine ⟨144492895614928544428761013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192657194153238059238348017 144492895614928544428761013)
          ·
            refine ⟨13546208963899551040196345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144492895614928544428761013 13546208963899551040196345)
            ·
              refine ⟨10159656722924663280147259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13546208963899551040196345 10159656722924663280147259)
              ·
                refine ⟨15239485084386994920220889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10159656722924663280147259 15239485084386994920220889)
                ·
                  refine ⟨11429613813290246190165667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15239485084386994920220889 11429613813290246190165667)
                  ·
                    refine ⟨17144420719935369285248501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11429613813290246190165667 17144420719935369285248501)
                    ·
                      refine ⟨1607289442493940870492047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17144420719935369285248501 1607289442493940870492047)
                      ·
                        rfl

theorem cell23_3130185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_3130185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130185 prefixEnd_3130185 := by exact prefixLift 3130185
  have htrace : WordTrace (prefixWord ++ tailWord_3130185) baseStart_3130185 baseEnd_3130185 := by
    simpa [prefixWord, tailWord_3130185, baseEnd_3130185] using wordTrace_append hprefix tailTrace_3130185
  have hstable : (prefixWord ++ tailWord_3130185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130185).length < 2 ^ (prefixWord ++ tailWord_3130185).sum := by decide
  have hdescent : baseEnd_3130185 < baseStart_3130185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130212 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_3130212 : Nat := 118140960795 + 3130212 * 2 ^ 59
def prefixEnd_3130212 : Nat := 4983230072969 + 3 ^ 40 * 3130212 * 2
def baseEnd_3130212 : Nat := 1607303306471612264854423

theorem tailTrace_3130212 : CollatzResearch.WordTrace tailWord_3130212 prefixEnd_3130212 1607303306471612264854423 := by
  unfold tailWord_3130212
  simp only [CollatzResearch.WordTrace]
  refine ⟨57084105467891998246608445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76112140623855997662144593 57084105467891998246608445)
  ·
    refine ⟨21406539550459499342478167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57084105467891998246608445 21406539550459499342478167)
    ·
      refine ⟨32109809325689249013717251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21406539550459499342478167 32109809325689249013717251)
      ·
        refine ⟨48164713988533873520575877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32109809325689249013717251 48164713988533873520575877)
        ·
          refine ⟨9030883872850101285107977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48164713988533873520575877 9030883872850101285107977)
          ·
            refine ⟨6773162904637575963830983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9030883872850101285107977 6773162904637575963830983)
            ·
              refine ⟨10159744356956363945746475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6773162904637575963830983 10159744356956363945746475)
              ·
                refine ⟨15239616535434545918619713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10159744356956363945746475 15239616535434545918619713)
                ·
                  refine ⟨11429712401575909438964785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15239616535434545918619713 11429712401575909438964785)
                  ·
                    refine ⟨8572284301181932079223589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11429712401575909438964785 8572284301181932079223589)
                    ·
                      refine ⟨1607303306471612264854423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8572284301181932079223589 1607303306471612264854423)
                      ·
                        rfl

theorem cell23_3130212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_3130212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130212 prefixEnd_3130212 := by exact prefixLift 3130212
  have htrace : WordTrace (prefixWord ++ tailWord_3130212) baseStart_3130212 baseEnd_3130212 := by
    simpa [prefixWord, tailWord_3130212, baseEnd_3130212] using wordTrace_append hprefix tailTrace_3130212
  have hstable : (prefixWord ++ tailWord_3130212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130212).length < 2 ^ (prefixWord ++ tailWord_3130212).sum := by decide
  have hdescent : baseEnd_3130212 < baseStart_3130212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130216 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_3130216 : Nat := 118140960795 + 3130216 * 2 ^ 59
def prefixEnd_3130216 : Nat := 4983230072969 + 3 ^ 40 * 3130216 * 2
def baseEnd_3130216 : Nat := 1607305360394230249204405

theorem tailTrace_3130216 : CollatzResearch.WordTrace tailWord_3130216 prefixEnd_3130216 1607305360394230249204405 := by
  unfold tailWord_3130216
  simp only [CollatzResearch.WordTrace]
  refine ⟨57084178413884752588181251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76112237885179670117575001 57084178413884752588181251)
  ·
    refine ⟨85626267620827128882271877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57084178413884752588181251 85626267620827128882271877)
    ·
      refine ⟨16054925178905086665425977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85626267620827128882271877 16054925178905086665425977)
      ·
        refine ⟨12041193884178814999069483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16054925178905086665425977 12041193884178814999069483)
        ·
          refine ⟨18061790826268222498604225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12041193884178814999069483 18061790826268222498604225)
          ·
            refine ⟨13546343119701166873953169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18061790826268222498604225 13546343119701166873953169)
            ·
              refine ⟨10159757339775875155464877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13546343119701166873953169 10159757339775875155464877)
              ·
                refine ⟨3809909002415953183299329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10159757339775875155464877 3809909002415953183299329)
                ·
                  refine ⟨2857431751811964887474497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3809909002415953183299329 2857431751811964887474497)
                  ·
                    refine ⟨2143073813858973665605873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2857431751811964887474497 2143073813858973665605873)
                    ·
                      refine ⟨1607305360394230249204405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2143073813858973665605873 1607305360394230249204405)
                      ·
                        rfl

theorem cell23_3130216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_3130216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130216 prefixEnd_3130216 := by exact prefixLift 3130216
  have htrace : WordTrace (prefixWord ++ tailWord_3130216) baseStart_3130216 baseEnd_3130216 := by
    simpa [prefixWord, tailWord_3130216, baseEnd_3130216] using wordTrace_append hprefix tailTrace_3130216
  have hstable : (prefixWord ++ tailWord_3130216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130216).length < 2 ^ (prefixWord ++ tailWord_3130216).sum := by decide
  have hdescent : baseEnd_3130216 < baseStart_3130216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130295 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 8]
def baseStart_3130295 : Nat := 118140960795 + 3130295 * 2 ^ 59
def prefixEnd_3130295 : Nat := 4983230072969 + 3 ^ 40 * 3130295 * 2
def baseEnd_3130295 : Nat := 178593991707326160012949

theorem tailTrace_3130295 : CollatzResearch.WordTrace tailWord_3130295 prefixEnd_3130295 178593991707326160012949 := by
  unfold tailWord_3130295
  simp only [CollatzResearch.WordTrace]
  refine ⟨114171238194483301668488339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76114158796322201112325559 114171238194483301668488339)
  ·
    refine ⟨171256857291724952502732509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114171238194483301668488339 171256857291724952502732509)
    ·
      refine ⟨64221321484396857188524691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171256857291724952502732509 64221321484396857188524691)
      ·
        refine ⟨96331982226595285782787037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64221321484396857188524691 96331982226595285782787037)
        ·
          refine ⟨36124493334973232168545139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96331982226595285782787037 36124493334973232168545139)
          ·
            refine ⟨54186740002459848252817709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36124493334973232168545139 54186740002459848252817709)
            ·
              refine ⟨20320027500922443094806641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54186740002459848252817709 20320027500922443094806641)
              ·
                refine ⟨15240020625691832321104981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20320027500922443094806641 15240020625691832321104981)
                ·
                  refine ⟨178593991707326160012949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15240020625691832321104981 178593991707326160012949)
                  ·
                    rfl

theorem cell23_3130295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 8].length) (baseStart_3130295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130295 prefixEnd_3130295 := by exact prefixLift 3130295
  have htrace : WordTrace (prefixWord ++ tailWord_3130295) baseStart_3130295 baseEnd_3130295 := by
    simpa [prefixWord, tailWord_3130295, baseEnd_3130295] using wordTrace_append hprefix tailTrace_3130295
  have hstable : (prefixWord ++ tailWord_3130295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130295).length < 2 ^ (prefixWord ++ tailWord_3130295).sum := by decide
  have hdescent : baseEnd_3130295 < baseStart_3130295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130329 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 6]
def baseStart_3130329 : Nat := 118140960795 + 3130329 * 2 ^ 59
def prefixEnd_3130329 : Nat := 4983230072969 + 3 ^ 40 * 3130329 * 2
def baseEnd_3130329 : Nat := 178595931523132034121265

theorem tailTrace_3130329 : CollatzResearch.WordTrace tailWord_3130329 prefixEnd_3130329 178595931523132034121265 := by
  unfold tailWord_3130329
  simp only [CollatzResearch.WordTrace]
  refine ⟨114172478276360125475226041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76114985517573416983484027 114172478276360125475226041)
  ·
    refine ⟨85629358707270094106419531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114172478276360125475226041 85629358707270094106419531)
    ·
      refine ⟨128444038060905141159629297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85629358707270094106419531 128444038060905141159629297)
      ·
        refine ⟨96333028545678855869721973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128444038060905141159629297 96333028545678855869721973)
        ·
          refine ⟨9031221426157392737786435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96333028545678855869721973 9031221426157392737786435)
          ·
            refine ⟨13546832139236089106679653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9031221426157392737786435 13546832139236089106679653)
            ·
              refine ⟨2540031026106766707502435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13546832139236089106679653 2540031026106766707502435)
              ·
                refine ⟨3810046539160150061253653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540031026106766707502435 3810046539160150061253653)
                ·
                  refine ⟨178595931523132034121265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3810046539160150061253653 178595931523132034121265)
                  ·
                    rfl

theorem cell23_3130329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 6].length) (baseStart_3130329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130329 prefixEnd_3130329 := by exact prefixLift 3130329
  have htrace : WordTrace (prefixWord ++ tailWord_3130329) baseStart_3130329 baseEnd_3130329 := by
    simpa [prefixWord, tailWord_3130329, baseEnd_3130329] using wordTrace_append hprefix tailTrace_3130329
  have hstable : (prefixWord ++ tailWord_3130329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130329).length < 2 ^ (prefixWord ++ tailWord_3130329).sum := by decide
  have hdescent : baseEnd_3130329 < baseStart_3130329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130339 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 5, 1, 3]
def baseStart_3130339 : Nat := 118140960795 + 3130339 * 2 ^ 59
def prefixEnd_3130339 : Nat := 4983230072969 + 3 ^ 40 * 3130339 * 2
def baseEnd_3130339 : Nat := 1607368518514733267966339

theorem tailTrace_3130339 : CollatzResearch.WordTrace tailWord_3130339 prefixEnd_3130339 1607368518514733267966339 := by
  unfold tailWord_3130339
  simp only [CollatzResearch.WordTrace]
  refine ⟨114172843006323897183090071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76115228670882598122060047 114172843006323897183090071)
  ·
    refine ⟨171259264509485845774635107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114172843006323897183090071 171259264509485845774635107)
    ·
      refine ⟨256888896764228768661952661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171259264509485845774635107 256888896764228768661952661)
      ·
        refine ⟨12041667035823223531029031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 256888896764228768661952661 12041667035823223531029031)
        ·
          refine ⟨18062500553734835296543547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12041667035823223531029031 18062500553734835296543547)
          ·
            refine ⟨27093750830602252944815321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18062500553734835296543547 27093750830602252944815321)
            ·
              refine ⟨20320313122951689708611491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27093750830602252944815321 20320313122951689708611491)
              ·
                refine ⟨30480469684427534562917237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20320313122951689708611491 30480469684427534562917237)
                ·
                  refine ⟨2857544032915081365273491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30480469684427534562917237 2857544032915081365273491)
                  ·
                    refine ⟨4286316049372622047910237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2857544032915081365273491 4286316049372622047910237)
                    ·
                      refine ⟨1607368518514733267966339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4286316049372622047910237 1607368518514733267966339)
                      ·
                        rfl

theorem cell23_3130339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_3130339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130339 prefixEnd_3130339 := by exact prefixLift 3130339
  have htrace : WordTrace (prefixWord ++ tailWord_3130339) baseStart_3130339 baseEnd_3130339 := by
    simpa [prefixWord, tailWord_3130339, baseEnd_3130339] using wordTrace_append hprefix tailTrace_3130339
  have hstable : (prefixWord ++ tailWord_3130339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130339).length < 2 ^ (prefixWord ++ tailWord_3130339).sum := by decide
  have hdescent : baseEnd_3130339 < baseStart_3130339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130389 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 1, 6]
def baseStart_3130389 : Nat := 118140960795 + 3130389 * 2 ^ 59
def prefixEnd_3130389 : Nat := 4983230072969 + 3 ^ 40 * 3130389 * 2
def baseEnd_3130389 : Nat := 535798064182486024113703

theorem tailTrace_3130389 : CollatzResearch.WordTrace tailWord_3130389 prefixEnd_3130389 535798064182486024113703 := by
  unfold tailWord_3130389
  simp only [CollatzResearch.WordTrace]
  refine ⟨114174666656142755722410221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76116444437428503814940147 114174666656142755722410221)
  ·
    refine ⟨42815499996053533395903833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114174666656142755722410221 42815499996053533395903833)
    ·
      refine ⟨32111624997040150046927875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42815499996053533395903833 32111624997040150046927875)
      ·
        refine ⟨48167437495560225070391813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32111624997040150046927875 48167437495560225070391813)
        ·
          refine ⟨9031394530417542200698465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48167437495560225070391813 9031394530417542200698465)
          ·
            refine ⟨6773545897813156650523849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9031394530417542200698465 6773545897813156650523849)
            ·
              refine ⟨5080159423359867487892887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6773545897813156650523849 5080159423359867487892887)
              ·
                refine ⟨7620239135039801231839331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5080159423359867487892887 7620239135039801231839331)
                ·
                  refine ⟨11430358702559701847758997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7620239135039801231839331 11430358702559701847758997)
                  ·
                    refine ⟨535798064182486024113703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11430358702559701847758997 535798064182486024113703)
                    ·
                      rfl

theorem cell23_3130389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_3130389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130389 prefixEnd_3130389 := by exact prefixLift 3130389
  have htrace : WordTrace (prefixWord ++ tailWord_3130389) baseStart_3130389 baseEnd_3130389 := by
    simpa [prefixWord, tailWord_3130389, baseEnd_3130389] using wordTrace_append hprefix tailTrace_3130389
  have hstable : (prefixWord ++ tailWord_3130389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130389).length < 2 ^ (prefixWord ++ tailWord_3130389).sum := by decide
  have hdescent : baseEnd_3130389 < baseStart_3130389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130399 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 3]
def baseStart_3130399 : Nat := 118140960795 + 3130399 * 2 ^ 59
def prefixEnd_3130399 : Nat := 4983230072969 + 3 ^ 40 * 3130399 * 2
def baseEnd_3130399 : Nat := 1607399327354003033216063

theorem tailTrace_3130399 : CollatzResearch.WordTrace tailWord_3130399 prefixEnd_3130399 1607399327354003033216063 := by
  unfold tailWord_3130399
  simp only [CollatzResearch.WordTrace]
  refine ⟨114175031386106527430274251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76116687590737684953516167 114175031386106527430274251)
  ·
    refine ⟨171262547079159791145411377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114175031386106527430274251 171262547079159791145411377)
    ·
      refine ⟨128446910309369843359058533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171262547079159791145411377 128446910309369843359058533)
      ·
        refine ⟨24083795683006845629823475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128446910309369843359058533 24083795683006845629823475)
        ·
          refine ⟨36125693524510268444735213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24083795683006845629823475 36125693524510268444735213)
          ·
            refine ⟨13547135071691350666775705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36125693524510268444735213 13547135071691350666775705)
            ·
              refine ⟨10160351303768513000081779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13547135071691350666775705 10160351303768513000081779)
              ·
                refine ⟨15240526955652769500122669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10160351303768513000081779 15240526955652769500122669)
                ·
                  refine ⟨5715197608369788562546001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15240526955652769500122669 5715197608369788562546001)
                  ·
                    refine ⟨4286398206277341421909501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5715197608369788562546001 4286398206277341421909501)
                    ·
                      refine ⟨1607399327354003033216063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4286398206277341421909501 1607399327354003033216063)
                      ·
                        rfl

theorem cell23_3130399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_3130399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130399 prefixEnd_3130399 := by exact prefixLift 3130399
  have htrace : WordTrace (prefixWord ++ tailWord_3130399) baseStart_3130399 baseEnd_3130399 := by
    simpa [prefixWord, tailWord_3130399, baseEnd_3130399] using wordTrace_append hprefix tailTrace_3130399
  have hstable : (prefixWord ++ tailWord_3130399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130399).length < 2 ^ (prefixWord ++ tailWord_3130399).sum := by decide
  have hdescent : baseEnd_3130399 < baseStart_3130399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130400 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3130400 : Nat := 118140960795 + 3130400 * 2 ^ 59
def prefixEnd_3130400 : Nat := 4983230072969 + 3 ^ 40 * 3130400 * 2
def baseEnd_3130400 : Nat := 1607399840834657529303559

theorem tailTrace_3130400 : CollatzResearch.WordTrace tailWord_3130400 prefixEnd_3130400 1607399840834657529303559 := by
  unfold tailWord_3130400
  simp only [CollatzResearch.WordTrace]
  refine ⟨57087533929551452300530327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76116711906068603067373769 57087533929551452300530327)
  ·
    refine ⟨85631300894327178450795491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57087533929551452300530327 85631300894327178450795491)
    ·
      refine ⟨128446951341490767676193237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85631300894327178450795491 128446951341490767676193237)
      ·
        refine ⟨3010475422066189867410779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 128446951341490767676193237 3010475422066189867410779)
        ·
          refine ⟨4515713133099284801116169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010475422066189867410779 4515713133099284801116169)
          ·
            refine ⟨3386784849824463600837127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4515713133099284801116169 3386784849824463600837127)
            ·
              refine ⟨5080177274736695401255691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3386784849824463600837127 5080177274736695401255691)
              ·
                refine ⟨7620265912105043101883537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5080177274736695401255691 7620265912105043101883537)
                ·
                  refine ⟨5715199434078782326412653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7620265912105043101883537 5715199434078782326412653)
                  ·
                    refine ⟨2143199787779543372404745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5715199434078782326412653 2143199787779543372404745)
                    ·
                      refine ⟨1607399840834657529303559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2143199787779543372404745 1607399840834657529303559)
                      ·
                        rfl

theorem cell23_3130400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3130400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130400 prefixEnd_3130400 := by exact prefixLift 3130400
  have htrace : WordTrace (prefixWord ++ tailWord_3130400) baseStart_3130400 baseEnd_3130400 := by
    simpa [prefixWord, tailWord_3130400, baseEnd_3130400] using wordTrace_append hprefix tailTrace_3130400
  have hstable : (prefixWord ++ tailWord_3130400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130400).length < 2 ^ (prefixWord ++ tailWord_3130400).sum := by decide
  have hdescent : baseEnd_3130400 < baseStart_3130400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130410 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 1, 5]
def baseStart_3130410 : Nat := 118140960795 + 3130410 * 2 ^ 59
def prefixEnd_3130410 : Nat := 4983230072969 + 3 ^ 40 * 3130410 * 2
def baseEnd_3130410 : Nat := 535801658547067496726171

theorem tailTrace_3130410 : CollatzResearch.WordTrace tailWord_3130410 prefixEnd_3130410 535801658547067496726171 := by
  unfold tailWord_3130410
  simp only [CollatzResearch.WordTrace]
  refine ⟨28543858147266669077231171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76116955059377784205949789 28543858147266669077231171)
  ·
    refine ⟨42815787220900003615846757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28543858147266669077231171 42815787220900003615846757)
    ·
      refine ⟨8027960103918750677971267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42815787220900003615846757 8027960103918750677971267)
      ·
        refine ⟨12041940155878126016956901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8027960103918750677971267 12041940155878126016956901)
        ·
          refine ⟨2257863779227148628179419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12041940155878126016956901 2257863779227148628179419)
          ·
            refine ⟨3386795668840722942269129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257863779227148628179419 3386795668840722942269129)
            ·
              refine ⟨2540096751630542206701847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3386795668840722942269129 2540096751630542206701847)
              ·
                refine ⟨3810145127445813310052771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540096751630542206701847 3810145127445813310052771)
                ·
                  refine ⟨5715217691168719965079157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810145127445813310052771 5715217691168719965079157)
                  ·
                    refine ⟨535801658547067496726171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5715217691168719965079157 535801658547067496726171)
                    ·
                      rfl

theorem cell23_3130410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_3130410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130410 prefixEnd_3130410 := by exact prefixLift 3130410
  have htrace : WordTrace (prefixWord ++ tailWord_3130410) baseStart_3130410 baseEnd_3130410 := by
    simpa [prefixWord, tailWord_3130410, baseEnd_3130410] using wordTrace_append hprefix tailTrace_3130410
  have hstable : (prefixWord ++ tailWord_3130410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130410).length < 2 ^ (prefixWord ++ tailWord_3130410).sum := by decide
  have hdescent : baseEnd_3130410 < baseStart_3130410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130430 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_3130430 : Nat := 118140960795 + 3130430 * 2 ^ 59
def prefixEnd_3130430 : Nat := 4983230072969 + 3 ^ 40 * 3130430 * 2
def baseEnd_3130430 : Nat := 1607415245254292411928421

theorem tailTrace_3130430 : CollatzResearch.WordTrace tailWord_3130430 prefixEnd_3130430 1607415245254292411928421 := by
  unfold tailWord_3130430
  simp only [CollatzResearch.WordTrace]
  refine ⟨14272020256124277465581593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76117441365996146483101829 14272020256124277465581593)
  ·
    refine ⟨10704015192093208099186195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14272020256124277465581593 10704015192093208099186195)
    ·
      refine ⟨16056022788139812148779293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10704015192093208099186195 16056022788139812148779293)
      ·
        refine ⟨6021008545552429555792235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16056022788139812148779293 6021008545552429555792235)
        ·
          refine ⟨9031512818328644333688353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6021008545552429555792235 9031512818328644333688353)
          ·
            refine ⟨6773634613746483250266265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9031512818328644333688353 6773634613746483250266265)
            ·
              refine ⟨5080225960309862437699699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6773634613746483250266265 5080225960309862437699699)
              ·
                refine ⟨7620338940464793656549549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5080225960309862437699699 7620338940464793656549549)
                ·
                  refine ⟨2857627102674297621206081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7620338940464793656549549 2857627102674297621206081)
                  ·
                    refine ⟨2143220327005723215904561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2857627102674297621206081 2143220327005723215904561)
                    ·
                      refine ⟨1607415245254292411928421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2143220327005723215904561 1607415245254292411928421)
                      ·
                        rfl

theorem cell23_3130430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_3130430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130430 prefixEnd_3130430 := by exact prefixLift 3130430
  have htrace : WordTrace (prefixWord ++ tailWord_3130430) baseStart_3130430 baseEnd_3130430 := by
    simpa [prefixWord, tailWord_3130430, baseEnd_3130430] using wordTrace_append hprefix tailTrace_3130430
  have hstable : (prefixWord ++ tailWord_3130430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130430).length < 2 ^ (prefixWord ++ tailWord_3130430).sum := by decide
  have hdescent : baseEnd_3130430 < baseStart_3130430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130546 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2]
def baseStart_3130546 : Nat := 118140960795 + 3130546 * 2 ^ 59
def prefixEnd_3130546 : Nat := 4983230072969 + 3 ^ 40 * 3130546 * 2
def baseEnd_3130546 : Nat := 1607474809010213958077887

theorem tailTrace_3130546 : CollatzResearch.WordTrace tailWord_3130546 prefixEnd_3130546 1607474809010213958077887 := by
  unfold tailWord_3130546
  simp only [CollatzResearch.WordTrace]
  refine ⟨28545098229143492883968873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76120261944382647690583661 28545098229143492883968873)
  ·
    refine ⟨21408823671857619662976655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28545098229143492883968873 21408823671857619662976655)
    ·
      refine ⟨32113235507786429494464983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21408823671857619662976655 32113235507786429494464983)
      ·
        refine ⟨48169853261679644241697475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32113235507786429494464983 48169853261679644241697475)
        ·
          refine ⟨72254779892519466362546213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48169853261679644241697475 72254779892519466362546213)
          ·
            refine ⟨13547771229847399942977415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72254779892519466362546213 13547771229847399942977415)
            ·
              refine ⟨20321656844771099914466123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13547771229847399942977415 20321656844771099914466123)
              ·
                refine ⟨30482485267156649871699185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20321656844771099914466123 30482485267156649871699185)
                ·
                  refine ⟨22861863950367487403774389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30482485267156649871699185 22861863950367487403774389)
                  ·
                    refine ⟨2143299745346951944103849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22861863950367487403774389 2143299745346951944103849)
                    ·
                      refine ⟨1607474809010213958077887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2143299745346951944103849 1607474809010213958077887)
                      ·
                        rfl

theorem cell23_3130546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_3130546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130546 prefixEnd_3130546 := by exact prefixLift 3130546
  have htrace : WordTrace (prefixWord ++ tailWord_3130546) baseStart_3130546 baseEnd_3130546 := by
    simpa [prefixWord, tailWord_3130546, baseEnd_3130546] using wordTrace_append hprefix tailTrace_3130546
  have hstable : (prefixWord ++ tailWord_3130546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130546).length < 2 ^ (prefixWord ++ tailWord_3130546).sum := by decide
  have hdescent : baseEnd_3130546 < baseStart_3130546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130550 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3130550 : Nat := 118140960795 + 3130550 * 2 ^ 59
def prefixEnd_3130550 : Nat := 4983230072969 + 3 ^ 40 * 3130550 * 2
def baseEnd_3130550 : Nat := 1607476862932831942427869

theorem tailTrace_3130550 : CollatzResearch.WordTrace tailWord_3130550 prefixEnd_3130550 1607476862932831942427869 := by
  unfold tailWord_3130550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7136283675534967513688819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76120359205706320146014069 7136283675534967513688819)
  ·
    refine ⟨10704425513302451270533229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7136283675534967513688819 10704425513302451270533229)
    ·
      refine ⟨4014159567488419226449961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10704425513302451270533229 4014159567488419226449961)
      ·
        refine ⟨3010619675616314419837471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4014159567488419226449961 3010619675616314419837471)
        ·
          refine ⟨4515929513424471629756207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010619675616314419837471 4515929513424471629756207)
          ·
            refine ⟨6773894270136707444634311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4515929513424471629756207 6773894270136707444634311)
            ·
              refine ⟨10160841405205061166951467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6773894270136707444634311 10160841405205061166951467)
              ·
                refine ⟨15241262107807591750427201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10160841405205061166951467 15241262107807591750427201)
                ·
                  refine ⟨11430946580855693812820401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15241262107807591750427201 11430946580855693812820401)
                  ·
                    refine ⟨8573209935641770359615301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11430946580855693812820401 8573209935641770359615301)
                    ·
                      refine ⟨1607476862932831942427869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8573209935641770359615301 1607476862932831942427869)
                      ·
                        rfl

theorem cell23_3130550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3130550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130550 prefixEnd_3130550 := by exact prefixLift 3130550
  have htrace : WordTrace (prefixWord ++ tailWord_3130550) baseStart_3130550 baseEnd_3130550 := by
    simpa [prefixWord, tailWord_3130550, baseEnd_3130550] using wordTrace_append hprefix tailTrace_3130550
  have hstable : (prefixWord ++ tailWord_3130550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130550).length < 2 ^ (prefixWord ++ tailWord_3130550).sum := by decide
  have hdescent : baseEnd_3130550 < baseStart_3130550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130559 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 4]
def baseStart_3130559 : Nat := 118140960795 + 3130559 * 2 ^ 59
def prefixEnd_3130559 : Nat := 4983230072969 + 3 ^ 40 * 3130559 * 2
def baseEnd_3130559 : Nat := 1607481484258722407215327

theorem tailTrace_3130559 : CollatzResearch.WordTrace tailWord_3130559 prefixEnd_3130559 1607481484258722407215327 := by
  unfold tailWord_3130559
  simp only [CollatzResearch.WordTrace]
  refine ⟨114180867065526874756098731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76120578043684583170732487 114180867065526874756098731)
  ·
    refine ⟨171271300598290312134148097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114180867065526874756098731 171271300598290312134148097)
    ·
      refine ⟨128453475448717734100611073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171271300598290312134148097 128453475448717734100611073)
      ·
        refine ⟨96340106586538300575458305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128453475448717734100611073 96340106586538300575458305)
        ·
          refine ⟨72255079939903725431593729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96340106586538300575458305 72255079939903725431593729)
          ·
            refine ⟨54191309954927794073695297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72255079939903725431593729 54191309954927794073695297)
            ·
              refine ⟨40643482466195845555271473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54191309954927794073695297 40643482466195845555271473)
              ·
                refine ⟨30482611849646884166453605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40643482466195845555271473 30482611849646884166453605)
                ·
                  refine ⟨5715489721808790781210051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30482611849646884166453605 5715489721808790781210051)
                  ·
                    refine ⟨8573234582713186171815077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5715489721808790781210051 8573234582713186171815077)
                    ·
                      refine ⟨1607481484258722407215327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8573234582713186171815077 1607481484258722407215327)
                      ·
                        rfl

theorem cell23_3130559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_3130559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130559 prefixEnd_3130559 := by exact prefixLift 3130559
  have htrace : WordTrace (prefixWord ++ tailWord_3130559) baseStart_3130559 baseEnd_3130559 := by
    simpa [prefixWord, tailWord_3130559, baseEnd_3130559] using wordTrace_append hprefix tailTrace_3130559
  have hstable : (prefixWord ++ tailWord_3130559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130559).length < 2 ^ (prefixWord ++ tailWord_3130559).sum := by decide
  have hdescent : baseEnd_3130559 < baseStart_3130559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130579 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 3]
def baseStart_3130579 : Nat := 118140960795 + 3130579 * 2 ^ 59
def prefixEnd_3130579 : Nat := 4983230072969 + 3 ^ 40 * 3130579 * 2
def baseEnd_3130579 : Nat := 1607491753871812328965235

theorem tailTrace_3130579 : CollatzResearch.WordTrace tailWord_3130579 prefixEnd_3130579 1607491753871812328965235 := by
  unfold tailWord_3130579
  simp only [CollatzResearch.WordTrace]
  refine ⟨114181596525454418171826791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76121064350302945447884527 114181596525454418171826791)
  ·
    refine ⟨171272394788181627257740187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114181596525454418171826791 171272394788181627257740187)
    ·
      refine ⟨256908592182272440886610281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171272394788181627257740187 256908592182272440886610281)
      ·
        refine ⟨192681444136704330664957711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256908592182272440886610281 192681444136704330664957711)
        ·
          refine ⟨289022166205056495997436567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192681444136704330664957711 289022166205056495997436567)
          ·
            refine ⟨433533249307584743996154851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289022166205056495997436567 433533249307584743996154851)
            ·
              refine ⟨650299873961377115994232277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433533249307584743996154851 650299873961377115994232277)
              ·
                refine ⟨15241403295969776156114819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 650299873961377115994232277 15241403295969776156114819)
                ·
                  refine ⟨22862104943954664234172229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15241403295969776156114819 22862104943954664234172229)
                  ·
                    refine ⟨4286644676991499543907293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22862104943954664234172229 4286644676991499543907293)
                    ·
                      refine ⟨1607491753871812328965235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4286644676991499543907293 1607491753871812328965235)
                      ·
                        rfl

theorem cell23_3130579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 3].length) (baseStart_3130579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130579 prefixEnd_3130579 := by exact prefixLift 3130579
  have htrace : WordTrace (prefixWord ++ tailWord_3130579) baseStart_3130579 baseEnd_3130579 := by
    simpa [prefixWord, tailWord_3130579, baseEnd_3130579] using wordTrace_append hprefix tailTrace_3130579
  have hstable : (prefixWord ++ tailWord_3130579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130579).length < 2 ^ (prefixWord ++ tailWord_3130579).sum := by decide
  have hdescent : baseEnd_3130579 < baseStart_3130579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130596 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_3130596 : Nat := 118140960795 + 3130596 * 2 ^ 59
def prefixEnd_3130596 : Nat := 4983230072969 + 3 ^ 40 * 3130596 * 2
def baseEnd_3130596 : Nat := 1607500483042938762452657

theorem tailTrace_3130596 : CollatzResearch.WordTrace tailWord_3130596 prefixEnd_3130596 1607500483042938762452657 := by
  unfold tailWord_3130596
  simp only [CollatzResearch.WordTrace]
  refine ⟨57091108283196415037597821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76121477710928553383463761 57091108283196415037597821)
  ·
    refine ⟨21409165606198655639099183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57091108283196415037597821 21409165606198655639099183)
    ·
      refine ⟨32113748409297983458648775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21409165606198655639099183 32113748409297983458648775)
      ·
        refine ⟨48170622613946975187973163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32113748409297983458648775 48170622613946975187973163)
        ·
          refine ⟨72255933920920462781959745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48170622613946975187973163 72255933920920462781959745)
          ·
            refine ⟨54191950440690347086469809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72255933920920462781959745 54191950440690347086469809)
            ·
              refine ⟨40643962830517760314852357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54191950440690347086469809 40643962830517760314852357)
              ·
                refine ⟨7620743030722080059034817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40643962830517760314852357 7620743030722080059034817)
                ·
                  refine ⟨5715557273041560044276113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7620743030722080059034817 5715557273041560044276113)
                  ·
                    refine ⟨4286667954781170033207085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5715557273041560044276113 4286667954781170033207085)
                    ·
                      refine ⟨1607500483042938762452657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4286667954781170033207085 1607500483042938762452657)
                      ·
                        rfl

theorem cell23_3130596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_3130596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130596 prefixEnd_3130596 := by exact prefixLift 3130596
  have htrace : WordTrace (prefixWord ++ tailWord_3130596) baseStart_3130596 baseEnd_3130596 := by
    simpa [prefixWord, tailWord_3130596, baseEnd_3130596] using wordTrace_append hprefix tailTrace_3130596
  have hstable : (prefixWord ++ tailWord_3130596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130596).length < 2 ^ (prefixWord ++ tailWord_3130596).sum := by decide
  have hdescent : baseEnd_3130596 < baseStart_3130596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130603 : List Nat := [1, 1, 1, 1, 2, 6, 2, 4, 1, 4]
def baseStart_3130603 : Nat := 118140960795 + 3130603 * 2 ^ 59
def prefixEnd_3130603 : Nat := 4983230072969 + 3 ^ 40 * 3130603 * 2
def baseEnd_3130603 : Nat := 535834692469173411688375

theorem tailTrace_3130603 : CollatzResearch.WordTrace tailWord_3130603 prefixEnd_3130603 535834692469173411688375 := by
  unfold tailWord_3130603
  simp only [CollatzResearch.WordTrace]
  refine ⟨114182471877367470270700463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76121647918244980180466975 114182471877367470270700463)
  ·
    refine ⟨171273707816051205406050695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114182471877367470270700463 171273707816051205406050695)
    ·
      refine ⟨256910561724076808109076043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171273707816051205406050695 256910561724076808109076043)
      ·
        refine ⟨385365842586115212163614065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256910561724076808109076043 385365842586115212163614065)
        ·
          refine ⟨289024381939586409122710549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385365842586115212163614065 289024381939586409122710549)
          ·
            refine ⟨13548017903418112927627057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 289024381939586409122710549 13548017903418112927627057)
            ·
              refine ⟨10161013427563584695720293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13548017903418112927627057 10161013427563584695720293)
              ·
                refine ⟨1905190017668172130447555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10161013427563584695720293 1905190017668172130447555)
                ·
                  refine ⟨2857785026502258195671333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905190017668172130447555 2857785026502258195671333)
                  ·
                    refine ⟨535834692469173411688375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2857785026502258195671333 535834692469173411688375)
                    ·
                      rfl

theorem cell23_3130603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 1, 4].length) (baseStart_3130603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130603 prefixEnd_3130603 := by exact prefixLift 3130603
  have htrace : WordTrace (prefixWord ++ tailWord_3130603) baseStart_3130603 baseEnd_3130603 := by
    simpa [prefixWord, tailWord_3130603, baseEnd_3130603] using wordTrace_append hprefix tailTrace_3130603
  have hstable : (prefixWord ++ tailWord_3130603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130603).length < 2 ^ (prefixWord ++ tailWord_3130603).sum := by decide
  have hdescent : baseEnd_3130603 < baseStart_3130603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130654 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3130654 : Nat := 118140960795 + 3130654 * 2 ^ 59
def prefixEnd_3130654 : Nat := 4983230072969 + 3 ^ 40 * 3130654 * 2
def baseEnd_3130654 : Nat := 535843421640299845175797

theorem tailTrace_3130654 : CollatzResearch.WordTrace tailWord_3130654 prefixEnd_3130654 535843421640299845175797 := by
  unfold tailWord_3130654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14273041500022838247600877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76122888000121803987204677 14273041500022838247600877)
  ·
    refine ⟨5352390562508564342850329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14273041500022838247600877 5352390562508564342850329)
    ·
      refine ⟨4014292921881423257137747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5352390562508564342850329 4014292921881423257137747)
      ·
        refine ⟨6021439382822134885706621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4014292921881423257137747 6021439382822134885706621)
        ·
          refine ⟨2258039768558300582139983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6021439382822134885706621 2258039768558300582139983)
          ·
            refine ⟨3387059652837450873209975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258039768558300582139983 3387059652837450873209975)
            ·
              refine ⟨5080589479256176309814963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3387059652837450873209975 5080589479256176309814963)
              ·
                refine ⟨7620884218884264464722445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5080589479256176309814963 7620884218884264464722445)
                ·
                  refine ⟨2857831582081599174270917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7620884218884264464722445 2857831582081599174270917)
                  ·
                    refine ⟨535843421640299845175797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2857831582081599174270917 535843421640299845175797)
                    ·
                      rfl

theorem cell23_3130654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3130654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130654 prefixEnd_3130654 := by exact prefixLift 3130654
  have htrace : WordTrace (prefixWord ++ tailWord_3130654) baseStart_3130654 baseEnd_3130654 := by
    simpa [prefixWord, tailWord_3130654, baseEnd_3130654] using wordTrace_append hprefix tailTrace_3130654
  have hstable : (prefixWord ++ tailWord_3130654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130654).length < 2 ^ (prefixWord ++ tailWord_3130654).sum := by decide
  have hdescent : baseEnd_3130654 < baseStart_3130654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130700 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 1, 1, 4]
def baseStart_3130700 : Nat := 118140960795 + 3130700 * 2 ^ 59
def prefixEnd_3130700 : Nat := 4983230072969 + 3 ^ 40 * 3130700 * 2
def baseEnd_3130700 : Nat := 1607553885031006355552179

theorem tailTrace_3130700 : CollatzResearch.WordTrace tailWord_3130700 prefixEnd_3130700 1607553885031006355552179 := by
  unfold tailWord_3130700
  simp only [CollatzResearch.WordTrace]
  refine ⟨57093004879008027918490777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76124006505344037224654369 57093004879008027918490777)
  ·
    refine ⟨42819753659256020938868083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57093004879008027918490777 42819753659256020938868083)
    ·
      refine ⟨64229630488884031408302125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42819753659256020938868083 64229630488884031408302125)
      ·
        refine ⟨24086111433331511778113297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64229630488884031408302125 24086111433331511778113297)
        ·
          refine ⟨18064583574998633833584973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24086111433331511778113297 18064583574998633833584973)
          ·
            refine ⟨6774218840624487687594365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18064583574998633833584973 6774218840624487687594365)
            ·
              refine ⟨2540332065234182882847887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6774218840624487687594365 2540332065234182882847887)
              ·
                refine ⟨3810498097851274324271831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540332065234182882847887 3810498097851274324271831)
                ·
                  refine ⟨5715747146776911486407747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810498097851274324271831 5715747146776911486407747)
                  ·
                    refine ⟨8573620720165367229611621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5715747146776911486407747 8573620720165367229611621)
                    ·
                      refine ⟨1607553885031006355552179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8573620720165367229611621 1607553885031006355552179)
                      ·
                        rfl

theorem cell23_3130700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_3130700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130700 prefixEnd_3130700 := by exact prefixLift 3130700
  have htrace : WordTrace (prefixWord ++ tailWord_3130700) baseStart_3130700 baseEnd_3130700 := by
    simpa [prefixWord, tailWord_3130700, baseEnd_3130700] using wordTrace_append hprefix tailTrace_3130700
  have hstable : (prefixWord ++ tailWord_3130700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130700).length < 2 ^ (prefixWord ++ tailWord_3130700).sum := by decide
  have hdescent : baseEnd_3130700 < baseStart_3130700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130730 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3130730 : Nat := 118140960795 + 3130730 * 2 ^ 59
def prefixEnd_3130730 : Nat := 4983230072969 + 3 ^ 40 * 3130730 * 2
def baseEnd_3130730 : Nat := 1607569289450641238177041

theorem tailTrace_3130730 : CollatzResearch.WordTrace tailWord_3130730 prefixEnd_3130730 1607569289450641238177041 := by
  unfold tailWord_3130730
  simp only [CollatzResearch.WordTrace]
  refine ⟨28546775986976842740143411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76124735965271580640382429 28546775986976842740143411)
  ·
    refine ⟨42820163980465264110215117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28546775986976842740143411 42820163980465264110215117)
    ·
      refine ⟨16057561492674474041330669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42820163980465264110215117 16057561492674474041330669)
      ·
        refine ⟨6021585559752927765499001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16057561492674474041330669 6021585559752927765499001)
        ·
          refine ⟨4516189169814695824124251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6021585559752927765499001 4516189169814695824124251)
          ·
            refine ⟨6774283754722043736186377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516189169814695824124251 6774283754722043736186377)
            ·
              refine ⟨5080712816041532802139783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6774283754722043736186377 5080712816041532802139783)
              ·
                refine ⟨7621069224062299203209675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5080712816041532802139783 7621069224062299203209675)
                ·
                  refine ⟨11431603836093448804814513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7621069224062299203209675 11431603836093448804814513)
                  ·
                    refine ⟨8573702877070086603610885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11431603836093448804814513 8573702877070086603610885)
                    ·
                      refine ⟨1607569289450641238177041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8573702877070086603610885 1607569289450641238177041)
                      ·
                        rfl

theorem cell23_3130730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3130730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130730 prefixEnd_3130730 := by exact prefixLift 3130730
  have htrace : WordTrace (prefixWord ++ tailWord_3130730) baseStart_3130730 baseEnd_3130730 := by
    simpa [prefixWord, tailWord_3130730, baseEnd_3130730] using wordTrace_append hprefix tailTrace_3130730
  have hstable : (prefixWord ++ tailWord_3130730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130730).length < 2 ^ (prefixWord ++ tailWord_3130730).sum := by decide
  have hdescent : baseEnd_3130730 < baseStart_3130730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130733 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3130733 : Nat := 118140960795 + 3130733 * 2 ^ 59
def prefixEnd_3130733 : Nat := 4983230072969 + 3 ^ 40 * 3130733 * 2
def baseEnd_3130733 : Nat := 1607570829892604726439527

theorem tailTrace_3130733 : CollatzResearch.WordTrace tailWord_3130733 prefixEnd_3130733 1607570829892604726439527 := by
  unfold tailWord_3130733
  simp only [CollatzResearch.WordTrace]
  refine ⟨114187213366896502472932853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76124808911264334981955235 114187213366896502472932853)
  ·
    refine ⟨10705051253146547106837455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114187213366896502472932853 10705051253146547106837455)
    ·
      refine ⟨16057576879719820660256183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10705051253146547106837455 16057576879719820660256183)
      ·
        refine ⟨24086365319579730990384275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16057576879719820660256183 24086365319579730990384275)
        ·
          refine ⟨36129547979369596485576413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24086365319579730990384275 36129547979369596485576413)
          ·
            refine ⟨13548580492263598682091155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36129547979369596485576413 13548580492263598682091155)
            ·
              refine ⟨20322870738395398023136733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13548580492263598682091155 20322870738395398023136733)
              ·
                refine ⟨7621076526898274258676275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20322870738395398023136733 7621076526898274258676275)
                ·
                  refine ⟨11431614790347411388014413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7621076526898274258676275 11431614790347411388014413)
                  ·
                    refine ⟨4286855546380279270505405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11431614790347411388014413 4286855546380279270505405)
                    ·
                      refine ⟨1607570829892604726439527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4286855546380279270505405 1607570829892604726439527)
                      ·
                        rfl

theorem cell23_3130733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3130733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130733 prefixEnd_3130733 := by exact prefixLift 3130733
  have htrace : WordTrace (prefixWord ++ tailWord_3130733) baseStart_3130733 baseEnd_3130733 := by
    simpa [prefixWord, tailWord_3130733, baseEnd_3130733] using wordTrace_append hprefix tailTrace_3130733
  have hstable : (prefixWord ++ tailWord_3130733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130733).length < 2 ^ (prefixWord ++ tailWord_3130733).sum := by decide
  have hdescent : baseEnd_3130733 < baseStart_3130733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130734 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_3130734 : Nat := 118140960795 + 3130734 * 2 ^ 59
def prefixEnd_3130734 : Nat := 4983230072969 + 3 ^ 40 * 3130734 * 2
def baseEnd_3130734 : Nat := 1607571343373259222527023

theorem tailTrace_3130734 : CollatzResearch.WordTrace tailWord_3130734 prefixEnd_3130734 1607571343373259222527023 := by
  unfold tailWord_3130734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14273406229986609955464907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76124833226595253095812837 14273406229986609955464907)
  ·
    refine ⟨21410109344979914933197361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14273406229986609955464907 21410109344979914933197361)
    ·
      refine ⟨16057582008734936199898021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21410109344979914933197361 16057582008734936199898021)
      ·
        refine ⟨3010796626637800537480879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16057582008734936199898021 3010796626637800537480879)
        ·
          refine ⟨4516194939956700806221319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010796626637800537480879 4516194939956700806221319)
          ·
            refine ⟨6774292409935051209331979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516194939956700806221319 6774292409935051209331979)
            ·
              refine ⟨10161438614902576813997969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6774292409935051209331979 10161438614902576813997969)
              ·
                refine ⟨7621078961176932610498477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10161438614902576813997969 7621078961176932610498477)
                ·
                  refine ⟨2857904610441349728936929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7621078961176932610498477 2857904610441349728936929)
                  ·
                    refine ⟨2143428457831012296702697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2857904610441349728936929 2143428457831012296702697)
                    ·
                      refine ⟨1607571343373259222527023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2143428457831012296702697 1607571343373259222527023)
                      ·
                        rfl

theorem cell23_3130734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_3130734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130734 prefixEnd_3130734 := by exact prefixLift 3130734
  have htrace : WordTrace (prefixWord ++ tailWord_3130734) baseStart_3130734 baseEnd_3130734 := by
    simpa [prefixWord, tailWord_3130734, baseEnd_3130734] using wordTrace_append hprefix tailTrace_3130734
  have hstable : (prefixWord ++ tailWord_3130734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130734).length < 2 ^ (prefixWord ++ tailWord_3130734).sum := by decide
  have hdescent : baseEnd_3130734 < baseStart_3130734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130739 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 10]
def baseStart_3130739 : Nat := 118140960795 + 3130739 * 2 ^ 59
def prefixEnd_3130739 : Nat := 4983230072969 + 3 ^ 40 * 3130739 * 2
def baseEnd_3130739 : Nat := 1607573910776531702964499

theorem tailTrace_3130739 : CollatzResearch.WordTrace tailWord_3130739 prefixEnd_3130739 1607573910776531702964499 := by
  unfold tailWord_3130739
  simp only [CollatzResearch.WordTrace]
  refine ⟨114187432204874765497651271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76124954803249843665100847 114187432204874765497651271)
  ·
    refine ⟨171281148307312148246476907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114187432204874765497651271 171281148307312148246476907)
    ·
      refine ⟨256921722460968222369715361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171281148307312148246476907 256921722460968222369715361)
      ·
        refine ⟨192691291845726166777286521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256921722460968222369715361 192691291845726166777286521)
        ·
          refine ⟨144518468884294625082964891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192691291845726166777286521 144518468884294625082964891)
          ·
            refine ⟨216777703326441937624447337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144518468884294625082964891 216777703326441937624447337)
            ·
              refine ⟨162583277494831453218335503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216777703326441937624447337 162583277494831453218335503)
              ·
                refine ⟨243874916242247179827503255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162583277494831453218335503 243874916242247179827503255)
                ·
                  refine ⟨365812374363370769741254883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243874916242247179827503255 365812374363370769741254883)
                  ·
                    refine ⟨548718561545056154611882325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 365812374363370769741254883 548718561545056154611882325)
                    ·
                      refine ⟨1607573910776531702964499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 548718561545056154611882325 1607573910776531702964499)
                      ·
                        rfl

theorem cell23_3130739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_3130739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130739 prefixEnd_3130739 := by exact prefixLift 3130739
  have htrace : WordTrace (prefixWord ++ tailWord_3130739) baseStart_3130739 baseEnd_3130739 := by
    simpa [prefixWord, tailWord_3130739, baseEnd_3130739] using wordTrace_append hprefix tailTrace_3130739
  have hstable : (prefixWord ++ tailWord_3130739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130739).length < 2 ^ (prefixWord ++ tailWord_3130739).sum := by decide
  have hdescent : baseEnd_3130739 < baseStart_3130739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130743 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 3, 3, 2]
def baseStart_3130743 : Nat := 118140960795 + 3130743 * 2 ^ 59
def prefixEnd_3130743 : Nat := 4983230072969 + 3 ^ 40 * 3130743 * 2
def baseEnd_3130743 : Nat := 1607575964699149687314481

theorem tailTrace_3130743 : CollatzResearch.WordTrace tailWord_3130743 prefixEnd_3130743 1607575964699149687314481 := by
  unfold tailWord_3130743
  simp only [CollatzResearch.WordTrace]
  refine ⟨114187578096860274180796883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76125052064573516120531255 114187578096860274180796883)
  ·
    refine ⟨171281367145290411271195325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114187578096860274180796883 171281367145290411271195325)
    ·
      refine ⟨64230512679483904226698247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171281367145290411271195325 64230512679483904226698247)
      ·
        refine ⟨96345769019225856340047371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64230512679483904226698247 96345769019225856340047371)
        ·
          refine ⟨144518653528838784510071057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96345769019225856340047371 144518653528838784510071057)
          ·
            refine ⟨108388990146629088382553293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144518653528838784510071057 108388990146629088382553293)
            ·
              refine ⟨40645871304985908143457485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108388990146629088382553293 40645871304985908143457485)
              ·
                refine ⟨15242201739369715553796557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40645871304985908143457485 15242201739369715553796557)
                ·
                  refine ⟨5715825652263643332673709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15242201739369715553796557 5715825652263643332673709)
                  ·
                    refine ⟨2143434619598866249752641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5715825652263643332673709 2143434619598866249752641)
                    ·
                      refine ⟨1607575964699149687314481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2143434619598866249752641 1607575964699149687314481)
                      ·
                        rfl

theorem cell23_3130743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 3, 2].length) (baseStart_3130743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130743 prefixEnd_3130743 := by exact prefixLift 3130743
  have htrace : WordTrace (prefixWord ++ tailWord_3130743) baseStart_3130743 baseEnd_3130743 := by
    simpa [prefixWord, tailWord_3130743, baseEnd_3130743] using wordTrace_append hprefix tailTrace_3130743
  have hstable : (prefixWord ++ tailWord_3130743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130743).length < 2 ^ (prefixWord ++ tailWord_3130743).sum := by decide
  have hdescent : baseEnd_3130743 < baseStart_3130743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130754 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_3130754 : Nat := 118140960795 + 3130754 * 2 ^ 59
def prefixEnd_3130754 : Nat := 4983230072969 + 3 ^ 40 * 3130754 * 2
def baseEnd_3130754 : Nat := 1607581612986349144276931

theorem tailTrace_3130754 : CollatzResearch.WordTrace tailWord_3130754 prefixEnd_3130754 1607581612986349144276931 := by
  unfold tailWord_3130754
  simp only [CollatzResearch.WordTrace]
  refine ⟨28546994824955105764861829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76125319533213615372964877 28546994824955105764861829)
  ·
    refine ⟨5352561529679082330911593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28546994824955105764861829 5352561529679082330911593)
    ·
      refine ⟨4014421147259311748183695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5352561529679082330911593 4014421147259311748183695)
      ·
        refine ⟨6021631720888967622275543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4014421147259311748183695 6021631720888967622275543)
        ·
          refine ⟨9032447581333451433413315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6021631720888967622275543 9032447581333451433413315)
          ·
            refine ⟨13548671372000177150119973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9032447581333451433413315 13548671372000177150119973)
            ·
              refine ⟨2540375882250033215647495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13548671372000177150119973 2540375882250033215647495)
              ·
                refine ⟨3810563823375049823471243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540375882250033215647495 3810563823375049823471243)
                ·
                  refine ⟨5715845735062574735206865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810563823375049823471243 5715845735062574735206865)
                  ·
                    refine ⟨4286884301296931051405149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5715845735062574735206865 4286884301296931051405149)
                    ·
                      refine ⟨1607581612986349144276931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4286884301296931051405149 1607581612986349144276931)
                      ·
                        rfl

theorem cell23_3130754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_3130754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130754 prefixEnd_3130754 := by exact prefixLift 3130754
  have htrace : WordTrace (prefixWord ++ tailWord_3130754) baseStart_3130754 baseEnd_3130754 := by
    simpa [prefixWord, tailWord_3130754, baseEnd_3130754] using wordTrace_append hprefix tailTrace_3130754
  have hstable : (prefixWord ++ tailWord_3130754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130754).length < 2 ^ (prefixWord ++ tailWord_3130754).sum := by decide
  have hdescent : baseEnd_3130754 < baseStart_3130754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130773 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 3, 4, 2]
def baseStart_3130773 : Nat := 118140960795 + 3130773 * 2 ^ 59
def prefixEnd_3130773 : Nat := 4983230072969 + 3 ^ 40 * 3130773 * 2
def baseEnd_3130773 : Nat := 1607591369118784569939343

theorem tailTrace_3130773 : CollatzResearch.WordTrace tailWord_3130773 prefixEnd_3130773 1607591369118784569939343 := by
  unfold tailWord_3130773
  simp only [CollatzResearch.WordTrace]
  refine ⟨114188672286751589304388973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76125781524501059536259315 114188672286751589304388973)
  ·
    refine ⟨42820752107531845989145865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114188672286751589304388973 42820752107531845989145865)
    ·
      refine ⟨32115564080648884491859399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42820752107531845989145865 32115564080648884491859399)
      ·
        refine ⟨48173346120973326737789099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32115564080648884491859399 48173346120973326737789099)
        ·
          refine ⟨72260019181459990106683649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48173346120973326737789099 72260019181459990106683649)
          ·
            refine ⟨54195014386094992580012737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72260019181459990106683649 54195014386094992580012737)
            ·
              refine ⟨40646260789571244435009553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54195014386094992580012737 40646260789571244435009553)
              ·
                refine ⟨30484695592178433326257165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40646260789571244435009553 30484695592178433326257165)
                ·
                  refine ⟨11431760847066912497346437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30484695592178433326257165 11431760847066912497346437)
                  ·
                    refine ⟨2143455158825046093252457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11431760847066912497346437 2143455158825046093252457)
                    ·
                      refine ⟨1607591369118784569939343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2143455158825046093252457 1607591369118784569939343)
                      ·
                        rfl

theorem cell23_3130773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_3130773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130773 prefixEnd_3130773 := by exact prefixLift 3130773
  have htrace : WordTrace (prefixWord ++ tailWord_3130773) baseStart_3130773 baseEnd_3130773 := by
    simpa [prefixWord, tailWord_3130773, baseEnd_3130773] using wordTrace_append hprefix tailTrace_3130773
  have hstable : (prefixWord ++ tailWord_3130773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130773).length < 2 ^ (prefixWord ++ tailWord_3130773).sum := by decide
  have hdescent : baseEnd_3130773 < baseStart_3130773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130796 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 7]
def baseStart_3130796 : Nat := 118140960795 + 3130796 * 2 ^ 59
def prefixEnd_3130796 : Nat := 4983230072969 + 3 ^ 40 * 3130796 * 2
def baseEnd_3130796 : Nat := 178622575463759775550193

theorem tailTrace_3130796 : CollatzResearch.WordTrace tailWord_3130796 prefixEnd_3130796 178622575463759775550193 := by
  unfold tailWord_3130796
  simp only [CollatzResearch.WordTrace]
  refine ⟨57094755582834132116238121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76126340777112176154984161 57094755582834132116238121)
  ·
    refine ⟨42821066687125599087178591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57094755582834132116238121 42821066687125599087178591)
    ·
      refine ⟨64231600030688398630767887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42821066687125599087178591 64231600030688398630767887)
      ·
        refine ⟨96347400046032597946151831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64231600030688398630767887 96347400046032597946151831)
        ·
          refine ⟨144521100069048896919227747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96347400046032597946151831 144521100069048896919227747)
          ·
            refine ⟨216781650103573345378841621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144521100069048896919227747 216781650103573345378841621)
            ·
              refine ⟨10161639848605000564633201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 216781650103573345378841621 10161639848605000564633201)
              ·
                refine ⟨7621229886453750423474901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10161639848605000564633201 7621229886453750423474901)
                ·
                  refine ⟨178622575463759775550193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7621229886453750423474901 178622575463759775550193)
                  ·
                    rfl

theorem cell23_3130796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_3130796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130796 prefixEnd_3130796 := by exact prefixLift 3130796
  have htrace : WordTrace (prefixWord ++ tailWord_3130796) baseStart_3130796 baseEnd_3130796 := by
    simpa [prefixWord, tailWord_3130796, baseEnd_3130796] using wordTrace_append hprefix tailTrace_3130796
  have hstable : (prefixWord ++ tailWord_3130796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130796).length < 2 ^ (prefixWord ++ tailWord_3130796).sum := by decide
  have hdescent : baseEnd_3130796 < baseStart_3130796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130863 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 4]
def baseStart_3130863 : Nat := 118140960795 + 3130863 * 2 ^ 59
def prefixEnd_3130863 : Nat := 4983230072969 + 3 ^ 40 * 3130863 * 2
def baseEnd_3130863 : Nat := 1607637582377689217813929

theorem tailTrace_3130863 : CollatzResearch.WordTrace tailWord_3130863 prefixEnd_3130863 1607637582377689217813929 := by
  unfold tailWord_3130863
  simp only [CollatzResearch.WordTrace]
  refine ⟨114191954856425534675165243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76127969904283689783443495 114191954856425534675165243)
  ·
    refine ⟨171287932284638302012747865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114191954856425534675165243 171287932284638302012747865)
    ·
      refine ⟨128465949213478726509560899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171287932284638302012747865 128465949213478726509560899)
      ·
        refine ⟨192698923820218089764341349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128465949213478726509560899 192698923820218089764341349)
        ·
          refine ⟨36131048216290891830814003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192698923820218089764341349 36131048216290891830814003)
          ·
            refine ⟨54196572324436337746221005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36131048216290891830814003 54196572324436337746221005)
            ·
              refine ⟨20323714621663626654832877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54196572324436337746221005 20323714621663626654832877)
              ·
                refine ⟨7621392983123859995562329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20323714621663626654832877 7621392983123859995562329)
                ·
                  refine ⟨5716044737342894996671747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7621392983123859995562329 5716044737342894996671747)
                  ·
                    refine ⟨8574067106014342495007621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5716044737342894996671747 8574067106014342495007621)
                    ·
                      refine ⟨1607637582377689217813929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8574067106014342495007621 1607637582377689217813929)
                      ·
                        rfl

theorem cell23_3130863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_3130863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130863 prefixEnd_3130863 := by exact prefixLift 3130863
  have htrace : WordTrace (prefixWord ++ tailWord_3130863) baseStart_3130863 baseEnd_3130863 := by
    simpa [prefixWord, tailWord_3130863, baseEnd_3130863] using wordTrace_append hprefix tailTrace_3130863
  have hstable : (prefixWord ++ tailWord_3130863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130863).length < 2 ^ (prefixWord ++ tailWord_3130863).sum := by decide
  have hdescent : baseEnd_3130863 < baseStart_3130863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130883 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 3]
def baseStart_3130883 : Nat := 118140960795 + 3130883 * 2 ^ 59
def prefixEnd_3130883 : Nat := 4983230072969 + 3 ^ 40 * 3130883 * 2
def baseEnd_3130883 : Nat := 1607647851990779139563837

theorem tailTrace_3130883 : CollatzResearch.WordTrace tailWord_3130883 prefixEnd_3130883 1607647851990779139563837 := by
  unfold tailWord_3130883
  simp only [CollatzResearch.WordTrace]
  refine ⟨114192684316353078090893303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76128456210902052060595535 114192684316353078090893303)
  ·
    refine ⟨171289026474529617136339955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114192684316353078090893303 171289026474529617136339955)
    ·
      refine ⟨256933539711794425704509933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171289026474529617136339955 256933539711794425704509933)
      ·
        refine ⟨96350077391922909639191225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256933539711794425704509933 96350077391922909639191225)
        ·
          refine ⟨72262558043942182229393419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96350077391922909639191225 72262558043942182229393419)
          ·
            refine ⟨108393837065913273344090129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72262558043942182229393419 108393837065913273344090129)
            ·
              refine ⟨81295377799434955008067597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108393837065913273344090129 81295377799434955008067597)
              ·
                refine ⟨30485766674788108128025349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81295377799434955008067597 30485766674788108128025349)
                ·
                  refine ⟨5716081251522770274004753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30485766674788108128025349 5716081251522770274004753)
                  ·
                    refine ⟨4287060938642077705503565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5716081251522770274004753 4287060938642077705503565)
                    ·
                      refine ⟨1607647851990779139563837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4287060938642077705503565 1607647851990779139563837)
                      ·
                        rfl

theorem cell23_3130883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_3130883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130883 prefixEnd_3130883 := by exact prefixLift 3130883
  have htrace : WordTrace (prefixWord ++ tailWord_3130883) baseStart_3130883 baseEnd_3130883 := by
    simpa [prefixWord, tailWord_3130883, baseEnd_3130883] using wordTrace_append hprefix tailTrace_3130883
  have hstable : (prefixWord ++ tailWord_3130883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130883).length < 2 ^ (prefixWord ++ tailWord_3130883).sum := by decide
  have hdescent : baseEnd_3130883 < baseStart_3130883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130930 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_3130930 : Nat := 118140960795 + 3130930 * 2 ^ 59
def prefixEnd_3130930 : Nat := 4983230072969 + 3 ^ 40 * 3130930 * 2
def baseEnd_3130930 : Nat := 1607671985581540455676121

theorem tailTrace_3130930 : CollatzResearch.WordTrace tailWord_3130930 prefixEnd_3130930 1607671985581540455676121 := by
  unfold tailWord_3130930
  simp only [CollatzResearch.WordTrace]
  refine ⟨28548599636795701279463561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76129599031455203411902829 28548599636795701279463561)
  ·
    refine ⟨21411449727596775959597671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28548599636795701279463561 21411449727596775959597671)
    ·
      refine ⟨32117174591395163939396507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21411449727596775959597671 32117174591395163939396507)
      ·
        refine ⟨48175761887092745909094761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32117174591395163939396507 48175761887092745909094761)
        ·
          refine ⟨36131821415319559431821071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48175761887092745909094761 36131821415319559431821071)
          ·
            refine ⟨54197732122979339147731607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36131821415319559431821071 54197732122979339147731607)
            ·
              refine ⟨81296598184469008721597411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54197732122979339147731607 81296598184469008721597411)
              ·
                refine ⟨121944897276703513082396117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81296598184469008721597411 121944897276703513082396117)
                ·
                  refine ⟨2858083529922738587868659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 121944897276703513082396117 2858083529922738587868659)
                  ·
                    refine ⟨4287125294884107881802989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2858083529922738587868659 4287125294884107881802989)
                    ·
                      refine ⟨1607671985581540455676121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4287125294884107881802989 1607671985581540455676121)
                      ·
                        rfl

theorem cell23_3130930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_3130930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130930 prefixEnd_3130930 := by exact prefixLift 3130930
  have htrace : WordTrace (prefixWord ++ tailWord_3130930) baseStart_3130930 baseEnd_3130930 := by
    simpa [prefixWord, tailWord_3130930, baseEnd_3130930] using wordTrace_append hprefix tailTrace_3130930
  have hstable : (prefixWord ++ tailWord_3130930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130930).length < 2 ^ (prefixWord ++ tailWord_3130930).sum := by decide
  have hdescent : baseEnd_3130930 < baseStart_3130930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130953 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 4]
def baseStart_3130953 : Nat := 118140960795 + 3130953 * 2 ^ 59
def prefixEnd_3130953 : Nat := 4983230072969 + 3 ^ 40 * 3130953 * 2
def baseEnd_3130953 : Nat := 1607683795636593865688515

theorem tailTrace_3130953 : CollatzResearch.WordTrace tailWord_3130953 prefixEnd_3130953 1607683795636593865688515 := by
  unfold tailWord_3130953
  simp only [CollatzResearch.WordTrace]
  refine ⟨114195237426099480045941513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76130158284066320030627675 114195237426099480045941513)
  ·
    refine ⟨85646428069574610034456135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114195237426099480045941513 85646428069574610034456135)
    ·
      refine ⟨128469642104361915051684203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85646428069574610034456135 128469642104361915051684203)
      ·
        refine ⟨192704463156542872577526305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128469642104361915051684203 192704463156542872577526305)
        ·
          refine ⟨144528347367407154433144729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192704463156542872577526305 144528347367407154433144729)
          ·
            refine ⟨108396260525555365824858547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144528347367407154433144729 108396260525555365824858547)
            ·
              refine ⟨162594390788333048737287821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108396260525555365824858547 162594390788333048737287821)
              ·
                refine ⟨60972896545624893276482933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162594390788333048737287821 60972896545624893276482933)
                ·
                  refine ⟨5716209051152333744670275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60972896545624893276482933 5716209051152333744670275)
                  ·
                    refine ⟨8574313576728500617005413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5716209051152333744670275 8574313576728500617005413)
                    ·
                      refine ⟨1607683795636593865688515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8574313576728500617005413 1607683795636593865688515)
                      ·
                        rfl

theorem cell23_3130953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_3130953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130953 prefixEnd_3130953 := by exact prefixLift 3130953
  have htrace : WordTrace (prefixWord ++ tailWord_3130953) baseStart_3130953 baseEnd_3130953 := by
    simpa [prefixWord, tailWord_3130953, baseEnd_3130953] using wordTrace_append hprefix tailTrace_3130953
  have hstable : (prefixWord ++ tailWord_3130953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130953).length < 2 ^ (prefixWord ++ tailWord_3130953).sum := by decide
  have hdescent : baseEnd_3130953 < baseStart_3130953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130980 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_3130980 : Nat := 118140960795 + 3130980 * 2 ^ 59
def prefixEnd_3130980 : Nat := 4983230072969 + 3 ^ 40 * 3130980 * 2
def baseEnd_3130980 : Nat := 535899219871421753350297

theorem tailTrace_3130980 : CollatzResearch.WordTrace tailWord_3130980 prefixEnd_3130980 535899219871421753350297 := by
  unfold tailWord_3130980
  simp only [CollatzResearch.WordTrace]
  refine ⟨57098111098500831828587197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76130814798001109104782929 57098111098500831828587197)
  ·
    refine ⟨21411791661937811935720199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57098111098500831828587197 21411791661937811935720199)
    ·
      refine ⟨32117687492906717903580299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21411791661937811935720199 32117687492906717903580299)
      ·
        refine ⟨48176531239360076855370449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32117687492906717903580299 48176531239360076855370449)
        ·
          refine ⟨36132398429520057641527837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48176531239360076855370449 36132398429520057641527837)
          ·
            refine ⟨13549649411070021615572939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36132398429520057641527837 13549649411070021615572939)
            ·
              refine ⟨20324474116605032423359409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13549649411070021615572939 20324474116605032423359409)
              ·
                refine ⟨15243355587453774317519557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20324474116605032423359409 15243355587453774317519557)
                ·
                  refine ⟨2858129172647582684534917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15243355587453774317519557 2858129172647582684534917)
                  ·
                    refine ⟨535899219871421753350297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2858129172647582684534917 535899219871421753350297)
                    ·
                      rfl

theorem cell23_3130980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_3130980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130980 prefixEnd_3130980 := by exact prefixLift 3130980
  have htrace : WordTrace (prefixWord ++ tailWord_3130980) baseStart_3130980 baseEnd_3130980 := by
    simpa [prefixWord, tailWord_3130980, baseEnd_3130980] using wordTrace_append hprefix tailTrace_3130980
  have hstable : (prefixWord ++ tailWord_3130980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130980).length < 2 ^ (prefixWord ++ tailWord_3130980).sum := by decide
  have hdescent : baseEnd_3130980 < baseStart_3130980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130981 : List Nat := [1, 3, 1, 3, 3, 3, 1, 3, 1, 1, 3]
def baseStart_3130981 : Nat := 118140960795 + 3130981 * 2 ^ 59
def prefixEnd_3130981 : Nat := 4983230072969 + 3 ^ 40 * 3130981 * 2
def baseEnd_3130981 : Nat := 1607698173094919756138387

theorem tailTrace_3130981 : CollatzResearch.WordTrace tailWord_3130981 prefixEnd_3130981 1607698173094919756138387 := by
  unfold tailWord_3130981
  simp only [CollatzResearch.WordTrace]
  refine ⟨114196258669998040827960797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76130839113332027218640531 114196258669998040827960797)
  ·
    refine ⟨42823597001249265310485299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114196258669998040827960797 42823597001249265310485299)
    ·
      refine ⟨64235395501873897965727949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42823597001249265310485299 64235395501873897965727949)
      ·
        refine ⟨24088273313202711737147981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64235395501873897965727949 24088273313202711737147981)
        ·
          refine ⟨9033102492451016901430493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24088273313202711737147981 9033102492451016901430493)
          ·
            refine ⟨3387413434669131338036435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9033102492451016901430493 3387413434669131338036435)
            ·
              refine ⟨5081120152003697007054653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3387413434669131338036435 5081120152003697007054653)
              ·
                refine ⟨1905420057001386377645495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5081120152003697007054653 1905420057001386377645495)
                ·
                  refine ⟨2858130085502079566468243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905420057001386377645495 2858130085502079566468243)
                  ·
                    refine ⟨4287195128253119349702365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2858130085502079566468243 4287195128253119349702365)
                    ·
                      refine ⟨1607698173094919756138387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4287195128253119349702365 1607698173094919756138387)
                      ·
                        rfl

theorem cell23_3130981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_3130981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130981 prefixEnd_3130981 := by exact prefixLift 3130981
  have htrace : WordTrace (prefixWord ++ tailWord_3130981) baseStart_3130981 baseEnd_3130981 := by
    simpa [prefixWord, tailWord_3130981, baseEnd_3130981] using wordTrace_append hprefix tailTrace_3130981
  have hstable : (prefixWord ++ tailWord_3130981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130981).length < 2 ^ (prefixWord ++ tailWord_3130981).sum := by decide
  have hdescent : baseEnd_3130981 < baseStart_3130981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130997 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 4, 4]
def baseStart_3130997 : Nat := 118140960795 + 3130997 * 2 ^ 59
def prefixEnd_3130997 : Nat := 4983230072969 + 3 ^ 40 * 3130997 * 2
def baseEnd_3130997 : Nat := 535902129595130564512771

theorem tailTrace_3130997 : CollatzResearch.WordTrace tailWord_3130997 prefixEnd_3130997 535902129595130564512771 := by
  unfold tailWord_3130997
  simp only [CollatzResearch.WordTrace]
  refine ⟨114196842237940075560543245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76131228158626717040362163 114196842237940075560543245)
  ·
    refine ⟨42823815839227528335203717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114196842237940075560543245 42823815839227528335203717)
    ·
      refine ⟨8029465469855161562850697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42823815839227528335203717 8029465469855161562850697)
      ·
        refine ⟨6022099102391371172138023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8029465469855161562850697 6022099102391371172138023)
        ·
          refine ⟨9033148653587056758207035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6022099102391371172138023 9033148653587056758207035)
          ·
            refine ⟨13549722980380585137310553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9033148653587056758207035 13549722980380585137310553)
            ·
              refine ⟨10162292235285438852982915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13549722980380585137310553 10162292235285438852982915)
              ·
                refine ⟨15243438352928158279474373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10162292235285438852982915 15243438352928158279474373)
                ·
                  refine ⟨2858144691174029677401445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15243438352928158279474373 2858144691174029677401445)
                  ·
                    refine ⟨535902129595130564512771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2858144691174029677401445 535902129595130564512771)
                    ·
                      rfl

theorem cell23_3130997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_3130997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130997 prefixEnd_3130997 := by exact prefixLift 3130997
  have htrace : WordTrace (prefixWord ++ tailWord_3130997) baseStart_3130997 baseEnd_3130997 := by
    simpa [prefixWord, tailWord_3130997, baseEnd_3130997] using wordTrace_append hprefix tailTrace_3130997
  have hstable : (prefixWord ++ tailWord_3130997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130997).length < 2 ^ (prefixWord ++ tailWord_3130997).sum := by decide
  have hdescent : baseEnd_3130997 < baseStart_3130997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130998 : List Nat := [5, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_3130998 : Nat := 118140960795 + 3130998 * 2 ^ 59
def prefixEnd_3130998 : Nat := 4983230072969 + 3 ^ 40 * 3130998 * 2
def baseEnd_3130998 : Nat := 1607706902266046189625809

theorem tailTrace_3130998 : CollatzResearch.WordTrace tailWord_3130998 prefixEnd_3130998 1607706902266046189625809 := by
  unfold tailWord_3130998
  simp only [CollatzResearch.WordTrace]
  refine ⟨7137304919433528295708103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76131252473957635154219765 7137304919433528295708103)
  ·
    refine ⟨10705957379150292443562155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7137304919433528295708103 10705957379150292443562155)
    ·
      refine ⟨16058936068725438665343233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10705957379150292443562155 16058936068725438665343233)
      ·
        refine ⟨12044202051544078999007425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16058936068725438665343233 12044202051544078999007425)
        ·
          refine ⟨9033151538658059249255569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12044202051544078999007425 9033151538658059249255569)
          ·
            refine ⟨6774863653993544436941677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9033151538658059249255569 6774863653993544436941677)
            ·
              refine ⟨2540573870247579163853129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6774863653993544436941677 2540573870247579163853129)
              ·
                refine ⟨1905430402685684372889847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540573870247579163853129 1905430402685684372889847)
                ·
                  refine ⟨2858145604028526559334771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905430402685684372889847 2858145604028526559334771)
                  ·
                    refine ⟨4287218406042789839002157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2858145604028526559334771 4287218406042789839002157)
                    ·
                      refine ⟨1607706902266046189625809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4287218406042789839002157 1607706902266046189625809)
                      ·
                        rfl

theorem cell23_3130998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_3130998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3130998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3130998 prefixEnd_3130998 := by exact prefixLift 3130998
  have htrace : WordTrace (prefixWord ++ tailWord_3130998) baseStart_3130998 baseEnd_3130998 := by
    simpa [prefixWord, tailWord_3130998, baseEnd_3130998] using wordTrace_append hprefix tailTrace_3130998
  have hstable : (prefixWord ++ tailWord_3130998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130998).length < 2 ^ (prefixWord ++ tailWord_3130998).sum := by decide
  have hdescent : baseEnd_3130998 < baseStart_3130998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131013 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_3131013 : Nat := 118140960795 + 3131013 * 2 ^ 59
def prefixEnd_3131013 : Nat := 4983230072969 + 3 ^ 40 * 3131013 * 2
def baseEnd_3131013 : Nat := 1607714604475863630938239

theorem tailTrace_3131013 : CollatzResearch.WordTrace tailWord_3131013 prefixEnd_3131013 1607714604475863630938239 := by
  unfold tailWord_3131013
  simp only [CollatzResearch.WordTrace]
  refine ⟨114197425805882110293125693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76131617203921406862083795 114197425805882110293125693)
  ·
    refine ⟨42824034677205791359922135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114197425805882110293125693 42824034677205791359922135)
    ·
      refine ⟨64236052015808687039883203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42824034677205791359922135 64236052015808687039883203)
      ·
        refine ⟨96354078023713030559824805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64236052015808687039883203 96354078023713030559824805)
        ·
          refine ⟨18066389629446193229967151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96354078023713030559824805 18066389629446193229967151)
          ·
            refine ⟨27099584444169289844950727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18066389629446193229967151 27099584444169289844950727)
            ·
              refine ⟨40649376666253934767426091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27099584444169289844950727 40649376666253934767426091)
              ·
                refine ⟨60974064999380902151139137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40649376666253934767426091 60974064999380902151139137)
                ·
                  refine ⟨45730548749535676613354353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60974064999380902151139137 45730548749535676613354353)
                  ·
                    refine ⟨34297911562151757460015765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45730548749535676613354353 34297911562151757460015765)
                    ·
                      refine ⟨1607714604475863630938239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34297911562151757460015765 1607714604475863630938239)
                      ·
                        rfl

theorem cell23_3131013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_3131013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131013 prefixEnd_3131013 := by exact prefixLift 3131013
  have htrace : WordTrace (prefixWord ++ tailWord_3131013) baseStart_3131013 baseEnd_3131013 := by
    simpa [prefixWord, tailWord_3131013, baseEnd_3131013] using wordTrace_append hprefix tailTrace_3131013
  have hstable : (prefixWord ++ tailWord_3131013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131013).length < 2 ^ (prefixWord ++ tailWord_3131013).sum := by decide
  have hdescent : baseEnd_3131013 < baseStart_3131013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131020 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 1, 3, 3]
def baseStart_3131020 : Nat := 118140960795 + 3131020 * 2 ^ 59
def prefixEnd_3131020 : Nat := 4983230072969 + 3 ^ 40 * 3131020 * 2
def baseEnd_3131020 : Nat := 1607718198840445103550707

theorem tailTrace_3131020 : CollatzResearch.WordTrace tailWord_3131020 prefixEnd_3131020 1607718198840445103550707 := by
  unfold tailWord_3131020
  simp only [CollatzResearch.WordTrace]
  refine ⟨57098840558428375244315257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76131787411237833659087009 57098840558428375244315257)
  ·
    refine ⟨42824130418821281433236443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57098840558428375244315257 42824130418821281433236443)
    ·
      refine ⟨64236195628231922149854665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42824130418821281433236443 64236195628231922149854665)
      ·
        refine ⟨48177146721173941612390999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64236195628231922149854665 48177146721173941612390999)
        ·
          refine ⟨72265720081760912418586499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48177146721173941612390999 72265720081760912418586499)
          ·
            refine ⟨108398580122641368627879749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72265720081760912418586499 108398580122641368627879749)
            ·
              refine ⟨20324733772995256617727453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108398580122641368627879749 20324733772995256617727453)
              ·
                refine ⟨7621775164873221231647795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20324733772995256617727453 7621775164873221231647795)
                ·
                  refine ⟨11432662747309831847471693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7621775164873221231647795 11432662747309831847471693)
                  ·
                    refine ⟨4287248530241186942801885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11432662747309831847471693 4287248530241186942801885)
                    ·
                      refine ⟨1607718198840445103550707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4287248530241186942801885 1607718198840445103550707)
                      ·
                        rfl

theorem cell23_3131020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_3131020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131020 prefixEnd_3131020 := by exact prefixLift 3131020
  have htrace : WordTrace (prefixWord ++ tailWord_3131020) baseStart_3131020 baseEnd_3131020 := by
    simpa [prefixWord, tailWord_3131020, baseEnd_3131020] using wordTrace_append hprefix tailTrace_3131020
  have hstable : (prefixWord ++ tailWord_3131020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131020).length < 2 ^ (prefixWord ++ tailWord_3131020).sum := by decide
  have hdescent : baseEnd_3131020 < baseStart_3131020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131033 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_3131033 : Nat := 118140960795 + 3131033 * 2 ^ 59
def prefixEnd_3131033 : Nat := 4983230072969 + 3 ^ 40 * 3131033 * 2
def baseEnd_3131033 : Nat := 1607724874088953552688147

theorem tailTrace_3131033 : CollatzResearch.WordTrace tailWord_3131033 prefixEnd_3131033 1607724874088953552688147 := by
  unfold tailWord_3131033
  simp only [CollatzResearch.WordTrace]
  refine ⟨114198155265809653708853753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76132103510539769139235835 114198155265809653708853753)
  ·
    refine ⟨85648616449357240281640315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114198155265809653708853753 85648616449357240281640315)
    ·
      refine ⟨128472924674035860422460473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85648616449357240281640315 128472924674035860422460473)
      ·
        refine ⟨96354693505526895316845355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128472924674035860422460473 96354693505526895316845355)
        ·
          refine ⟨144532040258290342975268033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96354693505526895316845355 144532040258290342975268033)
          ·
            refine ⟨108399030193717757231451025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144532040258290342975268033 108399030193717757231451025)
            ·
              refine ⟨81299272645288317923588269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108399030193717757231451025 81299272645288317923588269)
              ·
                refine ⟨30487227241983119221345601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81299272645288317923588269 30487227241983119221345601)
                ·
                  refine ⟨22865420431487339416009201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30487227241983119221345601 22865420431487339416009201)
                  ·
                    refine ⟨17149065323615504562006901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22865420431487339416009201 17149065323615504562006901)
                    ·
                      refine ⟨1607724874088953552688147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17149065323615504562006901 1607724874088953552688147)
                      ·
                        rfl

theorem cell23_3131033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_3131033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131033 prefixEnd_3131033 := by exact prefixLift 3131033
  have htrace : WordTrace (prefixWord ++ tailWord_3131033) baseStart_3131033 baseEnd_3131033 := by
    simpa [prefixWord, tailWord_3131033, baseEnd_3131033] using wordTrace_append hprefix tailTrace_3131033
  have hstable : (prefixWord ++ tailWord_3131033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131033).length < 2 ^ (prefixWord ++ tailWord_3131033).sum := by decide
  have hdescent : baseEnd_3131033 < baseStart_3131033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131048 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3131048 : Nat := 118140960795 + 3131048 * 2 ^ 59
def prefixEnd_3131048 : Nat := 4983230072969 + 3 ^ 40 * 3131048 * 2
def baseEnd_3131048 : Nat := 535910858766256998000193

theorem tailTrace_3131048 : CollatzResearch.WordTrace tailWord_3131048 prefixEnd_3131048 535910858766256998000193 := by
  unfold tailWord_3131048
  simp only [CollatzResearch.WordTrace]
  refine ⟨57099351180377655635324899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76132468240503540847099865 57099351180377655635324899)
  ·
    refine ⟨85649026770566483452987349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57099351180377655635324899 85649026770566483452987349)
    ·
      refine ⟨2007399064935151955929391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 85649026770566483452987349 2007399064935151955929391)
      ·
        refine ⟨3011098597402727933894087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2007399064935151955929391 3011098597402727933894087)
        ·
          refine ⟨4516647896104091900841131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011098597402727933894087 4516647896104091900841131)
          ·
            refine ⟨6774971844156137851261697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516647896104091900841131 6774971844156137851261697)
            ·
              refine ⟨5081228883117103388446273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6774971844156137851261697 5081228883117103388446273)
              ·
                refine ⟨3810921662337827541334705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5081228883117103388446273 3810921662337827541334705)
                ·
                  refine ⟨2858191246753370656001029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3810921662337827541334705 2858191246753370656001029)
                  ·
                    refine ⟨535910858766256998000193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2858191246753370656001029 535910858766256998000193)
                    ·
                      rfl

theorem cell23_3131048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3131048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131048 prefixEnd_3131048 := by exact prefixLift 3131048
  have htrace : WordTrace (prefixWord ++ tailWord_3131048) baseStart_3131048 baseEnd_3131048 := by
    simpa [prefixWord, tailWord_3131048, baseEnd_3131048] using wordTrace_append hprefix tailTrace_3131048
  have hstable : (prefixWord ++ tailWord_3131048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131048).length < 2 ^ (prefixWord ++ tailWord_3131048).sum := by decide
  have hdescent : baseEnd_3131048 < baseStart_3131048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131070 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_3131070 : Nat := 118140960795 + 3131070 * 2 ^ 59
def prefixEnd_3131070 : Nat := 4983230072969 + 3 ^ 40 * 3131070 * 2
def baseEnd_3131070 : Nat := 535914624291056635975159

theorem tailTrace_3131070 : CollatzResearch.WordTrace tailWord_3131070 prefixEnd_3131070 535914624291056635975159 := by
  unfold tailWord_3131070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14274938095834451128493833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76133003177783739351967109 14274938095834451128493833)
  ·
    refine ⟨10706203571875838346370375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14274938095834451128493833 10706203571875838346370375)
    ·
      refine ⟨16059305357813757519555563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10706203571875838346370375 16059305357813757519555563)
      ·
        refine ⟨24088958036720636279333345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16059305357813757519555563 24088958036720636279333345)
        ·
          refine ⟨18066718527540477209500009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24088958036720636279333345 18066718527540477209500009)
          ·
            refine ⟨13550038895655357907125007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18066718527540477209500009 13550038895655357907125007)
            ·
              refine ⟨20325058343483036860687511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13550038895655357907125007 20325058343483036860687511)
              ·
                refine ⟨30487587515224555291031267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20325058343483036860687511 30487587515224555291031267)
                ·
                  refine ⟨45731381272836832936546901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30487587515224555291031267 45731381272836832936546901)
                  ·
                    refine ⟨535914624291056635975159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45731381272836832936546901 535914624291056635975159)
                    ·
                      rfl

theorem cell23_3131070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_3131070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131070 prefixEnd_3131070 := by exact prefixLift 3131070
  have htrace : WordTrace (prefixWord ++ tailWord_3131070) baseStart_3131070 baseEnd_3131070 := by
    simpa [prefixWord, tailWord_3131070, baseEnd_3131070] using wordTrace_append hprefix tailTrace_3131070
  have hstable : (prefixWord ++ tailWord_3131070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131070).length < 2 ^ (prefixWord ++ tailWord_3131070).sum := by decide
  have hdescent : baseEnd_3131070 < baseStart_3131070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131080 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_3131080 : Nat := 118140960795 + 3131080 * 2 ^ 59
def prefixEnd_3131080 : Nat := 4983230072969 + 3 ^ 40 * 3131080 * 2
def baseEnd_3131080 : Nat := 1607749007679714868800431

theorem tailTrace_3131080 : CollatzResearch.WordTrace tailWord_3131080 prefixEnd_3131080 1607749007679714868800431 := by
  unfold tailWord_3131080
  simp only [CollatzResearch.WordTrace]
  refine ⟨57099934748319690367907347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76133246331092920490543129 57099934748319690367907347)
  ·
    refine ⟨85649902122479535551861021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57099934748319690367907347 85649902122479535551861021)
    ·
      refine ⟨32118713295929825831947883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85649902122479535551861021 32118713295929825831947883)
      ·
        refine ⟨48178069943894738747921825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32118713295929825831947883 48178069943894738747921825)
        ·
          refine ⟨36133552457921054060941369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48178069943894738747921825 36133552457921054060941369)
          ·
            refine ⟨27100164343440790545706027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36133552457921054060941369 27100164343440790545706027)
            ·
              refine ⟨40650246515161185818559041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27100164343440790545706027 40650246515161185818559041)
              ·
                refine ⟨30487684886370889363919281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40650246515161185818559041 30487684886370889363919281)
                ·
                  refine ⟨22865763664778167022939461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30487684886370889363919281 22865763664778167022939461)
                  ·
                    refine ⟨4287330687145906316801149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22865763664778167022939461 4287330687145906316801149)
                    ·
                      refine ⟨1607749007679714868800431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4287330687145906316801149 1607749007679714868800431)
                      ·
                        rfl

theorem cell23_3131080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_3131080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131080 prefixEnd_3131080 := by exact prefixLift 3131080
  have htrace : WordTrace (prefixWord ++ tailWord_3131080) baseStart_3131080 baseEnd_3131080 := by
    simpa [prefixWord, tailWord_3131080, baseEnd_3131080] using wordTrace_append hprefix tailTrace_3131080
  have hstable : (prefixWord ++ tailWord_3131080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131080).length < 2 ^ (prefixWord ++ tailWord_3131080).sum := by decide
  have hdescent : baseEnd_3131080 < baseStart_3131080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131117 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 7]
def baseStart_3131117 : Nat := 118140960795 + 3131117 * 2 ^ 59
def prefixEnd_3131117 : Nat := 4983230072969 + 3 ^ 40 * 3131117 * 2
def baseEnd_3131117 : Nat := 178640889607103469337529

theorem tailTrace_3131117 : CollatzResearch.WordTrace tailWord_3131117 prefixEnd_3131117 178640889607103469337529 := by
  unfold tailWord_3131117
  simp only [CollatzResearch.WordTrace]
  refine ⟨114201218997505336054911605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76134145998336890703274403 114201218997505336054911605)
  ·
    refine ⟨10706364281016125255147963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114201218997505336054911605 10706364281016125255147963)
    ·
      refine ⟨16059546421524187882721945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10706364281016125255147963 16059546421524187882721945)
      ·
        refine ⟨12044659816143140912041459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16059546421524187882721945 12044659816143140912041459)
        ·
          refine ⟨18066989724214711368062189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12044659816143140912041459 18066989724214711368062189)
          ·
            refine ⟨6775121146580516763023321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18066989724214711368062189 6775121146580516763023321)
            ·
              refine ⟨5081340859935387572267491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6775121146580516763023321 5081340859935387572267491)
              ·
                refine ⟨7622011289903081358401237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5081340859935387572267491 7622011289903081358401237)
                ·
                  refine ⟨178640889607103469337529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7622011289903081358401237 178640889607103469337529)
                  ·
                    rfl

theorem cell23_3131117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_3131117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131117 prefixEnd_3131117 := by exact prefixLift 3131117
  have htrace : WordTrace (prefixWord ++ tailWord_3131117) baseStart_3131117 baseEnd_3131117 := by
    simpa [prefixWord, tailWord_3131117, baseEnd_3131117] using wordTrace_append hprefix tailTrace_3131117
  have hstable : (prefixWord ++ tailWord_3131117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131117).length < 2 ^ (prefixWord ++ tailWord_3131117).sum := by decide
  have hdescent : baseEnd_3131117 < baseStart_3131117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131137 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_3131137 : Nat := 118140960795 + 3131137 * 2 ^ 59
def prefixEnd_3131137 : Nat := 4983230072969 + 3 ^ 40 * 3131137 * 2
def baseEnd_3131137 : Nat := 1607778276077021145787669

theorem tailTrace_3131137 : CollatzResearch.WordTrace tailWord_3131137 prefixEnd_3131137 1607778276077021145787669 := by
  unfold tailWord_3131137
  simp only [CollatzResearch.WordTrace]
  refine ⟨114201948457432879470639665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76134632304955252980426443 114201948457432879470639665)
  ·
    refine ⟨85651461343074659602979749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114201948457432879470639665 85651461343074659602979749)
    ·
      refine ⟨16059649001826498675558703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85651461343074659602979749 16059649001826498675558703)
      ·
        refine ⟨24089473502739748013338055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16059649001826498675558703 24089473502739748013338055)
        ·
          refine ⟨36134210254109622020007083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24089473502739748013338055 36134210254109622020007083)
          ·
            refine ⟨54201315381164433030010625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36134210254109622020007083 54201315381164433030010625)
            ·
              refine ⟨40650986535873324772507969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54201315381164433030010625 40650986535873324772507969)
              ·
                refine ⟨30488239901904993579380977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40650986535873324772507969 30488239901904993579380977)
                ·
                  refine ⟨22866179926428745184535733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30488239901904993579380977 22866179926428745184535733)
                  ·
                    refine ⟨2143704368102694861050225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22866179926428745184535733 2143704368102694861050225)
                    ·
                      refine ⟨1607778276077021145787669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2143704368102694861050225 1607778276077021145787669)
                      ·
                        rfl

theorem cell23_3131137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_3131137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131137 prefixEnd_3131137 := by exact prefixLift 3131137
  have htrace : WordTrace (prefixWord ++ tailWord_3131137) baseStart_3131137 baseEnd_3131137 := by
    simpa [prefixWord, tailWord_3131137, baseEnd_3131137] using wordTrace_append hprefix tailTrace_3131137
  have hstable : (prefixWord ++ tailWord_3131137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131137).length < 2 ^ (prefixWord ++ tailWord_3131137).sum := by decide
  have hdescent : baseEnd_3131137 < baseStart_3131137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131167 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 4]
def baseStart_3131167 : Nat := 118140960795 + 3131167 * 2 ^ 59
def prefixEnd_3131167 : Nat := 4983230072969 + 3 ^ 40 * 3131167 * 2
def baseEnd_3131167 : Nat := 1607793680496656028412531

theorem tailTrace_3131167 : CollatzResearch.WordTrace tailWord_3131167 prefixEnd_3131167 1607793680496656028412531 := by
  unfold tailWord_3131167
  simp only [CollatzResearch.WordTrace]
  refine ⟨114203042647324194594231755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76135361764882796396154503 114203042647324194594231755)
  ·
    refine ⟨171304563970986291891347633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114203042647324194594231755 171304563970986291891347633)
    ·
      refine ⟨128478422978239718918510725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171304563970986291891347633 128478422978239718918510725)
      ·
        refine ⟨24089704308419947297220761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128478422978239718918510725 24089704308419947297220761)
        ·
          refine ⟨18067278231314960472915571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24089704308419947297220761 18067278231314960472915571)
          ·
            refine ⟨27100917346972440709373357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18067278231314960472915571 27100917346972440709373357)
            ·
              refine ⟨10162844005114665266015009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27100917346972440709373357 10162844005114665266015009)
              ·
                refine ⟨7622133003835998949511257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10162844005114665266015009 7622133003835998949511257)
                ·
                  refine ⟨5716599752876999212133443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7622133003835998949511257 5716599752876999212133443)
                  ·
                    refine ⟨8574899629315498818200165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5716599752876999212133443 8574899629315498818200165)
                    ·
                      refine ⟨1607793680496656028412531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8574899629315498818200165 1607793680496656028412531)
                      ·
                        rfl

theorem cell23_3131167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_3131167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131167 prefixEnd_3131167 := by exact prefixLift 3131167
  have htrace : WordTrace (prefixWord ++ tailWord_3131167) baseStart_3131167 baseEnd_3131167 := by
    simpa [prefixWord, tailWord_3131167, baseEnd_3131167] using wordTrace_append hprefix tailTrace_3131167
  have hstable : (prefixWord ++ tailWord_3131167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131167).length < 2 ^ (prefixWord ++ tailWord_3131167).sum := by decide
  have hdescent : baseEnd_3131167 < baseStart_3131167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131228 : List Nat := [2, 2, 4, 2, 2, 1, 1, 4, 1, 4]
def baseStart_3131228 : Nat := 118140960795 + 3131228 * 2 ^ 59
def prefixEnd_3131228 : Nat := 4983230072969 + 3 ^ 40 * 3131228 * 2
def baseEnd_3131228 : Nat := 535941667605526763249917

theorem tailTrace_3131228 : CollatzResearch.WordTrace tailWord_3131228 prefixEnd_3131228 535941667605526763249917 := by
  unfold tailWord_3131228
  simp only [CollatzResearch.WordTrace]
  refine ⟨57102633750051601006101169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76136845000068801341468225 57102633750051601006101169)
  ·
    refine ⟨42826975312538700754575877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57102633750051601006101169 42826975312538700754575877)
    ·
      refine ⟨8030057871101006391482977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42826975312538700754575877 8030057871101006391482977)
      ·
        refine ⟨6022543403325754793612233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8030057871101006391482977 6022543403325754793612233)
        ·
          refine ⟨4516907552494316095209175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6022543403325754793612233 4516907552494316095209175)
          ·
            refine ⟨6775361328741474142813763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516907552494316095209175 6775361328741474142813763)
            ·
              refine ⟨10163041993112211214220645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6775361328741474142813763 10163041993112211214220645)
              ·
                refine ⟨1905570373708539602666371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10163041993112211214220645 1905570373708539602666371)
                ·
                  refine ⟨2858355560562809403999557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905570373708539602666371 2858355560562809403999557)
                  ·
                    refine ⟨535941667605526763249917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2858355560562809403999557 535941667605526763249917)
                    ·
                      rfl

theorem cell23_3131228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_3131228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131228 prefixEnd_3131228 := by exact prefixLift 3131228
  have htrace : WordTrace (prefixWord ++ tailWord_3131228) baseStart_3131228 baseEnd_3131228 := by
    simpa [prefixWord, tailWord_3131228, baseEnd_3131228] using wordTrace_append hprefix tailTrace_3131228
  have hstable : (prefixWord ++ tailWord_3131228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131228).length < 2 ^ (prefixWord ++ tailWord_3131228).sum := by decide
  have hdescent : baseEnd_3131228 < baseStart_3131228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131257 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 4]
def baseStart_3131257 : Nat := 118140960795 + 3131257 * 2 ^ 59
def prefixEnd_3131257 : Nat := 4983230072969 + 3 ^ 40 * 3131257 * 2
def baseEnd_3131257 : Nat := 1607839893755560676287117

theorem tailTrace_3131257 : CollatzResearch.WordTrace tailWord_3131257 prefixEnd_3131257 1607839893755560676287117 := by
  unfold tailWord_3131257
  simp only [CollatzResearch.WordTrace]
  refine ⟨114206325216998139965008025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76137550144665426643338683 114206325216998139965008025)
  ·
    refine ⟨85654743912748604973756019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114206325216998139965008025 85654743912748604973756019)
    ·
      refine ⟨128482115869122907460634029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85654743912748604973756019 128482115869122907460634029)
      ·
        refine ⟨48180793450921090297737761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128482115869122907460634029 48180793450921090297737761)
        ·
          refine ⟨36135595088190817723303321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48180793450921090297737761 36135595088190817723303321)
          ·
            refine ⟨27101696316143113292477491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36135595088190817723303321 27101696316143113292477491)
            ·
              refine ⟨40652544474214669938716237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27101696316143113292477491 40652544474214669938716237)
              ·
                refine ⟨15244704177830501227018589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40652544474214669938716237 15244704177830501227018589)
                ·
                  refine ⟨5716764066686437960131971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15244704177830501227018589 5716764066686437960131971)
                  ·
                    refine ⟨8575146100029656940197957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5716764066686437960131971 8575146100029656940197957)
                    ·
                      refine ⟨1607839893755560676287117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8575146100029656940197957 1607839893755560676287117)
                      ·
                        rfl

theorem cell23_3131257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_3131257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131257 prefixEnd_3131257 := by exact prefixLift 3131257
  have htrace : WordTrace (prefixWord ++ tailWord_3131257) baseStart_3131257 baseEnd_3131257 := by
    simpa [prefixWord, tailWord_3131257, baseEnd_3131257] using wordTrace_append hprefix tailTrace_3131257
  have hstable : (prefixWord ++ tailWord_3131257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131257).length < 2 ^ (prefixWord ++ tailWord_3131257).sum := by decide
  have hdescent : baseEnd_3131257 < baseStart_3131257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131267 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 1, 6]
def baseStart_3131267 : Nat := 118140960795 + 3131267 * 2 ^ 59
def prefixEnd_3131267 : Nat := 4983230072969 + 3 ^ 40 * 3131267 * 2
def baseEnd_3131267 : Nat := 535948342854035212387357

theorem tailTrace_3131267 : CollatzResearch.WordTrace tailWord_3131267 prefixEnd_3131267 535948342854035212387357 := by
  unfold tailWord_3131267
  simp only [CollatzResearch.WordTrace]
  refine ⟨114206689946961911672872055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76137793297974607781914703 114206689946961911672872055)
  ·
    refine ⟨171310034920442867509308083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114206689946961911672872055 171310034920442867509308083)
    ·
      refine ⟨256965052380664301263962125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171310034920442867509308083 256965052380664301263962125)
      ·
        refine ⟨96361894642749112973985797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256965052380664301263962125 96361894642749112973985797)
        ·
          refine ⟨18067855245515458682622337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96361894642749112973985797 18067855245515458682622337)
          ·
            refine ⟨13550891434136594011966753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18067855245515458682622337 13550891434136594011966753)
            ·
              refine ⟨10163168575602445508975065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13550891434136594011966753 10163168575602445508975065)
              ·
                refine ⟨7622376431701834131731299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10163168575602445508975065 7622376431701834131731299)
                ·
                  refine ⟨11433564647552751197596949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7622376431701834131731299 11433564647552751197596949)
                  ·
                    refine ⟨535948342854035212387357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11433564647552751197596949 535948342854035212387357)
                    ·
                      rfl

theorem cell23_3131267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 6].length) (baseStart_3131267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131267 prefixEnd_3131267 := by exact prefixLift 3131267
  have htrace : WordTrace (prefixWord ++ tailWord_3131267) baseStart_3131267 baseEnd_3131267 := by
    simpa [prefixWord, tailWord_3131267, baseEnd_3131267] using wordTrace_append hprefix tailTrace_3131267
  have hstable : (prefixWord ++ tailWord_3131267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131267).length < 2 ^ (prefixWord ++ tailWord_3131267).sum := by decide
  have hdescent : baseEnd_3131267 < baseStart_3131267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131325 : List Nat := [1, 4, 1, 2, 3, 1, 3, 3, 1, 2, 2]
def baseStart_3131325 : Nat := 118140960795 + 3131325 * 2 ^ 59
def prefixEnd_3131325 : Nat := 4983230072969 + 3 ^ 40 * 3131325 * 2
def baseEnd_3131325 : Nat := 1607874810440066410236805

theorem tailTrace_3131325 : CollatzResearch.WordTrace tailWord_3131325 prefixEnd_3131325 1607874810440066410236805 := by
  unfold tailWord_3131325
  simp only [CollatzResearch.WordTrace]
  refine ⟨114208805380751787578483429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76139203587167858385655619 114208805380751787578483429)
  ·
    refine ⟨21414151008890960170965643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114208805380751787578483429 21414151008890960170965643)
    ·
      refine ⟨32121226513336440256448465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21414151008890960170965643 32121226513336440256448465)
      ·
        refine ⟨24090919885002330192336349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32121226513336440256448465 24090919885002330192336349)
        ·
          refine ⟨9034094956875873822126131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24090919885002330192336349 9034094956875873822126131)
          ·
            refine ⟨13551142435313810733189197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9034094956875873822126131 13551142435313810733189197)
            ·
              refine ⟨5081678413242679024945949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13551142435313810733189197 5081678413242679024945949)
              ·
                refine ⟨1905629404966004634354731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5081678413242679024945949 1905629404966004634354731)
                ·
                  refine ⟨2858444107449006951532097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905629404966004634354731 2858444107449006951532097)
                  ·
                    refine ⟨2143833080586755213649073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2858444107449006951532097 2143833080586755213649073)
                    ·
                      refine ⟨1607874810440066410236805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2143833080586755213649073 1607874810440066410236805)
                      ·
                        rfl

theorem cell23_3131325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_3131325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131325 prefixEnd_3131325 := by exact prefixLift 3131325
  have htrace : WordTrace (prefixWord ++ tailWord_3131325) baseStart_3131325 baseEnd_3131325 := by
    simpa [prefixWord, tailWord_3131325, baseEnd_3131325] using wordTrace_append hprefix tailTrace_3131325
  have hstable : (prefixWord ++ tailWord_3131325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131325).length < 2 ^ (prefixWord ++ tailWord_3131325).sum := by decide
  have hdescent : baseEnd_3131325 < baseStart_3131325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131362 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3131362 : Nat := 118140960795 + 3131362 * 2 ^ 59
def prefixEnd_3131362 : Nat := 4983230072969 + 3 ^ 40 * 3131362 * 2
def baseEnd_3131362 : Nat := 1607893809224282765474135

theorem tailTrace_3131362 : CollatzResearch.WordTrace tailWord_3131362 prefixEnd_3131362 1607893809224282765474135 := by
  unfold tailWord_3131362
  simp only [CollatzResearch.WordTrace]
  refine ⟨28552538720404435724395085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76140103254411828598386893 28552538720404435724395085)
  ·
    refine ⟨10707202020151663396648157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28552538720404435724395085 10707202020151663396648157)
    ·
      refine ⟨4015200757556873773743059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10707202020151663396648157 4015200757556873773743059)
      ·
        refine ⟨6022801136335310660614589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4015200757556873773743059 6022801136335310660614589)
        ·
          refine ⟨2258550426125741497730471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6022801136335310660614589 2258550426125741497730471)
          ·
            refine ⟨3387825639188612246595707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258550426125741497730471 3387825639188612246595707)
            ·
              refine ⟨5081738458782918369893561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3387825639188612246595707 5081738458782918369893561)
              ·
                refine ⟨3811303844087188777420171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5081738458782918369893561 3811303844087188777420171)
                ·
                  refine ⟨5716955766130783166130257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811303844087188777420171 5716955766130783166130257)
                  ·
                    refine ⟨4287716824598087374597693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5716955766130783166130257 4287716824598087374597693)
                    ·
                      refine ⟨1607893809224282765474135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4287716824598087374597693 1607893809224282765474135)
                      ·
                        rfl

theorem cell23_3131362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3131362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131362 prefixEnd_3131362 := by exact prefixLift 3131362
  have htrace : WordTrace (prefixWord ++ tailWord_3131362) baseStart_3131362 baseEnd_3131362 := by
    simpa [prefixWord, tailWord_3131362, baseEnd_3131362] using wordTrace_append hprefix tailTrace_3131362
  have hstable : (prefixWord ++ tailWord_3131362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131362).length < 2 ^ (prefixWord ++ tailWord_3131362).sum := by decide
  have hdescent : baseEnd_3131362 < baseStart_3131362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131417 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 1, 7]
def baseStart_3131417 : Nat := 118140960795 + 3131417 * 2 ^ 59
def prefixEnd_3131417 : Nat := 4983230072969 + 3 ^ 40 * 3131417 * 2
def baseEnd_3131417 : Nat := 535974016886760016762127

theorem tailTrace_3131417 : CollatzResearch.WordTrace tailWord_3131417 prefixEnd_3131417 535974016886760016762127 := by
  unfold tailWord_3131417
  simp only [CollatzResearch.WordTrace]
  refine ⟨114212160896418487290832505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76141440597612324860555003 114212160896418487290832505)
  ·
    refine ⟨85659120672313865468124379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114212160896418487290832505 85659120672313865468124379)
    ·
      refine ⟨128488681008470798202186569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85659120672313865468124379 128488681008470798202186569)
      ·
        refine ⟨96366510756353098651639927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128488681008470798202186569 96366510756353098651639927)
        ·
          refine ⟨144549766134529647977459891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96366510756353098651639927 144549766134529647977459891)
          ·
            refine ⟨216824649201794471966189837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144549766134529647977459891 216824649201794471966189837)
            ·
              refine ⟨81309243450672926987321189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216824649201794471966189837 81309243450672926987321189)
              ·
                refine ⟨15245483147001173810122723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81309243450672926987321189 15245483147001173810122723)
                ·
                  refine ⟨22868224720501760715184085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15245483147001173810122723 22868224720501760715184085)
                  ·
                    refine ⟨535974016886760016762127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22868224720501760715184085 535974016886760016762127)
                    ·
                      rfl

theorem cell23_3131417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_3131417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131417 prefixEnd_3131417 := by exact prefixLift 3131417
  have htrace : WordTrace (prefixWord ++ tailWord_3131417) baseStart_3131417 baseEnd_3131417 := by
    simpa [prefixWord, tailWord_3131417, baseEnd_3131417] using wordTrace_append hprefix tailTrace_3131417
  have hstable : (prefixWord ++ tailWord_3131417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131417).length < 2 ^ (prefixWord ++ tailWord_3131417).sum := by decide
  have hdescent : baseEnd_3131417 < baseStart_3131417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131438 : List Nat := [4, 1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_3131438 : Nat := 118140960795 + 3131438 * 2 ^ 59
def prefixEnd_3131438 : Nat := 4983230072969 + 3 ^ 40 * 3131438 * 2
def baseEnd_3131438 : Nat := 178659203750447163124865

theorem tailTrace_3131438 : CollatzResearch.WordTrace tailWord_3131438 prefixEnd_3131438 178659203750447163124865 := by
  unfold tailWord_3131438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14276615853667800984668371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76141951219561605251564645 14276615853667800984668371)
  ·
    refine ⟨21414923780501701477002557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14276615853667800984668371 21414923780501701477002557)
    ·
      refine ⟨8030596417688138053875959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21414923780501701477002557 8030596417688138053875959)
      ·
        refine ⟨12045894626532207080813939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8030596417688138053875959 12045894626532207080813939)
        ·
          refine ⟨18068841939798310621220909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12045894626532207080813939 18068841939798310621220909)
          ·
            refine ⟨6775815727424366482957841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18068841939798310621220909 6775815727424366482957841)
            ·
              refine ⟨5081861795568274862218381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6775815727424366482957841 5081861795568274862218381)
              ·
                refine ⟨1905698173338103073331893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5081861795568274862218381 1905698173338103073331893)
                ·
                  refine ⟨178659203750447163124865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1905698173338103073331893 178659203750447163124865)
                  ·
                    rfl

theorem cell23_3131438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_3131438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131438 prefixEnd_3131438 := by exact prefixLift 3131438
  have htrace : WordTrace (prefixWord ++ tailWord_3131438) baseStart_3131438 baseEnd_3131438 := by
    simpa [prefixWord, tailWord_3131438, baseEnd_3131438] using wordTrace_append hprefix tailTrace_3131438
  have hstable : (prefixWord ++ tailWord_3131438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131438).length < 2 ^ (prefixWord ++ tailWord_3131438).sum := by decide
  have hdescent : baseEnd_3131438 < baseStart_3131438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131528 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 6]
def baseStart_3131528 : Nat := 118140960795 + 3131528 * 2 ^ 59
def prefixEnd_3131528 : Nat := 4983230072969 + 3 ^ 40 * 3131528 * 2
def baseEnd_3131528 : Nat := 178664338556992123999819

theorem tailTrace_3131528 : CollatzResearch.WordTrace tailWord_3131528 prefixEnd_3131528 178664338556992123999819 := by
  unfold tailWord_3131528
  simp only [CollatzResearch.WordTrace]
  refine ⟨57108104699508176624061619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76144139599344235498748825 57108104699508176624061619)
  ·
    refine ⟨85662157049262264936092429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57108104699508176624061619 85662157049262264936092429)
    ·
      refine ⟨32123308893473349351034661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85662157049262264936092429 32123308893473349351034661)
      ·
        refine ⟨6023120417526253003318999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32123308893473349351034661 6023120417526253003318999)
        ·
          refine ⟨9034680626289379504978499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6023120417526253003318999 9034680626289379504978499)
          ·
            refine ⟨13552020939434069257467749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9034680626289379504978499 13552020939434069257467749)
            ·
              refine ⟨2541003926143887985775203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13552020939434069257467749 2541003926143887985775203)
              ·
                refine ⟨3811505889215831978662805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541003926143887985775203 3811505889215831978662805)
                ·
                  refine ⟨178664338556992123999819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3811505889215831978662805 178664338556992123999819)
                  ·
                    rfl

theorem cell23_3131528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 6].length) (baseStart_3131528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131528 prefixEnd_3131528 := by exact prefixLift 3131528
  have htrace : WordTrace (prefixWord ++ tailWord_3131528) baseStart_3131528 baseEnd_3131528 := by
    simpa [prefixWord, tailWord_3131528, baseEnd_3131528] using wordTrace_append hprefix tailTrace_3131528
  have hstable : (prefixWord ++ tailWord_3131528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131528).length < 2 ^ (prefixWord ++ tailWord_3131528).sum := by decide
  have hdescent : baseEnd_3131528 < baseStart_3131528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131538 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_3131538 : Nat := 118140960795 + 3131538 * 2 ^ 59
def prefixEnd_3131538 : Nat := 4983230072969 + 3 ^ 40 * 3131538 * 2
def baseEnd_3131538 : Nat := 1607984181819474076873325

theorem tailTrace_3131538 : CollatzResearch.WordTrace tailWord_3131538 prefixEnd_3131538 1607984181819474076873325 := by
  unfold tailWord_3131538
  simp only [CollatzResearch.WordTrace]
  refine ⟨28554143532245031238996817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76144382752653416637324845 28554143532245031238996817)
  ·
    refine ⟨21415607649183773429247613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28554143532245031238996817 21415607649183773429247613)
    ·
      refine ⟨8030852868443915035967855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21415607649183773429247613 8030852868443915035967855)
      ·
        refine ⟨12046279302665872553951783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8030852868443915035967855 12046279302665872553951783)
        ·
          refine ⟨18069418953998808830927675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12046279302665872553951783 18069418953998808830927675)
          ·
            refine ⟨27104128430998213246391513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18069418953998808830927675 27104128430998213246391513)
            ·
              refine ⟨20328096323248659934793635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27104128430998213246391513 20328096323248659934793635)
              ·
                refine ⟨30492144484872989902190453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20328096323248659934793635 30492144484872989902190453)
                ·
                  refine ⟨2858638545456842803330355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30492144484872989902190453 2858638545456842803330355)
                  ·
                    refine ⟨4287957818185264204995533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2858638545456842803330355 4287957818185264204995533)
                    ·
                      refine ⟨1607984181819474076873325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4287957818185264204995533 1607984181819474076873325)
                      ·
                        rfl

theorem cell23_3131538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_3131538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131538 prefixEnd_3131538 := by exact prefixLift 3131538
  have htrace : WordTrace (prefixWord ++ tailWord_3131538) baseStart_3131538 baseEnd_3131538 := by
    simpa [prefixWord, tailWord_3131538, baseEnd_3131538] using wordTrace_append hprefix tailTrace_3131538
  have hstable : (prefixWord ++ tailWord_3131538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131538).length < 2 ^ (prefixWord ++ tailWord_3131538).sum := by decide
  have hdescent : baseEnd_3131538 < baseStart_3131538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131565 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_3131565 : Nat := 118140960795 + 3131565 * 2 ^ 59
def prefixEnd_3131565 : Nat := 4983230072969 + 3 ^ 40 * 3131565 * 2
def baseEnd_3131565 : Nat := 1607998045797145471235701

theorem tailTrace_3131565 : CollatzResearch.WordTrace tailWord_3131565 prefixEnd_3131565 1607998045797145471235701 := by
  unfold tailWord_3131565
  simp only [CollatzResearch.WordTrace]
  refine ⟨114217558899882308567220149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76145039266588205711480099 114217558899882308567220149)
  ·
    refine ⟨10707896146863966428176889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114217558899882308567220149 10707896146863966428176889)
    ·
      refine ⟨8030922110147974821132667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10707896146863966428176889 8030922110147974821132667)
      ·
        refine ⟨12046383165221962231699001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8030922110147974821132667 12046383165221962231699001)
        ·
          refine ⟨9034787373916471673774251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12046383165221962231699001 9034787373916471673774251)
          ·
            refine ⟨13552181060874707510661377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9034787373916471673774251 13552181060874707510661377)
            ·
              refine ⟨10164135795656030632996033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13552181060874707510661377 10164135795656030632996033)
              ·
                refine ⟨7623101846742022974747025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10164135795656030632996033 7623101846742022974747025)
                ·
                  refine ⟨5717326385056517231060269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7623101846742022974747025 5717326385056517231060269)
                  ·
                    refine ⟨2143997394396193961647601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5717326385056517231060269 2143997394396193961647601)
                    ·
                      refine ⟨1607998045797145471235701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2143997394396193961647601 1607998045797145471235701)
                      ·
                        rfl

theorem cell23_3131565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_3131565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131565 prefixEnd_3131565 := by exact prefixLift 3131565
  have htrace : WordTrace (prefixWord ++ tailWord_3131565) baseStart_3131565 baseEnd_3131565 := by
    simpa [prefixWord, tailWord_3131565, baseEnd_3131565] using wordTrace_append hprefix tailTrace_3131565
  have hstable : (prefixWord ++ tailWord_3131565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131565).length < 2 ^ (prefixWord ++ tailWord_3131565).sum := by decide
  have hdescent : baseEnd_3131565 < baseStart_3131565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131566 : List Nat := [4, 1, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3131566 : Nat := 118140960795 + 3131566 * 2 ^ 59
def prefixEnd_3131566 : Nat := 4983230072969 + 3 ^ 40 * 3131566 * 2
def baseEnd_3131566 : Nat := 535999519759266655774399

theorem tailTrace_3131566 : CollatzResearch.WordTrace tailWord_3131566 prefixEnd_3131566 535999519759266655774399 := by
  unfold tailWord_3131566
  simp only [CollatzResearch.WordTrace]
  refine ⟨14277199421609835717250819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76145063581919123825337701 14277199421609835717250819)
  ·
    refine ⟨21415799132414753575876229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14277199421609835717250819 21415799132414753575876229)
    ·
      refine ⟨4015462337327766295476793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21415799132414753575876229 4015462337327766295476793)
      ·
        refine ⟨3011596752995824721607595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4015462337327766295476793 3011596752995824721607595)
        ·
          refine ⟨4517395129493737082411393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011596752995824721607595 4517395129493737082411393)
          ·
            refine ⟨3388046347120302811808545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4517395129493737082411393 3388046347120302811808545)
            ·
              refine ⟨2541034760340227108856409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3388046347120302811808545 2541034760340227108856409)
              ·
                refine ⟨1905776070255170331642307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2541034760340227108856409 1905776070255170331642307)
                ·
                  refine ⟨2858664105382755497463461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905776070255170331642307 2858664105382755497463461)
                  ·
                    refine ⟨535999519759266655774399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2858664105382755497463461 535999519759266655774399)
                    ·
                      rfl

theorem cell23_3131566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3131566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131566 prefixEnd_3131566 := by exact prefixLift 3131566
  have htrace : WordTrace (prefixWord ++ tailWord_3131566) baseStart_3131566 baseEnd_3131566 := by
    simpa [prefixWord, tailWord_3131566, baseEnd_3131566] using wordTrace_append hprefix tailTrace_3131566
  have hstable : (prefixWord ++ tailWord_3131566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131566).length < 2 ^ (prefixWord ++ tailWord_3131566).sum := by decide
  have hdescent : baseEnd_3131566 < baseStart_3131566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131588 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3131588 : Nat := 118140960795 + 3131588 * 2 ^ 59
def prefixEnd_3131588 : Nat := 4983230072969 + 3 ^ 40 * 3131588 * 2
def baseEnd_3131588 : Nat := 536003285284066293749365

theorem tailTrace_3131588 : CollatzResearch.WordTrace tailWord_3131588 prefixEnd_3131588 536003285284066293749365 := by
  unfold tailWord_3131588
  simp only [CollatzResearch.WordTrace]
  refine ⟨57109198889399491747653709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76145598519199322330204945 57109198889399491747653709)
  ·
    refine ⟨21415949583524809405370141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57109198889399491747653709 21415949583524809405370141)
    ·
      refine ⟨8030981093821803527013803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21415949583524809405370141 8030981093821803527013803)
      ·
        refine ⟨12046471640732705290520705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8030981093821803527013803 12046471640732705290520705)
        ·
          refine ⟨9034853730549528967890529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12046471640732705290520705 9034853730549528967890529)
          ·
            refine ⟨6776140297912146725917897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9034853730549528967890529 6776140297912146725917897)
            ·
              refine ⟨5082105223434110044438423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6776140297912146725917897 5082105223434110044438423)
              ·
                refine ⟨7623157835151165066657635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5082105223434110044438423 7623157835151165066657635)
                ·
                  refine ⟨11434736752726747599986453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7623157835151165066657635 11434736752726747599986453)
                  ·
                    refine ⟨536003285284066293749365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11434736752726747599986453 536003285284066293749365)
                    ·
                      rfl

theorem cell23_3131588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3131588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131588 prefixEnd_3131588 := by exact prefixLift 3131588
  have htrace : WordTrace (prefixWord ++ tailWord_3131588) baseStart_3131588 baseEnd_3131588 := by
    simpa [prefixWord, tailWord_3131588, baseEnd_3131588] using wordTrace_append hprefix tailTrace_3131588
  have hstable : (prefixWord ++ tailWord_3131588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131588).length < 2 ^ (prefixWord ++ tailWord_3131588).sum := by decide
  have hdescent : baseEnd_3131588 < baseStart_3131588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131598 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_3131598 : Nat := 118140960795 + 3131598 * 2 ^ 59
def prefixEnd_3131598 : Nat := 4983230072969 + 3 ^ 40 * 3131598 * 2
def baseEnd_3131598 : Nat := 1608014990658743842123049

theorem tailTrace_3131598 : CollatzResearch.WordTrace tailWord_3131598 prefixEnd_3131598 1608014990658743842123049 := by
  unfold tailWord_3131598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14277345313595344400396431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76145841672508503468780965 14277345313595344400396431)
  ·
    refine ⟨21416017970393016600594647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14277345313595344400396431 21416017970393016600594647)
    ·
      refine ⟨32124026955589524900891971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21416017970393016600594647 32124026955589524900891971)
      ·
        refine ⟨48186040433384287351337957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32124026955589524900891971 48186040433384287351337957)
        ·
          refine ⟨9034882581259553878375867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48186040433384287351337957 9034882581259553878375867)
          ·
            refine ⟨13552323871889330817563801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9034882581259553878375867 13552323871889330817563801)
            ·
              refine ⟨10164242903916998113172851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13552323871889330817563801 10164242903916998113172851)
              ·
                refine ⟨15246364355875497169759277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10164242903916998113172851 15246364355875497169759277)
                ·
                  refine ⟨5717386633453311438659729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15246364355875497169759277 5717386633453311438659729)
                  ·
                    refine ⟨4288039975089983578994797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5717386633453311438659729 4288039975089983578994797)
                    ·
                      refine ⟨1608014990658743842123049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4288039975089983578994797 1608014990658743842123049)
                      ·
                        rfl

theorem cell23_3131598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_3131598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131598 prefixEnd_3131598 := by exact prefixLift 3131598
  have htrace : WordTrace (prefixWord ++ tailWord_3131598) baseStart_3131598 baseEnd_3131598 := by
    simpa [prefixWord, tailWord_3131598, baseEnd_3131598] using wordTrace_append hprefix tailTrace_3131598
  have hstable : (prefixWord ++ tailWord_3131598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131598).length < 2 ^ (prefixWord ++ tailWord_3131598).sum := by decide
  have hdescent : baseEnd_3131598 < baseStart_3131598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131612 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3131612 : Nat := 118140960795 + 3131612 * 2 ^ 59
def prefixEnd_3131612 : Nat := 4983230072969 + 3 ^ 40 * 3131612 * 2
def baseEnd_3131612 : Nat := 1608022179387906787347985

theorem tailTrace_3131612 : CollatzResearch.WordTrace tailWord_3131612 prefixEnd_3131612 1608022179387906787347985 := by
  unfold tailWord_3131612
  simp only [CollatzResearch.WordTrace]
  refine ⟨57109636565356017797090545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76146182087141357062787393 57109636565356017797090545)
  ·
    refine ⟨42832227424017013347817909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57109636565356017797090545 42832227424017013347817909)
    ·
      refine ⟨4015521321001595001357929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42832227424017013347817909 4015521321001595001357929)
      ·
        refine ⟨3011640990751196251018447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4015521321001595001357929 3011640990751196251018447)
        ·
          refine ⟨4517461486126794376527671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011640990751196251018447 4517461486126794376527671)
          ·
            refine ⟨6776192229190191564791507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517461486126794376527671 6776192229190191564791507)
            ·
              refine ⟨10164288343785287347187261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776192229190191564791507 10164288343785287347187261)
              ·
                refine ⟨3811608128919482755195223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10164288343785287347187261 3811608128919482755195223)
                ·
                  refine ⟨5717412193379224132792835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811608128919482755195223 5717412193379224132792835)
                  ·
                    refine ⟨8576118290068836199189253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5717412193379224132792835 8576118290068836199189253)
                    ·
                      refine ⟨1608022179387906787347985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8576118290068836199189253 1608022179387906787347985)
                      ·
                        rfl

theorem cell23_3131612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3131612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131612 prefixEnd_3131612 := by exact prefixLift 3131612
  have htrace : WordTrace (prefixWord ++ tailWord_3131612) baseStart_3131612 baseEnd_3131612 := by
    simpa [prefixWord, tailWord_3131612, baseEnd_3131612] using wordTrace_append hprefix tailTrace_3131612
  have hstable : (prefixWord ++ tailWord_3131612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131612).length < 2 ^ (prefixWord ++ tailWord_3131612).sum := by decide
  have hdescent : baseEnd_3131612 < baseStart_3131612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131628 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 3]
def baseStart_3131628 : Nat := 118140960795 + 3131628 * 2 ^ 59
def prefixEnd_3131628 : Nat := 4983230072969 + 3 ^ 40 * 3131628 * 2
def baseEnd_3131628 : Nat := 1608030395078378724747911

theorem tailTrace_3131628 : CollatzResearch.WordTrace tailWord_3131628 prefixEnd_3131628 1608030395078378724747911 := by
  unfold tailWord_3131628
  simp only [CollatzResearch.WordTrace]
  refine ⟨57109928349327035163381769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76146571132436046884509025 57109928349327035163381769)
  ·
    refine ⟨42832446261995276372536327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57109928349327035163381769 42832446261995276372536327)
    ·
      refine ⟨64248669392992914558804491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42832446261995276372536327 64248669392992914558804491)
      ·
        refine ⟨96373004089489371838206737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64248669392992914558804491 96373004089489371838206737)
        ·
          refine ⟨72279753067117028878655053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96373004089489371838206737 72279753067117028878655053)
          ·
            refine ⟨27104907400168885829495645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72279753067117028878655053 27104907400168885829495645)
            ·
              refine ⟨10164340275063332186060867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27104907400168885829495645 10164340275063332186060867)
              ·
                refine ⟨15246510412594998279091301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10164340275063332186060867 15246510412594998279091301)
                ·
                  refine ⟨2858720702361562177329619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15246510412594998279091301 2858720702361562177329619)
                  ·
                    refine ⟨4288081053542343265994429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2858720702361562177329619 4288081053542343265994429)
                    ·
                      refine ⟨1608030395078378724747911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4288081053542343265994429 1608030395078378724747911)
                      ·
                        rfl

theorem cell23_3131628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_3131628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131628 prefixEnd_3131628 := by exact prefixLift 3131628
  have htrace : WordTrace (prefixWord ++ tailWord_3131628) baseStart_3131628 baseEnd_3131628 := by
    simpa [prefixWord, tailWord_3131628, baseEnd_3131628] using wordTrace_append hprefix tailTrace_3131628
  have hstable : (prefixWord ++ tailWord_3131628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131628).length < 2 ^ (prefixWord ++ tailWord_3131628).sum := by decide
  have hdescent : baseEnd_3131628 < baseStart_3131628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131671 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3131671 : Nat := 118140960795 + 3131671 * 2 ^ 59
def prefixEnd_3131671 : Nat := 4983230072969 + 3 ^ 40 * 3131671 * 2
def baseEnd_3131671 : Nat := 1608052474746522056510213

theorem tailTrace_3131671 : CollatzResearch.WordTrace tailWord_3131671 prefixEnd_3131671 1608052474746522056510213 := by
  unfold tailWord_3131671
  simp only [CollatzResearch.WordTrace]
  refine ⟨114221425037498288670578867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76147616691665525780385911 114221425037498288670578867)
  ·
    refine ⟨171332137556247433005868301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114221425037498288670578867 171332137556247433005868301)
    ·
      refine ⟨64249551583592787377200613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171332137556247433005868301 64249551583592787377200613)
      ·
        refine ⟨12046790921923647633225115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64249551583592787377200613 12046790921923647633225115)
        ·
          refine ⟨18070186382885471449837673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12046790921923647633225115 18070186382885471449837673)
          ·
            refine ⟨13552639787164103587378255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18070186382885471449837673 13552639787164103587378255)
            ·
              refine ⟨20328959680746155381067383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13552639787164103587378255 20328959680746155381067383)
              ·
                refine ⟨30493439521119233071601075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20328959680746155381067383 30493439521119233071601075)
                ·
                  refine ⟨45740159281678849607401613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30493439521119233071601075 45740159281678849607401613)
                  ·
                    refine ⟨17152559730629568602775605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45740159281678849607401613 17152559730629568602775605)
                    ·
                      refine ⟨1608052474746522056510213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17152559730629568602775605 1608052474746522056510213)
                      ·
                        rfl

theorem cell23_3131671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3131671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131671 prefixEnd_3131671 := by exact prefixLift 3131671
  have htrace : WordTrace (prefixWord ++ tailWord_3131671) baseStart_3131671 baseEnd_3131671 := by
    simpa [prefixWord, tailWord_3131671, baseEnd_3131671] using wordTrace_append hprefix tailTrace_3131671
  have hstable : (prefixWord ++ tailWord_3131671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131671).length < 2 ^ (prefixWord ++ tailWord_3131671).sum := by decide
  have hdescent : baseEnd_3131671 < baseStart_3131671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131681 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3131681 : Nat := 118140960795 + 3131681 * 2 ^ 59
def prefixEnd_3131681 : Nat := 4983230072969 + 3 ^ 40 * 3131681 * 2
def baseEnd_3131681 : Nat := 1608057609553067017385167

theorem tailTrace_3131681 : CollatzResearch.WordTrace tailWord_3131681 prefixEnd_3131681 1608057609553067017385167 := by
  unfold tailWord_3131681
  simp only [CollatzResearch.WordTrace]
  refine ⟨114221789767462060378442897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76147859844974706918961931 114221789767462060378442897)
  ·
    refine ⟨85666342325596545283832173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114221789767462060378442897 85666342325596545283832173)
    ·
      refine ⟨32124878372098704481437065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85666342325596545283832173 32124878372098704481437065)
      ·
        refine ⟨24093658779074028361077799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32124878372098704481437065 24093658779074028361077799)
        ·
          refine ⟨36140488168611042541616699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24093658779074028361077799 36140488168611042541616699)
          ·
            refine ⟨54210732252916563812425049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36140488168611042541616699 54210732252916563812425049)
            ·
              refine ⟨40658049189687422859318787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54210732252916563812425049 40658049189687422859318787)
              ·
                refine ⟨60987073784531134288978181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40658049189687422859318787 60987073784531134288978181)
                ·
                  refine ⟨11435076334599587679183409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60987073784531134288978181 11435076334599587679183409)
                  ·
                    refine ⟨8576307250949690759387557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11435076334599587679183409 8576307250949690759387557)
                    ·
                      refine ⟨1608057609553067017385167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8576307250949690759387557 1608057609553067017385167)
                      ·
                        rfl

theorem cell23_3131681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3131681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131681 prefixEnd_3131681 := by exact prefixLift 3131681
  have htrace : WordTrace (prefixWord ++ tailWord_3131681) baseStart_3131681 baseEnd_3131681 := by
    simpa [prefixWord, tailWord_3131681, baseEnd_3131681] using wordTrace_append hprefix tailTrace_3131681
  have hstable : (prefixWord ++ tailWord_3131681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131681).length < 2 ^ (prefixWord ++ tailWord_3131681).sum := by decide
  have hdescent : baseEnd_3131681 < baseStart_3131681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131781 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 8]
def baseStart_3131781 : Nat := 118140960795 + 3131781 * 2 ^ 59
def prefixEnd_3131781 : Nat := 4983230072969 + 3 ^ 40 * 3131781 * 2
def baseEnd_3131781 : Nat := 178678773068724069570523

theorem tailTrace_3131781 : CollatzResearch.WordTrace tailWord_3131781 prefixEnd_3131781 178678773068724069570523 := by
  unfold tailWord_3131781
  simp only [CollatzResearch.WordTrace]
  refine ⟨114225437067099777457083197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76150291378066518304722131 114225437067099777457083197)
  ·
    refine ⟨42834538900162416546406199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114225437067099777457083197 42834538900162416546406199)
    ·
      refine ⟨64251808350243624819609299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42834538900162416546406199 64251808350243624819609299)
      ·
        refine ⟨96377712525365437229413949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64251808350243624819609299 96377712525365437229413949)
        ·
          refine ⟨36141642197012038961030231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96377712525365437229413949 36141642197012038961030231)
          ·
            refine ⟨54212463295518058441545347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36141642197012038961030231 54212463295518058441545347)
            ·
              refine ⟨81318694943277087662318021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54212463295518058441545347 81318694943277087662318021)
              ·
                refine ⟨15247255301864453936684629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81318694943277087662318021 15247255301864453936684629)
                ·
                  refine ⟨178678773068724069570523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15247255301864453936684629 178678773068724069570523)
                  ·
                    rfl

theorem cell23_3131781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_3131781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131781 prefixEnd_3131781 := by exact prefixLift 3131781
  have htrace : WordTrace (prefixWord ++ tailWord_3131781) baseStart_3131781 baseEnd_3131781 := by
    simpa [prefixWord, tailWord_3131781, baseEnd_3131781] using wordTrace_append hprefix tailTrace_3131781
  have hstable : (prefixWord ++ tailWord_3131781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131781).length < 2 ^ (prefixWord ++ tailWord_3131781).sum := by decide
  have hdescent : baseEnd_3131781 < baseStart_3131781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131801 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_3131801 : Nat := 118140960795 + 3131801 * 2 ^ 59
def prefixEnd_3131801 : Nat := 4983230072969 + 3 ^ 40 * 3131801 * 2
def baseEnd_3131801 : Nat := 1608119227231606547884615

theorem tailTrace_3131801 : CollatzResearch.WordTrace tailWord_3131801 prefixEnd_3131801 1608119227231606547884615 := by
  unfold tailWord_3131801
  simp only [CollatzResearch.WordTrace]
  refine ⟨114226166527027320872811257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76150777684684880581874171 114226166527027320872811257)
  ·
    refine ⟨85669624895270490654608443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114226166527027320872811257 85669624895270490654608443)
    ·
      refine ⟨128504437342905735981912665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85669624895270490654608443 128504437342905735981912665)
      ·
        refine ⟨96378328007179301986434499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128504437342905735981912665 96378328007179301986434499)
        ·
          refine ⟨144567492010768952979651749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96378328007179301986434499 144567492010768952979651749)
          ·
            refine ⟨27106404752019178683684703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144567492010768952979651749 27106404752019178683684703)
            ·
              refine ⟨40659607128028768025527055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27106404752019178683684703 40659607128028768025527055)
              ·
                refine ⟨60989410692043152038290583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40659607128028768025527055 60989410692043152038290583)
                ·
                  refine ⟨91484116038064728057435875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60989410692043152038290583 91484116038064728057435875)
                  ·
                    refine ⟨137226174057097092086153813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91484116038064728057435875 137226174057097092086153813)
                    ·
                      refine ⟨1608119227231606547884615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 137226174057097092086153813 1608119227231606547884615)
                      ·
                        rfl

theorem cell23_3131801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_3131801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131801 prefixEnd_3131801 := by exact prefixLift 3131801
  have htrace : WordTrace (prefixWord ++ tailWord_3131801) baseStart_3131801 baseEnd_3131801 := by
    simpa [prefixWord, tailWord_3131801, baseEnd_3131801] using wordTrace_append hprefix tailTrace_3131801
  have hstable : (prefixWord ++ tailWord_3131801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131801).length < 2 ^ (prefixWord ++ tailWord_3131801).sum := by decide
  have hdescent : baseEnd_3131801 < baseStart_3131801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131802 : List Nat := [3, 1, 1, 4, 1, 2, 2, 4, 1, 4]
def baseStart_3131802 : Nat := 118140960795 + 3131802 * 2 ^ 59
def prefixEnd_3131802 : Nat := 4983230072969 + 3 ^ 40 * 3131802 * 2
def baseEnd_3131802 : Nat := 536039913570753681324037

theorem tailTrace_3131802 : CollatzResearch.WordTrace tailWord_3131802 prefixEnd_3131802 536039913570753681324037 := by
  unfold tailWord_3131802
  simp only [CollatzResearch.WordTrace]
  refine ⟨28556550750005924510899415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76150802000015798695731773 28556550750005924510899415)
  ·
    refine ⟨42834826125008886766349123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28556550750005924510899415 42834826125008886766349123)
    ·
      refine ⟨64252239187513330149523685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42834826125008886766349123 64252239187513330149523685)
      ·
        refine ⟨12047294847658749403035691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64252239187513330149523685 12047294847658749403035691)
        ·
          refine ⟨18070942271488124104553537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12047294847658749403035691 18070942271488124104553537)
          ·
            refine ⟨13553206703616093078415153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18070942271488124104553537 13553206703616093078415153)
            ·
              refine ⟨10164905027712069808811365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13553206703616093078415153 10164905027712069808811365)
              ·
                refine ⟨1905919692696013089152131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10164905027712069808811365 1905919692696013089152131)
                ·
                  refine ⟨2858879539044019633728197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905919692696013089152131 2858879539044019633728197)
                  ·
                    refine ⟨536039913570753681324037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2858879539044019633728197 536039913570753681324037)
                    ·
                      rfl

theorem cell23_3131802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_3131802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131802 prefixEnd_3131802 := by exact prefixLift 3131802
  have htrace : WordTrace (prefixWord ++ tailWord_3131802) baseStart_3131802 baseEnd_3131802 := by
    simpa [prefixWord, tailWord_3131802, baseEnd_3131802] using wordTrace_append hprefix tailTrace_3131802
  have hstable : (prefixWord ++ tailWord_3131802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131802).length < 2 ^ (prefixWord ++ tailWord_3131802).sum := by decide
  have hdescent : baseEnd_3131802 < baseStart_3131802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131882 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_3131882 : Nat := 118140960795 + 3131882 * 2 ^ 59
def prefixEnd_3131882 : Nat := 4983230072969 + 3 ^ 40 * 3131882 * 2
def baseEnd_3131882 : Nat := 1608160819164620730971743

theorem tailTrace_3131882 : CollatzResearch.WordTrace tailWord_3131882 prefixEnd_3131882 1608160819164620730971743 := by
  unfold tailWord_3131882
  simp only [CollatzResearch.WordTrace]
  refine ⟨28557280209933467926627475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76152747226489247804339933 28557280209933467926627475)
  ·
    refine ⟨42835920314900201889941213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28557280209933467926627475 42835920314900201889941213)
    ·
      refine ⟨16063470118087575708727955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42835920314900201889941213 16063470118087575708727955)
      ·
        refine ⟨24095205177131363563091933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16063470118087575708727955 24095205177131363563091933)
        ·
          refine ⟨9035701941424261336159475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24095205177131363563091933 9035701941424261336159475)
          ·
            refine ⟨13553552912136392004239213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9035701941424261336159475 13553552912136392004239213)
            ·
              refine ⟨5082582342051147001589705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13553552912136392004239213 5082582342051147001589705)
              ·
                refine ⟨3811936756538360251192279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5082582342051147001589705 3811936756538360251192279)
                ·
                  refine ⟨5717905134807540376788419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811936756538360251192279 5717905134807540376788419)
                  ·
                    refine ⟨8576857702211310565182629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5717905134807540376788419 8576857702211310565182629)
                    ·
                      refine ⟨1608160819164620730971743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8576857702211310565182629 1608160819164620730971743)
                      ·
                        rfl

theorem cell23_3131882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_3131882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131882 prefixEnd_3131882 := by exact prefixLift 3131882
  have htrace : WordTrace (prefixWord ++ tailWord_3131882) baseStart_3131882 baseEnd_3131882 := by
    simpa [prefixWord, tailWord_3131882, baseEnd_3131882] using wordTrace_append hprefix tailTrace_3131882
  have hstable : (prefixWord ++ tailWord_3131882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131882).length < 2 ^ (prefixWord ++ tailWord_3131882).sum := by decide
  have hdescent : baseEnd_3131882 < baseStart_3131882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131910 : List Nat := [6, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_3131910 : Nat := 118140960795 + 3131910 * 2 ^ 59
def prefixEnd_3131910 : Nat := 4983230072969 + 3 ^ 40 * 3131910 * 2
def baseEnd_3131910 : Nat := 1608175196622946621421615

theorem tailTrace_3131910 : CollatzResearch.WordTrace tailWord_3131910 prefixEnd_3131910 1608175196622946621421615 := by
  unfold tailWord_3131910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3569691940113513515266537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76153428055754954992352789 3569691940113513515266537)
  ·
    refine ⟨2677268955085135136449903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3569691940113513515266537 2677268955085135136449903)
    ·
      refine ⟨4015903432627702704674855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2677268955085135136449903 4015903432627702704674855)
      ·
        refine ⟨6023855148941554057012283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4015903432627702704674855 6023855148941554057012283)
        ·
          refine ⟨9035782723412331085518425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6023855148941554057012283 9035782723412331085518425)
          ·
            refine ⟨6776837042559248314138819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9035782723412331085518425 6776837042559248314138819)
            ·
              refine ⟨10165255563838872471208229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776837042559248314138819 10165255563838872471208229)
              ·
                refine ⟨1905985418219788588351543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10165255563838872471208229 1905985418219788588351543)
                ·
                  refine ⟨2858978127329682882527315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905985418219788588351543 2858978127329682882527315)
                  ·
                    refine ⟨4288467190994524323790973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2858978127329682882527315 4288467190994524323790973)
                    ·
                      refine ⟨1608175196622946621421615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4288467190994524323790973 1608175196622946621421615)
                      ·
                        rfl

theorem cell23_3131910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_3131910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131910 prefixEnd_3131910 := by exact prefixLift 3131910
  have htrace : WordTrace (prefixWord ++ tailWord_3131910) baseStart_3131910 baseEnd_3131910 := by
    simpa [prefixWord, tailWord_3131910, baseEnd_3131910] using wordTrace_append hprefix tailTrace_3131910
  have hstable : (prefixWord ++ tailWord_3131910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131910).length < 2 ^ (prefixWord ++ tailWord_3131910).sum := by decide
  have hdescent : baseEnd_3131910 < baseStart_3131910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131916 : List Nat := [2, 2, 1, 2, 4, 2, 1, 4, 1, 2, 2]
def baseStart_3131916 : Nat := 118140960795 + 3131916 * 2 ^ 59
def prefixEnd_3131916 : Nat := 4983230072969 + 3 ^ 40 * 3131916 * 2
def baseEnd_3131916 : Nat := 1608178277506873597946587

theorem tailTrace_3131916 : CollatzResearch.WordTrace tailWord_3131916 prefixEnd_3131916 1608178277506873597946587 := by
  unfold tailWord_3131916
  simp only [CollatzResearch.WordTrace]
  refine ⟨57115180460805347756623801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76153573947740463675498401 57115180460805347756623801)
  ·
    refine ⟨42836385345604010817467851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57115180460805347756623801 42836385345604010817467851)
    ·
      refine ⟨64254578018406016226201777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42836385345604010817467851 64254578018406016226201777)
      ·
        refine ⟨48190933513804512169651333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64254578018406016226201777 48190933513804512169651333)
        ·
          refine ⟨9035800033838346031809625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48190933513804512169651333 9035800033838346031809625)
          ·
            refine ⟨6776850025378759523857219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9035800033838346031809625 6776850025378759523857219)
            ·
              refine ⟨10165275038068139285785829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776850025378759523857219 10165275038068139285785829)
              ·
                refine ⟨1905989069637776116084843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10165275038068139285785829 1905989069637776116084843)
                ·
                  refine ⟨2858983604456664174127265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905989069637776116084843 2858983604456664174127265)
                  ·
                    refine ⟨2144237703342498130595449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2858983604456664174127265 2144237703342498130595449)
                    ·
                      refine ⟨1608178277506873597946587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2144237703342498130595449 1608178277506873597946587)
                      ·
                        rfl

theorem cell23_3131916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_3131916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131916 prefixEnd_3131916 := by exact prefixLift 3131916
  have htrace : WordTrace (prefixWord ++ tailWord_3131916) baseStart_3131916 baseEnd_3131916 := by
    simpa [prefixWord, tailWord_3131916, baseEnd_3131916] using wordTrace_append hprefix tailTrace_3131916
  have hstable : (prefixWord ++ tailWord_3131916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131916).length < 2 ^ (prefixWord ++ tailWord_3131916).sum := by decide
  have hdescent : baseEnd_3131916 < baseStart_3131916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131932 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_3131932 : Nat := 118140960795 + 3131932 * 2 ^ 59
def prefixEnd_3131932 : Nat := 4983230072969 + 3 ^ 40 * 3131932 * 2
def baseEnd_3131932 : Nat := 1608186493197345535346513

theorem tailTrace_3131932 : CollatzResearch.WordTrace tailWord_3131932 prefixEnd_3131932 1608186493197345535346513 := by
  unfold tailWord_3131932
  simp only [CollatzResearch.WordTrace]
  refine ⟨57115472244776365122915025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76153962993035153497220033 57115472244776365122915025)
  ·
    refine ⟨42836604183582273842186269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57115472244776365122915025 42836604183582273842186269)
    ·
      refine ⟨16063726568843352690819851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42836604183582273842186269 16063726568843352690819851)
      ·
        refine ⟨24095589853265029036229777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16063726568843352690819851 24095589853265029036229777)
        ·
          refine ⟨18071692389948771777172333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24095589853265029036229777 18071692389948771777172333)
          ·
            refine ⟨6776884646230789416439625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18071692389948771777172333 6776884646230789416439625)
            ·
              refine ⟨5082663484673092062329719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6776884646230789416439625 5082663484673092062329719)
              ·
                refine ⟨7623995227009638093494579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5082663484673092062329719 7623995227009638093494579)
                ·
                  refine ⟨11435992840514457140241869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7623995227009638093494579 11435992840514457140241869)
                  ·
                    refine ⟨4288497315192921427590701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11435992840514457140241869 4288497315192921427590701)
                    ·
                      refine ⟨1608186493197345535346513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4288497315192921427590701 1608186493197345535346513)
                      ·
                        rfl

theorem cell23_3131932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_3131932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131932 prefixEnd_3131932 := by exact prefixLift 3131932
  have htrace : WordTrace (prefixWord ++ tailWord_3131932) baseStart_3131932 baseEnd_3131932 := by
    simpa [prefixWord, tailWord_3131932, baseEnd_3131932] using wordTrace_append hprefix tailTrace_3131932
  have hstable : (prefixWord ++ tailWord_3131932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131932).length < 2 ^ (prefixWord ++ tailWord_3131932).sum := by decide
  have hdescent : baseEnd_3131932 < baseStart_3131932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131965 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_3131965 : Nat := 118140960795 + 3131965 * 2 ^ 59
def prefixEnd_3131965 : Nat := 4983230072969 + 3 ^ 40 * 3131965 * 2
def baseEnd_3131965 : Nat := 536067812686314635411287

theorem tailTrace_3131965 : CollatzResearch.WordTrace tailWord_3131965 prefixEnd_3131965 536067812686314635411287 := by
  unfold tailWord_3131965
  simp only [CollatzResearch.WordTrace]
  refine ⟨114232148098433176881781349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76154765398955451254520899 114232148098433176881781349)
  ·
    refine ⟨21418527768456220665334003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114232148098433176881781349 21418527768456220665334003)
    ·
      refine ⟨32127791652684330998001005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21418527768456220665334003 32127791652684330998001005)
      ·
        refine ⟨12047921869756624124250377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32127791652684330998001005 12047921869756624124250377)
        ·
          refine ⟨9035941402317468093187783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12047921869756624124250377 9035941402317468093187783)
          ·
            refine ⟨13553912103476202139781675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9035941402317468093187783 13553912103476202139781675)
            ·
              refine ⟨20330868155214303209672513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13553912103476202139781675 20330868155214303209672513)
              ·
                refine ⟨15248151116410727407254385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20330868155214303209672513 15248151116410727407254385)
                ·
                  refine ⟨11436113337308045555440789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15248151116410727407254385 11436113337308045555440789)
                  ·
                    refine ⟨536067812686314635411287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11436113337308045555440789 536067812686314635411287)
                    ·
                      rfl

theorem cell23_3131965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_3131965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131965 prefixEnd_3131965 := by exact prefixLift 3131965
  have htrace : WordTrace (prefixWord ++ tailWord_3131965) baseStart_3131965 baseEnd_3131965 := by
    simpa [prefixWord, tailWord_3131965, baseEnd_3131965] using wordTrace_append hprefix tailTrace_3131965
  have hstable : (prefixWord ++ tailWord_3131965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131965).length < 2 ^ (prefixWord ++ tailWord_3131965).sum := by decide
  have hdescent : baseEnd_3131965 < baseStart_3131965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131966 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3131966 : Nat := 118140960795 + 3131966 * 2 ^ 59
def prefixEnd_3131966 : Nat := 4983230072969 + 3 ^ 40 * 3131966 * 2
def baseEnd_3131966 : Nat := 1608203951539598402321357

theorem tailTrace_3131966 : CollatzResearch.WordTrace tailWord_3131966 prefixEnd_3131966 1608203951539598402321357 := by
  unfold tailWord_3131966
  simp only [CollatzResearch.WordTrace]
  refine ⟨14279023071428694256570969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76154789714286369368378501 14279023071428694256570969)
  ·
    refine ⟨10709267303571520692428227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14279023071428694256570969 10709267303571520692428227)
    ·
      refine ⟨16063900955357281038642341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10709267303571520692428227 16063900955357281038642341)
      ·
        refine ⟨3011981429129490194745439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16063900955357281038642341 3011981429129490194745439)
        ·
          refine ⟨4517972143694235292118159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011981429129490194745439 4517972143694235292118159)
          ·
            refine ⟨6776958215541352938177239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517972143694235292118159 6776958215541352938177239)
            ·
              refine ⟨10165437323312029407265859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776958215541352938177239 10165437323312029407265859)
              ·
                refine ⟨15248155984968044110898789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10165437323312029407265859 15248155984968044110898789)
                ·
                  refine ⟨2859029247181508270793523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15248155984968044110898789 2859029247181508270793523)
                  ·
                    refine ⟨4288543870772262406190285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2859029247181508270793523 4288543870772262406190285)
                    ·
                      refine ⟨1608203951539598402321357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4288543870772262406190285 1608203951539598402321357)
                      ·
                        rfl

theorem cell23_3131966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3131966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131966 prefixEnd_3131966 := by exact prefixLift 3131966
  have htrace : WordTrace (prefixWord ++ tailWord_3131966) baseStart_3131966 baseEnd_3131966 := by
    simpa [prefixWord, tailWord_3131966, baseEnd_3131966] using wordTrace_append hprefix tailTrace_3131966
  have hstable : (prefixWord ++ tailWord_3131966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131966).length < 2 ^ (prefixWord ++ tailWord_3131966).sum := by decide
  have hdescent : baseEnd_3131966 < baseStart_3131966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131985 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_3131985 : Nat := 118140960795 + 3131985 * 2 ^ 59
def prefixEnd_3131985 : Nat := 4983230072969 + 3 ^ 40 * 3131985 * 2
def baseEnd_3131985 : Nat := 1608213707672033827983769

theorem tailTrace_3131985 : CollatzResearch.WordTrace tailWord_3131985 prefixEnd_3131985 1608213707672033827983769 := by
  unfold tailWord_3131985
  simp only [CollatzResearch.WordTrace]
  refine ⟨114232877558360720297509409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76155251705573813531672939 114232877558360720297509409)
  ·
    refine ⟨85674658168770540223132057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114232877558360720297509409 85674658168770540223132057)
    ·
      refine ⟨64255993626577905167349043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85674658168770540223132057 64255993626577905167349043)
      ·
        refine ⟨96383990439866857751023565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64255993626577905167349043 96383990439866857751023565)
        ·
          refine ⟨36143996414950071656633837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96383990439866857751023565 36143996414950071656633837)
          ·
            refine ⟨13553998655606276871237689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36143996414950071656633837 13553998655606276871237689)
            ·
              refine ⟨10165498991704707653428267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13553998655606276871237689 10165498991704707653428267)
              ·
                refine ⟨15248248487557061480142401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10165498991704707653428267 15248248487557061480142401)
                ·
                  refine ⟨11436186365667796110106801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15248248487557061480142401 11436186365667796110106801)
                  ·
                    refine ⟨8577139774250847082580101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11436186365667796110106801 8577139774250847082580101)
                    ·
                      refine ⟨1608213707672033827983769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8577139774250847082580101 1608213707672033827983769)
                      ·
                        rfl

theorem cell23_3131985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_3131985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131985 prefixEnd_3131985 := by exact prefixLift 3131985
  have htrace : WordTrace (prefixWord ++ tailWord_3131985) baseStart_3131985 baseEnd_3131985 := by
    simpa [prefixWord, tailWord_3131985, baseEnd_3131985] using wordTrace_append hprefix tailTrace_3131985
  have hstable : (prefixWord ++ tailWord_3131985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131985).length < 2 ^ (prefixWord ++ tailWord_3131985).sum := by decide
  have hdescent : baseEnd_3131985 < baseStart_3131985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3131989 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 2, 2, 2]
def baseStart_3131989 : Nat := 118140960795 + 3131989 * 2 ^ 59
def prefixEnd_3131989 : Nat := 4983230072969 + 3 ^ 40 * 3131989 * 2
def baseEnd_3131989 : Nat := 1608215761594651812333751

theorem tailTrace_3131989 : CollatzResearch.WordTrace tailWord_3131989 prefixEnd_3131989 1608215761594651812333751 := by
  unfold tailWord_3131989
  simp only [CollatzResearch.WordTrace]
  refine ⟨114233023450346228980655021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76155348966897485987103347 114233023450346228980655021)
  ·
    refine ⟨42837383793879835867745633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114233023450346228980655021 42837383793879835867745633)
    ·
      refine ⟨32128037845409876900809225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42837383793879835867745633 32128037845409876900809225)
      ·
        refine ⟨24096028384057407675606919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32128037845409876900809225 24096028384057407675606919)
        ·
          refine ⟨36144042576086111513410379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24096028384057407675606919 36144042576086111513410379)
          ·
            refine ⟨54216063864129167270115569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36144042576086111513410379 54216063864129167270115569)
            ·
              refine ⟨40662047898096875452586677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54216063864129167270115569 40662047898096875452586677)
              ·
                refine ⟨3812066990446582073680001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40662047898096875452586677 3812066990446582073680001)
                ·
                  refine ⟨2859050242834936555260001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3812066990446582073680001 2859050242834936555260001)
                  ·
                    refine ⟨2144287682126202416445001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2859050242834936555260001 2144287682126202416445001)
                    ·
                      refine ⟨1608215761594651812333751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2144287682126202416445001 1608215761594651812333751)
                      ·
                        rfl

theorem cell23_3131989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_3131989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3131989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3131989 prefixEnd_3131989 := by exact prefixLift 3131989
  have htrace : WordTrace (prefixWord ++ tailWord_3131989) baseStart_3131989 baseEnd_3131989 := by
    simpa [prefixWord, tailWord_3131989, baseEnd_3131989] using wordTrace_append hprefix tailTrace_3131989
  have hstable : (prefixWord ++ tailWord_3131989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3131989).length < 2 ^ (prefixWord ++ tailWord_3131989).sum := by decide
  have hdescent : baseEnd_3131989 < baseStart_3131989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3131989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132012 : List Nat := [2, 2, 1, 1, 3, 1, 5, 3, 5]
def baseStart_3132012 : Nat := 118140960795 + 3132012 * 2 ^ 59
def prefixEnd_3132012 : Nat := 4983230072969 + 3 ^ 40 * 3132012 * 2
def baseEnd_3132012 : Nat := 178691952405522802482905

theorem tailTrace_3132012 : CollatzResearch.WordTrace tailWord_3132012 prefixEnd_3132012 178691952405522802482905 := by
  unfold tailWord_3132012
  simp only [CollatzResearch.WordTrace]
  refine ⟨57116931164631451954371145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76155908219508602605828193 57116931164631451954371145)
  ·
    refine ⟨42837698373473588965778359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57116931164631451954371145 42837698373473588965778359)
    ·
      refine ⟨64256547560210383448667539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42837698373473588965778359 64256547560210383448667539)
      ·
        refine ⟨96384821340315575173001309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64256547560210383448667539 96384821340315575173001309)
        ·
          refine ⟨36144308002618340689875491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96384821340315575173001309 36144308002618340689875491)
          ·
            refine ⟨54216462003927511034813237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36144308002618340689875491 54216462003927511034813237)
            ·
              refine ⟨5082793312868204159513741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54216462003927511034813237 5082793312868204159513741)
              ·
                refine ⟨1906047492325576559817653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5082793312868204159513741 1906047492325576559817653)
                ·
                  refine ⟨178691952405522802482905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1906047492325576559817653 178691952405522802482905)
                  ·
                    rfl

theorem cell23_3132012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_3132012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132012 prefixEnd_3132012 := by exact prefixLift 3132012
  have htrace : WordTrace (prefixWord ++ tailWord_3132012) baseStart_3132012 baseEnd_3132012 := by
    simpa [prefixWord, tailWord_3132012, baseEnd_3132012] using wordTrace_append hprefix tailTrace_3132012
  have hstable : (prefixWord ++ tailWord_3132012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132012).length < 2 ^ (prefixWord ++ tailWord_3132012).sum := by decide
  have hdescent : baseEnd_3132012 < baseStart_3132012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132025 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 4, 5]
def baseStart_3132025 : Nat := 118140960795 + 3132025 * 2 ^ 59
def prefixEnd_3132025 : Nat := 4983230072969 + 3 ^ 40 * 3132025 * 2
def baseEnd_3132025 : Nat := 536078082299404557161195

theorem tailTrace_3132025 : CollatzResearch.WordTrace tailWord_3132025 prefixEnd_3132025 536078082299404557161195 := by
  unfold tailWord_3132025
  simp only [CollatzResearch.WordTrace]
  refine ⟨114234336478215807128965529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76156224318810538085977019 114234336478215807128965529)
  ·
    refine ⟨85675752358661855346724147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114234336478215807128965529 85675752358661855346724147)
    ·
      refine ⟨128513628537992783020086221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85675752358661855346724147 128513628537992783020086221)
      ·
        refine ⟨48192610701747293632532333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128513628537992783020086221 48192610701747293632532333)
        ·
          refine ⟨18072229013155235112199625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48192610701747293632532333 18072229013155235112199625)
          ·
            refine ⟨13554171759866426334149719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18072229013155235112199625 13554171759866426334149719)
            ·
              refine ⟨20331257639799639501224579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13554171759866426334149719 20331257639799639501224579)
              ·
                refine ⟨30496886459699459251836869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20331257639799639501224579 30496886459699459251836869)
                ·
                  refine ⟨5718166211193648609719413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30496886459699459251836869 5718166211193648609719413)
                  ·
                    refine ⟨536078082299404557161195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5718166211193648609719413 536078082299404557161195)
                    ·
                      rfl

theorem cell23_3132025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_3132025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132025 prefixEnd_3132025 := by exact prefixLift 3132025
  have htrace : WordTrace (prefixWord ++ tailWord_3132025) baseStart_3132025 baseEnd_3132025 := by
    simpa [prefixWord, tailWord_3132025, baseEnd_3132025] using wordTrace_append hprefix tailTrace_3132025
  have hstable : (prefixWord ++ tailWord_3132025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132025).length < 2 ^ (prefixWord ++ tailWord_3132025).sum := by decide
  have hdescent : baseEnd_3132025 < baseStart_3132025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132029 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 7]
def baseStart_3132029 : Nat := 118140960795 + 3132029 * 2 ^ 59
def prefixEnd_3132029 : Nat := 4983230072969 + 3 ^ 40 * 3132029 * 2
def baseEnd_3132029 : Nat := 178692922313425739537063

theorem tailTrace_3132029 : CollatzResearch.WordTrace tailWord_3132029 prefixEnd_3132029 178692922313425739537063 := by
  unfold tailWord_3132029
  simp only [CollatzResearch.WordTrace]
  refine ⟨114234482370201315812111141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76156321580134210541407427 114234482370201315812111141)
  ·
    refine ⟨21418965444412746714770839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114234482370201315812111141 21418965444412746714770839)
    ·
      refine ⟨32128448166619120072156259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21418965444412746714770839 32128448166619120072156259)
      ·
        refine ⟨48192672249928680108234389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32128448166619120072156259 48192672249928680108234389)
        ·
          refine ⟨2259031511715406880073487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48192672249928680108234389 2259031511715406880073487)
          ·
            refine ⟨3388547267573110320110231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259031511715406880073487 3388547267573110320110231)
            ·
              refine ⟨5082820901359665480165347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3388547267573110320110231 5082820901359665480165347)
              ·
                refine ⟨7624231352039498220248021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5082820901359665480165347 7624231352039498220248021)
                ·
                  refine ⟨178692922313425739537063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7624231352039498220248021 178692922313425739537063)
                  ·
                    rfl

theorem cell23_3132029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_3132029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132029 prefixEnd_3132029 := by exact prefixLift 3132029
  have htrace : WordTrace (prefixWord ++ tailWord_3132029) baseStart_3132029 baseEnd_3132029 := by
    simpa [prefixWord, tailWord_3132029, baseEnd_3132029] using wordTrace_append hprefix tailTrace_3132029
  have hstable : (prefixWord ++ tailWord_3132029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132029).length < 2 ^ (prefixWord ++ tailWord_3132029).sum := by decide
  have hdescent : baseEnd_3132029 < baseStart_3132029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132034 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3132034 : Nat := 118140960795 + 3132034 * 2 ^ 59
def prefixEnd_3132034 : Nat := 4983230072969 + 3 ^ 40 * 3132034 * 2
def baseEnd_3132034 : Nat := 1608238868224104136271045

theorem tailTrace_3132034 : CollatzResearch.WordTrace tailWord_3132034 prefixEnd_3132034 1608238868224104136271045 := by
  unfold tailWord_3132034
  simp only [CollatzResearch.WordTrace]
  refine ⟨28558666183795800416510789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76156443156788801110695437 28558666183795800416510789)
  ·
    refine ⟨5354749909461712578095773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28558666183795800416510789 5354749909461712578095773)
    ·
      refine ⟨2008031216048142216785915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5354749909461712578095773 2008031216048142216785915)
      ·
        refine ⟨3012046824072213325178873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008031216048142216785915 3012046824072213325178873)
        ·
          refine ⟨2259035118054159993884155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3012046824072213325178873 2259035118054159993884155)
          ·
            refine ⟨3388552677081239990826233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259035118054159993884155 3388552677081239990826233)
            ·
              refine ⟨2541414507810929993119675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3388552677081239990826233 2541414507810929993119675)
              ·
                refine ⟨3812121761716394989679513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541414507810929993119675 3812121761716394989679513)
                ·
                  refine ⟨2859091321287296242259635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3812121761716394989679513 2859091321287296242259635)
                  ·
                    refine ⟨4288636981930944363389453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2859091321287296242259635 4288636981930944363389453)
                    ·
                      refine ⟨1608238868224104136271045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4288636981930944363389453 1608238868224104136271045)
                      ·
                        rfl

theorem cell23_3132034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3132034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132034 prefixEnd_3132034 := by exact prefixLift 3132034
  have htrace : WordTrace (prefixWord ++ tailWord_3132034) baseStart_3132034 baseEnd_3132034 := by
    simpa [prefixWord, tailWord_3132034, baseEnd_3132034] using wordTrace_append hprefix tailTrace_3132034
  have hstable : (prefixWord ++ tailWord_3132034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132034).length < 2 ^ (prefixWord ++ tailWord_3132034).sum := by decide
  have hdescent : baseEnd_3132034 < baseStart_3132034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132136 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 6]
def baseStart_3132136 : Nat := 118140960795 + 3132136 * 2 ^ 59
def prefixEnd_3132136 : Nat := 4983230072969 + 3 ^ 40 * 3132136 * 2
def baseEnd_3132136 : Nat := 178699027027873637466175

theorem tailTrace_3132136 : CollatzResearch.WordTrace tailWord_3132136 prefixEnd_3132136 178699027027873637466175 := by
  unfold tailWord_3132136
  simp only [CollatzResearch.WordTrace]
  refine ⟨57119192490406836543128131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76158923320542448724170841 57119192490406836543128131)
  ·
    refine ⟨85678788735610254814692197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57119192490406836543128131 85678788735610254814692197)
    ·
      refine ⟨16064772887926922777754787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85678788735610254814692197 16064772887926922777754787)
      ·
        refine ⟨24097159331890384166632181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16064772887926922777754787 24097159331890384166632181)
        ·
          refine ⟨2259108687364723515621767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24097159331890384166632181 2259108687364723515621767)
          ·
            refine ⟨3388663031047085273432651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259108687364723515621767 3388663031047085273432651)
            ·
              refine ⟨5082994546570627910148977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3388663031047085273432651 5082994546570627910148977)
              ·
                refine ⟨3812245909927970932611733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5082994546570627910148977 3812245909927970932611733)
                ·
                  refine ⟨178699027027873637466175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3812245909927970932611733 178699027027873637466175)
                  ·
                    rfl

theorem cell23_3132136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 6].length) (baseStart_3132136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132136 prefixEnd_3132136 := by exact prefixLift 3132136
  have htrace : WordTrace (prefixWord ++ tailWord_3132136) baseStart_3132136 baseEnd_3132136 := by
    simpa [prefixWord, tailWord_3132136, baseEnd_3132136] using wordTrace_append hprefix tailTrace_3132136
  have hstable : (prefixWord ++ tailWord_3132136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132136).length < 2 ^ (prefixWord ++ tailWord_3132136).sum := by decide
  have hdescent : baseEnd_3132136 < baseStart_3132136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132146 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3132146 : Nat := 118140960795 + 3132146 * 2 ^ 59
def prefixEnd_3132146 : Nat := 4983230072969 + 3 ^ 40 * 3132146 * 2
def baseEnd_3132146 : Nat := 1608296378057407698070529

theorem tailTrace_3132146 : CollatzResearch.WordTrace tailWord_3132146 prefixEnd_3132146 1608296378057407698070529 := by
  unfold tailWord_3132146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28559687427694361198530073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76159166473851629862746861 28559687427694361198530073)
  ·
    refine ⟨21419765570770770898897555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28559687427694361198530073 21419765570770770898897555)
    ·
      refine ⟨32129648356156156348346333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21419765570770770898897555 32129648356156156348346333)
      ·
        refine ⟨12048618133558558630629875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32129648356156156348346333 12048618133558558630629875)
        ·
          refine ⟨18072927200337837945944813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12048618133558558630629875 18072927200337837945944813)
          ·
            refine ⟨6777347700126689229729305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18072927200337837945944813 6777347700126689229729305)
            ·
              refine ⟨5083010775095016922296979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6777347700126689229729305 5083010775095016922296979)
              ·
                refine ⟨7624516162642525383445469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5083010775095016922296979 7624516162642525383445469)
                ·
                  refine ⟨2859193560990947018792051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7624516162642525383445469 2859193560990947018792051)
                  ·
                    refine ⟨4288790341486420528188077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2859193560990947018792051 4288790341486420528188077)
                    ·
                      refine ⟨1608296378057407698070529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4288790341486420528188077 1608296378057407698070529)
                      ·
                        rfl

theorem cell23_3132146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3132146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132146 prefixEnd_3132146 := by exact prefixLift 3132146
  have htrace : WordTrace (prefixWord ++ tailWord_3132146) baseStart_3132146 baseEnd_3132146 := by
    simpa [prefixWord, tailWord_3132146, baseEnd_3132146] using wordTrace_append hprefix tailTrace_3132146
  have hstable : (prefixWord ++ tailWord_3132146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132146).length < 2 ^ (prefixWord ++ tailWord_3132146).sum := by decide
  have hdescent : baseEnd_3132146 < baseStart_3132146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132175 : List Nat := [1, 1, 2, 1, 1, 1, 7, 9]
def baseStart_3132175 : Nat := 118140960795 + 3132175 * 2 ^ 59
def prefixEnd_3132175 : Nat := 4983230072969 + 3 ^ 40 * 3132175 * 2
def baseEnd_3132175 : Nat := 59567084036903262392885

theorem tailTrace_3132175 : CollatzResearch.WordTrace tailWord_3132175 prefixEnd_3132175 59567084036903262392885 := by
  unfold tailWord_3132175
  simp only [CollatzResearch.WordTrace]
  refine ⟨114239807427672382746925979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76159871618448255164617319 114239807427672382746925979)
  ·
    refine ⟨171359711141508574120388969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114239807427672382746925979 171359711141508574120388969)
    ·
      refine ⟨128519783356131430590291727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171359711141508574120388969 128519783356131430590291727)
      ·
        refine ⟨192779675034197145885437591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128519783356131430590291727 192779675034197145885437591)
        ·
          refine ⟨289169512551295718828156387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192779675034197145885437591 289169512551295718828156387)
          ·
            refine ⟨433754268826943578242234581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289169512551295718828156387 433754268826943578242234581)
            ·
              refine ⟨10166115675631490115052373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 433754268826943578242234581 10166115675631490115052373)
              ·
                refine ⟨59567084036903262392885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10166115675631490115052373 59567084036903262392885)
                ·
                  rfl

theorem cell23_3132175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 9].length) (baseStart_3132175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132175 prefixEnd_3132175 := by exact prefixLift 3132175
  have htrace : WordTrace (prefixWord ++ tailWord_3132175) baseStart_3132175 baseEnd_3132175 := by
    simpa [prefixWord, tailWord_3132175, baseEnd_3132175] using wordTrace_append hprefix tailTrace_3132175
  have hstable : (prefixWord ++ tailWord_3132175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132175).length < 2 ^ (prefixWord ++ tailWord_3132175).sum := by decide
  have hdescent : baseEnd_3132175 < baseStart_3132175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132192 : List Nat := [2, 1, 1, 5, 1, 4, 9]
def baseStart_3132192 : Nat := 118140960795 + 3132192 * 2 ^ 59
def prefixEnd_3132192 : Nat := 4983230072969 + 3 ^ 40 * 3132192 * 2
def baseEnd_3132192 : Nat := 19855802446512524914757

theorem tailTrace_3132192 : CollatzResearch.WordTrace tailWord_3132192 prefixEnd_3132192 19855802446512524914757 := by
  unfold tailWord_3132192
  simp only [CollatzResearch.WordTrace]
  refine ⟨57120213734305397325147415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76160284979073863100196553 57120213734305397325147415)
  ·
    refine ⟨85680320601458095987721123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57120213734305397325147415 85680320601458095987721123)
    ·
      refine ⟨128520480902187143981581685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85680320601458095987721123 128520480902187143981581685)
      ·
        refine ⟨12048795084580044748273283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128520480902187143981581685 12048795084580044748273283)
        ·
          refine ⟨18073192626870067122409925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12048795084580044748273283 18073192626870067122409925)
          ·
            refine ⟨3388723617538137585451861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18073192626870067122409925 3388723617538137585451861)
            ·
              refine ⟨19855802446512524914757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3388723617538137585451861 19855802446512524914757)
              ·
                rfl

theorem cell23_3132192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 9].length) (baseStart_3132192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132192 prefixEnd_3132192 := by exact prefixLift 3132192
  have htrace : WordTrace (prefixWord ++ tailWord_3132192) baseStart_3132192 baseEnd_3132192 := by
    simpa [prefixWord, tailWord_3132192, baseEnd_3132192] using wordTrace_append hprefix tailTrace_3132192
  have hstable : (prefixWord ++ tailWord_3132192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132192).length < 2 ^ (prefixWord ++ tailWord_3132192).sum := by decide
  have hdescent : baseEnd_3132192 < baseStart_3132192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132213 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 2, 4]
def baseStart_3132213 : Nat := 118140960795 + 3132213 * 2 ^ 59
def prefixEnd_3132213 : Nat := 4983230072969 + 3 ^ 40 * 3132213 * 2
def baseEnd_3132213 : Nat := 536110260420419645310907

theorem tailTrace_3132213 : CollatzResearch.WordTrace tailWord_3132213 prefixEnd_3132213 536110260420419645310907 := by
  unfold tailWord_3132213
  simp only [CollatzResearch.WordTrace]
  refine ⟨114241193401534715236809293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76160795601023143491206195 114241193401534715236809293)
  ·
    refine ⟨42840447525575518213803485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114241193401534715236809293 42840447525575518213803485)
    ·
      refine ⟨16065167822090819330176307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42840447525575518213803485 16065167822090819330176307)
      ·
        refine ⟨24097751733136228995264461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16065167822090819330176307 24097751733136228995264461)
        ·
          refine ⟨9036656899926085873224173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24097751733136228995264461 9036656899926085873224173)
          ·
            refine ⟨3388746337472282202459065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9036656899926085873224173 3388746337472282202459065)
            ·
              refine ⟨2541559753104211651844299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3388746337472282202459065 2541559753104211651844299)
              ·
                refine ⟨3812339629656317477766449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541559753104211651844299 3812339629656317477766449)
                ·
                  refine ⟨2859254722242238108324837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3812339629656317477766449 2859254722242238108324837)
                  ·
                    refine ⟨536110260420419645310907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2859254722242238108324837 536110260420419645310907)
                    ·
                      rfl

theorem cell23_3132213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_3132213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132213 prefixEnd_3132213 := by exact prefixLift 3132213
  have htrace : WordTrace (prefixWord ++ tailWord_3132213) baseStart_3132213 baseEnd_3132213 := by
    simpa [prefixWord, tailWord_3132213, baseEnd_3132213] using wordTrace_append hprefix tailTrace_3132213
  have hstable : (prefixWord ++ tailWord_3132213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132213).length < 2 ^ (prefixWord ++ tailWord_3132213).sum := by decide
  have hdescent : baseEnd_3132213 < baseStart_3132213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132272 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 4]
def baseStart_3132272 : Nat := 118140960795 + 3132272 * 2 ^ 59
def prefixEnd_3132272 : Nat := 4983230072969 + 3 ^ 40 * 3132272 * 2
def baseEnd_3132272 : Nat := 1608361076619874205094949

theorem tailTrace_3132272 : CollatzResearch.WordTrace tailWord_3132272 prefixEnd_3132272 1608361076619874205094949 := by
  unfold tailWord_3132272
  simp only [CollatzResearch.WordTrace]
  refine ⟨57121672654160484156603535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76162230205547312208804713 57121672654160484156603535)
  ·
    refine ⟨85682508981240726234905303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57121672654160484156603535 85682508981240726234905303)
    ·
      refine ⟨128523763471861089352357955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85682508981240726234905303 128523763471861089352357955)
      ·
        refine ⟨192785645207791634028536933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128523763471861089352357955 192785645207791634028536933)
        ·
          refine ⟨36147308476460931380350675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192785645207791634028536933 36147308476460931380350675)
          ·
            refine ⟨54220962714691397070526013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36147308476460931380350675 54220962714691397070526013)
            ·
              refine ⟨20332861018009273901447255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54220962714691397070526013 20332861018009273901447255)
              ·
                refine ⟨30499291527013910852170883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20332861018009273901447255 30499291527013910852170883)
                ·
                  refine ⟨45748937290520866278256325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30499291527013910852170883 45748937290520866278256325)
                  ·
                    refine ⟨8577925741972662427173061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45748937290520866278256325 8577925741972662427173061)
                    ·
                      refine ⟨1608361076619874205094949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8577925741972662427173061 1608361076619874205094949)
                      ·
                        rfl

theorem cell23_3132272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_3132272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132272 prefixEnd_3132272 := by exact prefixLift 3132272
  have htrace : WordTrace (prefixWord ++ tailWord_3132272) baseStart_3132272 baseEnd_3132272 := by
    simpa [prefixWord, tailWord_3132272, baseEnd_3132272] using wordTrace_append hprefix tailTrace_3132272
  have hstable : (prefixWord ++ tailWord_3132272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132272).length < 2 ^ (prefixWord ++ tailWord_3132272).sum := by decide
  have hdescent : baseEnd_3132272 < baseStart_3132272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132292 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_3132292 : Nat := 118140960795 + 3132292 * 2 ^ 59
def prefixEnd_3132292 : Nat := 4983230072969 + 3 ^ 40 * 3132292 * 2
def baseEnd_3132292 : Nat := 1608371346232964126844857

theorem tailTrace_3132292 : CollatzResearch.WordTrace tailWord_3132292 prefixEnd_3132292 1608371346232964126844857 := by
  unfold tailWord_3132292
  simp only [CollatzResearch.WordTrace]
  refine ⟨57122037384124255864467565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76162716512165674485956753 57122037384124255864467565)
  ·
    refine ⟨21420764019046595949175337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57122037384124255864467565 21420764019046595949175337)
    ·
      refine ⟨16065573014284946961881503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21420764019046595949175337 16065573014284946961881503)
      ·
        refine ⟨24098359521427420442822255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16065573014284946961881503 24098359521427420442822255)
        ·
          refine ⟨36147539282141130664233383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24098359521427420442822255 36147539282141130664233383)
          ·
            refine ⟨54221308923211695996350075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36147539282141130664233383 54221308923211695996350075)
            ·
              refine ⟨81331963384817543994525113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54221308923211695996350075 81331963384817543994525113)
              ·
                refine ⟨60998972538613157995893835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81331963384817543994525113 60998972538613157995893835)
                ·
                  refine ⟨91498458807919736993840753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60998972538613157995893835 91498458807919736993840753)
                  ·
                    refine ⟨68623844105939802745380565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91498458807919736993840753 68623844105939802745380565)
                    ·
                      refine ⟨1608371346232964126844857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68623844105939802745380565 1608371346232964126844857)
                      ·
                        rfl

theorem cell23_3132292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_3132292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132292 prefixEnd_3132292 := by exact prefixLift 3132292
  have htrace : WordTrace (prefixWord ++ tailWord_3132292) baseStart_3132292 baseEnd_3132292 := by
    simpa [prefixWord, tailWord_3132292, baseEnd_3132292] using wordTrace_append hprefix tailTrace_3132292
  have hstable : (prefixWord ++ tailWord_3132292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132292).length < 2 ^ (prefixWord ++ tailWord_3132292).sum := by decide
  have hdescent : baseEnd_3132292 < baseStart_3132292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132299 : List Nat := [1, 1, 1, 1, 4, 2, 3, 5, 5]
def baseStart_3132299 : Nat := 118140960795 + 3132299 * 2 ^ 59
def prefixEnd_3132299 : Nat := 4983230072969 + 3 ^ 40 * 3132299 * 2
def baseEnd_3132299 : Nat := 178708326733060622161925

theorem tailTrace_3132299 : CollatzResearch.WordTrace tailWord_3132299 prefixEnd_3132299 178708326733060622161925 := by
  unfold tailWord_3132299
  simp only [CollatzResearch.WordTrace]
  refine ⟨114244330079223151924439951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76162886719482101282959967 114244330079223151924439951)
  ·
    refine ⟨171366495118834727886659927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114244330079223151924439951 171366495118834727886659927)
    ·
      refine ⟨257049742678252091829989891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171366495118834727886659927 257049742678252091829989891)
      ·
        refine ⟨385574614017378137744984837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257049742678252091829989891 385574614017378137744984837)
        ·
          refine ⟨72295240128258400827184657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385574614017378137744984837 72295240128258400827184657)
          ·
            refine ⟨54221430096193800620388493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72295240128258400827184657 54221430096193800620388493)
            ·
              refine ⟨20333036286072675232645685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54221430096193800620388493 20333036286072675232645685)
              ·
                refine ⟨1906222151819313303060533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20333036286072675232645685 1906222151819313303060533)
                ·
                  refine ⟨178708326733060622161925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1906222151819313303060533 178708326733060622161925)
                  ·
                    rfl

theorem cell23_3132299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 5].length) (baseStart_3132299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132299 prefixEnd_3132299 := by exact prefixLift 3132299
  have htrace : WordTrace (prefixWord ++ tailWord_3132299) baseStart_3132299 baseEnd_3132299 := by
    simpa [prefixWord, tailWord_3132299, baseEnd_3132299] using wordTrace_append hprefix tailTrace_3132299
  have hstable : (prefixWord ++ tailWord_3132299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132299).length < 2 ^ (prefixWord ++ tailWord_3132299).sum := by decide
  have hdescent : baseEnd_3132299 < baseStart_3132299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132309 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_3132309 : Nat := 118140960795 + 3132309 * 2 ^ 59
def prefixEnd_3132309 : Nat := 4983230072969 + 3 ^ 40 * 3132309 * 2
def baseEnd_3132309 : Nat := 1608380075404090560332279

theorem tailTrace_3132309 : CollatzResearch.WordTrace tailWord_3132309 prefixEnd_3132309 1608380075404090560332279 := by
  unfold tailWord_3132309
  simp only [CollatzResearch.WordTrace]
  refine ⟨114244694809186923632303981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76163129872791282421535987 114244694809186923632303981)
  ·
    refine ⟨42841760553445096362113993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114244694809186923632303981 42841760553445096362113993)
    ·
      refine ⟨32131320415083822271585495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42841760553445096362113993 32131320415083822271585495)
      ·
        refine ⟨48196980622625733407378243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32131320415083822271585495 48196980622625733407378243)
        ·
          refine ⟨72295470933938600111067365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48196980622625733407378243 72295470933938600111067365)
          ·
            refine ⟨13555400800113487520825131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72295470933938600111067365 13555400800113487520825131)
            ·
              refine ⟨20333101200170231281237697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13555400800113487520825131 20333101200170231281237697)
              ·
                refine ⟨15249825900127673460928273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20333101200170231281237697 15249825900127673460928273)
                ·
                  refine ⟨11437369425095755095696205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15249825900127673460928273 11437369425095755095696205)
                  ·
                    refine ⟨4289013534410908160886077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11437369425095755095696205 4289013534410908160886077)
                    ·
                      refine ⟨1608380075404090560332279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4289013534410908160886077 1608380075404090560332279)
                      ·
                        rfl

theorem cell23_3132309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_3132309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132309 prefixEnd_3132309 := by exact prefixLift 3132309
  have htrace : WordTrace (prefixWord ++ tailWord_3132309) baseStart_3132309 baseEnd_3132309 := by
    simpa [prefixWord, tailWord_3132309, baseEnd_3132309] using wordTrace_append hprefix tailTrace_3132309
  have hstable : (prefixWord ++ tailWord_3132309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132309).length < 2 ^ (prefixWord ++ tailWord_3132309).sum := by decide
  have hdescent : baseEnd_3132309 < baseStart_3132309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132316 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 7]
def baseStart_3132316 : Nat := 118140960795 + 3132316 * 2 ^ 59
def prefixEnd_3132316 : Nat := 4983230072969 + 3 ^ 40 * 3132316 * 2
def baseEnd_3132316 : Nat := 178709296640963559216083

theorem tailTrace_3132316 : CollatzResearch.WordTrace tailWord_3132316 prefixEnd_3132316 178709296640963559216083 := by
  unfold tailWord_3132316
  simp only [CollatzResearch.WordTrace]
  refine ⟨57122475060080781913904401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76163300080107709218539201 57122475060080781913904401)
  ·
    refine ⟨42841856295060586435428301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57122475060080781913904401 42841856295060586435428301)
    ·
      refine ⟨16065696110647719913285613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42841856295060586435428301 16065696110647719913285613)
      ·
        refine ⟨6024636041492894967482105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16065696110647719913285613 6024636041492894967482105)
        ·
          refine ⟨4518477031119671225611579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6024636041492894967482105 4518477031119671225611579)
          ·
            refine ⟨6777715546679506838417369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518477031119671225611579 6777715546679506838417369)
            ·
              refine ⟨5083286660009630128813027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6777715546679506838417369 5083286660009630128813027)
              ·
                refine ⟨7624929990014445193219541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5083286660009630128813027 7624929990014445193219541)
                ·
                  refine ⟨178709296640963559216083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7624929990014445193219541 178709296640963559216083)
                  ·
                    rfl

theorem cell23_3132316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_3132316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132316 prefixEnd_3132316 := by exact prefixLift 3132316
  have htrace : WordTrace (prefixWord ++ tailWord_3132316) baseStart_3132316 baseEnd_3132316 := by
    simpa [prefixWord, tailWord_3132316, baseEnd_3132316] using wordTrace_append hprefix tailTrace_3132316
  have hstable : (prefixWord ++ tailWord_3132316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132316).length < 2 ^ (prefixWord ++ tailWord_3132316).sum := by decide
  have hdescent : baseEnd_3132316 < baseStart_3132316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132327 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_3132327 : Nat := 118140960795 + 3132327 * 2 ^ 59
def prefixEnd_3132327 : Nat := 4983230072969 + 3 ^ 40 * 3132327 * 2
def baseEnd_3132327 : Nat := 1608389318055871489907197

theorem tailTrace_3132327 : CollatzResearch.WordTrace tailWord_3132327 prefixEnd_3132327 1608389318055871489907197 := by
  unfold tailWord_3132327
  simp only [CollatzResearch.WordTrace]
  refine ⟨114245351323121712706459235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76163567548747808470972823 114245351323121712706459235)
  ·
    refine ⟨171368026984682569059688853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114245351323121712706459235 171368026984682569059688853)
    ·
      refine ⟨8032876264906995424672915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 171368026984682569059688853 8032876264906995424672915)
      ·
        refine ⟨12049314397360493137009373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8032876264906995424672915 12049314397360493137009373)
        ·
          refine ⟨4518492899010184926378515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12049314397360493137009373 4518492899010184926378515)
          ·
            refine ⟨6777739348515277389567773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518492899010184926378515 6777739348515277389567773)
            ·
              refine ⟨2541652255693229021087915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6777739348515277389567773 2541652255693229021087915)
              ·
                refine ⟨3812478383539843531631873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541652255693229021087915 3812478383539843531631873)
                ·
                  refine ⟨2859358787654882648723905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3812478383539843531631873 2859358787654882648723905)
                  ·
                    refine ⟨2144519090741161986542929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2859358787654882648723905 2144519090741161986542929)
                    ·
                      refine ⟨1608389318055871489907197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2144519090741161986542929 1608389318055871489907197)
                      ·
                        rfl

theorem cell23_3132327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_3132327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132327 prefixEnd_3132327 := by exact prefixLift 3132327
  have htrace : WordTrace (prefixWord ++ tailWord_3132327) baseStart_3132327 baseEnd_3132327 := by
    simpa [prefixWord, tailWord_3132327, baseEnd_3132327] using wordTrace_append hprefix tailTrace_3132327
  have hstable : (prefixWord ++ tailWord_3132327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132327).length < 2 ^ (prefixWord ++ tailWord_3132327).sum := by decide
  have hdescent : baseEnd_3132327 < baseStart_3132327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132359 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 5, 4]
def baseStart_3132359 : Nat := 118140960795 + 3132359 * 2 ^ 59
def prefixEnd_3132359 : Nat := 4983230072969 + 3 ^ 40 * 3132359 * 2
def baseEnd_3132359 : Nat := 536135249812271788235683

theorem tailTrace_3132359 : CollatzResearch.WordTrace tailWord_3132359 prefixEnd_3132359 536135249812271788235683 := by
  unfold tailWord_3132359
  simp only [CollatzResearch.WordTrace]
  refine ⟨114246518459005782171624131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76164345639337188114416087 114246518459005782171624131)
  ·
    refine ⟨171369777688508673257436197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114246518459005782171624131 171369777688508673257436197)
    ·
      refine ⟨32131833316595376235769287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171369777688508673257436197 32131833316595376235769287)
      ·
        refine ⟨48197749974893064353653931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32131833316595376235769287 48197749974893064353653931)
        ·
          refine ⟨72296624962339596530480897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48197749974893064353653931 72296624962339596530480897)
          ·
            refine ⟨54222468721754697397860673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72296624962339596530480897 54222468721754697397860673)
            ·
              refine ⟨40666851541316023048395505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54222468721754697397860673 40666851541316023048395505)
              ·
                refine ⟨30500138655987017286296629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40666851541316023048395505 30500138655987017286296629)
                ·
                  refine ⟨2859387998998782870590309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30500138655987017286296629 2859387998998782870590309)
                  ·
                    refine ⟨536135249812271788235683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2859387998998782870590309 536135249812271788235683)
                    ·
                      rfl

theorem cell23_3132359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_3132359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132359 prefixEnd_3132359 := by exact prefixLift 3132359
  have htrace : WordTrace (prefixWord ++ tailWord_3132359) baseStart_3132359 baseEnd_3132359 := by
    simpa [prefixWord, tailWord_3132359, baseEnd_3132359] using wordTrace_append hprefix tailTrace_3132359
  have hstable : (prefixWord ++ tailWord_3132359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132359).length < 2 ^ (prefixWord ++ tailWord_3132359).sum := by decide
  have hdescent : baseEnd_3132359 < baseStart_3132359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132366 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_3132366 : Nat := 118140960795 + 3132366 * 2 ^ 59
def prefixEnd_3132366 : Nat := 4983230072969 + 3 ^ 40 * 3132366 * 2
def baseEnd_3132366 : Nat := 1608409343801396837319517

theorem tailTrace_3132366 : CollatzResearch.WordTrace tailWord_3132366 prefixEnd_3132366 1608409343801396837319517 := by
  unfold tailWord_3132366
  simp only [CollatzResearch.WordTrace]
  refine ⟨14280846721247552795891119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76164515846653614911419301 14280846721247552795891119)
  ·
    refine ⟨21421270081871329193836679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14280846721247552795891119 21421270081871329193836679)
    ·
      refine ⟨32131905122806993790755019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21421270081871329193836679 32131905122806993790755019)
      ·
        refine ⟨48197857684210490686132529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32131905122806993790755019 48197857684210490686132529)
        ·
          refine ⟨36148393263157868014599397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48197857684210490686132529 36148393263157868014599397)
          ·
            refine ⟨6777823736842100252737387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36148393263157868014599397 6777823736842100252737387)
            ·
              refine ⟨10166735605263150379106081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6777823736842100252737387 10166735605263150379106081)
              ·
                refine ⟨7625051703947362784329561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10166735605263150379106081 7625051703947362784329561)
                ·
                  refine ⟨5718788777960522088247171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7625051703947362784329561 5718788777960522088247171)
                  ·
                    refine ⟨8578183166940783132370757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5718788777960522088247171 8578183166940783132370757)
                    ·
                      refine ⟨1608409343801396837319517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8578183166940783132370757 1608409343801396837319517)
                      ·
                        rfl

theorem cell23_3132366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_3132366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132366 prefixEnd_3132366 := by exact prefixLift 3132366
  have htrace : WordTrace (prefixWord ++ tailWord_3132366) baseStart_3132366 baseEnd_3132366 := by
    simpa [prefixWord, tailWord_3132366, baseEnd_3132366] using wordTrace_append hprefix tailTrace_3132366
  have hstable : (prefixWord ++ tailWord_3132366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132366).length < 2 ^ (prefixWord ++ tailWord_3132366).sum := by decide
  have hdescent : baseEnd_3132366 < baseStart_3132366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132376 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 3, 4]
def baseStart_3132376 : Nat := 118140960795 + 3132376 * 2 ^ 59
def prefixEnd_3132376 : Nat := 4983230072969 + 3 ^ 40 * 3132376 * 2
def baseEnd_3132376 : Nat := 536138159535980599398157

theorem tailTrace_3132376 : CollatzResearch.WordTrace tailWord_3132376 prefixEnd_3132376 536138159535980599398157 := by
  unfold tailWord_3132376
  simp only [CollatzResearch.WordTrace]
  refine ⟨57123569249972097037496491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76164758999962796049995321 57123569249972097037496491)
  ·
    refine ⟨85685353874958145556244737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57123569249972097037496491 85685353874958145556244737)
    ·
      refine ⟨64264015406218609167183553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85685353874958145556244737 64264015406218609167183553)
      ·
        refine ⟨48198011554663956875387665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64264015406218609167183553 48198011554663956875387665)
        ·
          refine ⟨36148508665997967656540749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48198011554663956875387665 36148508665997967656540749)
          ·
            refine ⟨13555690749749237871202781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36148508665997967656540749 13555690749749237871202781)
            ·
              refine ⟨5083384031155964201701043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13555690749749237871202781 5083384031155964201701043)
              ·
                refine ⟨7625076046733946302551565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5083384031155964201701043 7625076046733946302551565)
                ·
                  refine ⟨2859403517525229863456837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7625076046733946302551565 2859403517525229863456837)
                  ·
                    refine ⟨536138159535980599398157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2859403517525229863456837 536138159535980599398157)
                    ·
                      rfl

theorem cell23_3132376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_3132376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132376 prefixEnd_3132376 := by exact prefixLift 3132376
  have htrace : WordTrace (prefixWord ++ tailWord_3132376) baseStart_3132376 baseEnd_3132376 := by
    simpa [prefixWord, tailWord_3132376, baseEnd_3132376] using wordTrace_append hprefix tailTrace_3132376
  have hstable : (prefixWord ++ tailWord_3132376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132376).length < 2 ^ (prefixWord ++ tailWord_3132376).sum := by decide
  have hdescent : baseEnd_3132376 < baseStart_3132376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132466 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_3132466 : Nat := 118140960795 + 3132466 * 2 ^ 59
def prefixEnd_3132466 : Nat := 4983230072969 + 3 ^ 40 * 3132466 * 2
def baseEnd_3132466 : Nat := 536153563955615482023019

theorem tailTrace_3132466 : CollatzResearch.WordTrace tailWord_3132466 prefixEnd_3132466 536153563955615482023019 := by
  unfold tailWord_3132466
  simp only [CollatzResearch.WordTrace]
  refine ⟨28562605267404534861442313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76166947379745426297179501 28562605267404534861442313)
  ·
    refine ⟨21421953950553401146081735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28562605267404534861442313 21421953950553401146081735)
    ·
      refine ⟨32132930925830101719122603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21421953950553401146081735 32132930925830101719122603)
      ·
        refine ⟨48199396388745152578683905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32132930925830101719122603 48199396388745152578683905)
        ·
          refine ⟨36149547291558864434012929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48199396388745152578683905 36149547291558864434012929)
          ·
            refine ⟨27112160468669148325509697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36149547291558864434012929 27112160468669148325509697)
            ·
              refine ⟨20334120351501861244132273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27112160468669148325509697 20334120351501861244132273)
              ·
                refine ⟨15250590263626395933099205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20334120351501861244132273 15250590263626395933099205)
                ·
                  refine ⟨2859485674429949237456101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15250590263626395933099205 2859485674429949237456101)
                  ·
                    refine ⟨536153563955615482023019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2859485674429949237456101 536153563955615482023019)
                    ·
                      rfl

theorem cell23_3132466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_3132466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132466 prefixEnd_3132466 := by exact prefixLift 3132466
  have htrace : WordTrace (prefixWord ++ tailWord_3132466) baseStart_3132466 baseEnd_3132466 := by
    simpa [prefixWord, tailWord_3132466, baseEnd_3132466] using wordTrace_append hprefix tailTrace_3132466
  have hstable : (prefixWord ++ tailWord_3132466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132466).length < 2 ^ (prefixWord ++ tailWord_3132466).sum := by decide
  have hdescent : baseEnd_3132466 < baseStart_3132466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132469 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_3132469 : Nat := 118140960795 + 3132469 * 2 ^ 59
def prefixEnd_3132469 : Nat := 4983230072969 + 3 ^ 40 * 3132469 * 2
def baseEnd_3132469 : Nat := 1608462232308809934331543

theorem tailTrace_3132469 : CollatzResearch.WordTrace tailWord_3132469 prefixEnd_3132469 1608462232308809934331543 := by
  unfold tailWord_3132469
  simp only [CollatzResearch.WordTrace]
  refine ⟨114250530488607270958128461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76167020325738180638752307 114250530488607270958128461)
  ·
    refine ⟨42843948933227726609298173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114250530488607270958128461 42843948933227726609298173)
    ·
      refine ⟨16066480849960397478486815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42843948933227726609298173 16066480849960397478486815)
      ·
        refine ⟨24099721274940596217730223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16066480849960397478486815 24099721274940596217730223)
        ·
          refine ⟨36149581912410894326595335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24099721274940596217730223 36149581912410894326595335)
          ·
            refine ⟨54224372868616341489893003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36149581912410894326595335 54224372868616341489893003)
            ·
              refine ⟨81336559302924512234839505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54224372868616341489893003 81336559302924512234839505)
              ·
                refine ⟨61002419477193384176129629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81336559302924512234839505 61002419477193384176129629)
                ·
                  refine ⟨22875907303947519066048611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61002419477193384176129629 22875907303947519066048611)
                  ·
                    refine ⟨34313860955921278599072917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22875907303947519066048611 34313860955921278599072917)
                    ·
                      refine ⟨1608462232308809934331543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34313860955921278599072917 1608462232308809934331543)
                      ·
                        rfl

theorem cell23_3132469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_3132469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132469 prefixEnd_3132469 := by exact prefixLift 3132469
  have htrace : WordTrace (prefixWord ++ tailWord_3132469) baseStart_3132469 baseEnd_3132469 := by
    simpa [prefixWord, tailWord_3132469, baseEnd_3132469] using wordTrace_append hprefix tailTrace_3132469
  have hstable : (prefixWord ++ tailWord_3132469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132469).length < 2 ^ (prefixWord ++ tailWord_3132469).sum := by decide
  have hdescent : baseEnd_3132469 < baseStart_3132469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132470 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_3132470 : Nat := 118140960795 + 3132470 * 2 ^ 59
def prefixEnd_3132470 : Nat := 4983230072969 + 3 ^ 40 * 3132470 * 2
def baseEnd_3132470 : Nat := 536154248596488143473013

theorem tailTrace_3132470 : CollatzResearch.WordTrace tailWord_3132470 prefixEnd_3132470 536154248596488143473013 := by
  unfold tailWord_3132470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7140660435100228008057179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76167044641069098752609909 7140660435100228008057179)
  ·
    refine ⟨10710990652650342012085769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7140660435100228008057179 10710990652650342012085769)
    ·
      refine ⟨8033242989487756509064327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10710990652650342012085769 8033242989487756509064327)
      ·
        refine ⟨12049864484231634763596491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8033242989487756509064327 12049864484231634763596491)
        ·
          refine ⟨18074796726347452145394737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12049864484231634763596491 18074796726347452145394737)
          ·
            refine ⟨13556097544760589109046053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18074796726347452145394737 13556097544760589109046053)
            ·
              refine ⟨2541768289642610457946135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13556097544760589109046053 2541768289642610457946135)
              ·
                refine ⟨3812652434463915686919203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541768289642610457946135 3812652434463915686919203)
                ·
                  refine ⟨5718978651695873530378805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3812652434463915686919203 5718978651695873530378805)
                  ·
                    refine ⟨536154248596488143473013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5718978651695873530378805 536154248596488143473013)
                    ·
                      rfl

theorem cell23_3132470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_3132470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132470 prefixEnd_3132470 := by exact prefixLift 3132470
  have htrace : WordTrace (prefixWord ++ tailWord_3132470) baseStart_3132470 baseEnd_3132470 := by
    simpa [prefixWord, tailWord_3132470, baseEnd_3132470] using wordTrace_append hprefix tailTrace_3132470
  have hstable : (prefixWord ++ tailWord_3132470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132470).length < 2 ^ (prefixWord ++ tailWord_3132470).sum := by decide
  have hdescent : baseEnd_3132470 < baseStart_3132470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132473 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3132473 : Nat := 118140960795 + 3132473 * 2 ^ 59
def prefixEnd_3132473 : Nat := 4983230072969 + 3 ^ 40 * 3132473 * 2
def baseEnd_3132473 : Nat := 1608464286231427918681525

theorem tailTrace_3132473 : CollatzResearch.WordTrace tailWord_3132473 prefixEnd_3132473 1608464286231427918681525 := by
  unfold tailWord_3132473
  simp only [CollatzResearch.WordTrace]
  refine ⟨114250676380592779641274073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76167117587061853094182715 114250676380592779641274073)
  ·
    refine ⟨85688007285444584730955555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114250676380592779641274073 85688007285444584730955555)
    ·
      refine ⟨128532010928166877096433333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85688007285444584730955555 128532010928166877096433333)
      ·
        refine ⟨12049876024515644727790625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128532010928166877096433333 12049876024515644727790625)
        ·
          refine ⟨9037407018386733545842969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12049876024515644727790625 9037407018386733545842969)
          ·
            refine ⟨6778055263790050159382227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9037407018386733545842969 6778055263790050159382227)
            ·
              refine ⟨10167082895685075239073341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6778055263790050159382227 10167082895685075239073341)
              ·
                refine ⟨3812656085881903214652503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10167082895685075239073341 3812656085881903214652503)
                ·
                  refine ⟨5718984128822854821978755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3812656085881903214652503 5718984128822854821978755)
                  ·
                    refine ⟨8578476193234282232968133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5718984128822854821978755 8578476193234282232968133)
                    ·
                      refine ⟨1608464286231427918681525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8578476193234282232968133 1608464286231427918681525)
                      ·
                        rfl

theorem cell23_3132473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3132473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132473 prefixEnd_3132473 := by exact prefixLift 3132473
  have htrace : WordTrace (prefixWord ++ tailWord_3132473) baseStart_3132473 baseEnd_3132473 := by
    simpa [prefixWord, tailWord_3132473, baseEnd_3132473] using wordTrace_append hprefix tailTrace_3132473
  have hstable : (prefixWord ++ tailWord_3132473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132473).length < 2 ^ (prefixWord ++ tailWord_3132473).sum := by decide
  have hdescent : baseEnd_3132473 < baseStart_3132473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132493 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3132493 : Nat := 118140960795 + 3132493 * 2 ^ 59
def prefixEnd_3132493 : Nat := 4983230072969 + 3 ^ 40 * 3132493 * 2
def baseEnd_3132493 : Nat := 1608474555844517840431433

theorem tailTrace_3132493 : CollatzResearch.WordTrace tailWord_3132493 prefixEnd_3132493 1608474555844517840431433 := by
  unfold tailWord_3132493
  simp only [CollatzResearch.WordTrace]
  refine ⟨114251405840520323057002133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76167603893680215371334755 114251405840520323057002133)
  ·
    refine ⟨5355534648774390143296975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114251405840520323057002133 5355534648774390143296975)
    ·
      refine ⟨8033301973161585214945463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5355534648774390143296975 8033301973161585214945463)
      ·
        refine ⟨12049952959742377822418195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8033301973161585214945463 12049952959742377822418195)
        ·
          refine ⟨18074929439613566733627293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12049952959742377822418195 18074929439613566733627293)
          ·
            refine ⟨6778098539855087525110235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18074929439613566733627293 6778098539855087525110235)
            ·
              refine ⟨10167147809782631287665353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6778098539855087525110235 10167147809782631287665353)
              ·
                refine ⟨7625360857336973465749015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10167147809782631287665353 7625360857336973465749015)
                ·
                  refine ⟨11438041286005460198623523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7625360857336973465749015 11438041286005460198623523)
                  ·
                    refine ⟨17157061929008190297935285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11438041286005460198623523 17157061929008190297935285)
                    ·
                      refine ⟨1608474555844517840431433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17157061929008190297935285 1608474555844517840431433)
                      ·
                        rfl

theorem cell23_3132493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3132493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132493 prefixEnd_3132493 := by exact prefixLift 3132493
  have htrace : WordTrace (prefixWord ++ tailWord_3132493) baseStart_3132493 baseEnd_3132493 := by
    simpa [prefixWord, tailWord_3132493, baseEnd_3132493] using wordTrace_append hprefix tailTrace_3132493
  have hstable : (prefixWord ++ tailWord_3132493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132493).length < 2 ^ (prefixWord ++ tailWord_3132493).sum := by decide
  have hdescent : baseEnd_3132493 < baseStart_3132493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132506 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3]
def baseStart_3132506 : Nat := 118140960795 + 3132506 * 2 ^ 59
def prefixEnd_3132506 : Nat := 4983230072969 + 3 ^ 40 * 3132506 * 2
def baseEnd_3132506 : Nat := 1608481231093026289568873

theorem tailTrace_3132506 : CollatzResearch.WordTrace tailWord_3132506 prefixEnd_3132506 1608481231093026289568873 := by
  unfold tailWord_3132506
  simp only [CollatzResearch.WordTrace]
  refine ⟨28562969997368306569306343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76167919992982150851483581 28562969997368306569306343)
  ·
    refine ⟨42844454996052459853959515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28562969997368306569306343 42844454996052459853959515)
    ·
      refine ⟨64266682494078689780939273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42844454996052459853959515 64266682494078689780939273)
      ·
        refine ⟨48200011870559017335704455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64266682494078689780939273 48200011870559017335704455)
        ·
          refine ⟨72300017805838526003556683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48200011870559017335704455 72300017805838526003556683)
          ·
            refine ⟨108450026708757789005335025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72300017805838526003556683 108450026708757789005335025)
            ·
              refine ⟨81337520031568341754001269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108450026708757789005335025 81337520031568341754001269)
              ·
                refine ⟨7625392502959532039437619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81337520031568341754001269 7625392502959532039437619)
                ·
                  refine ⟨11438088754439298059156429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7625392502959532039437619 11438088754439298059156429)
                  ·
                    refine ⟨4289283282914736772183661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11438088754439298059156429 4289283282914736772183661)
                    ·
                      refine ⟨1608481231093026289568873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4289283282914736772183661 1608481231093026289568873)
                      ·
                        rfl

theorem cell23_3132506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_3132506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132506 prefixEnd_3132506 := by exact prefixLift 3132506
  have htrace : WordTrace (prefixWord ++ tailWord_3132506) baseStart_3132506 baseEnd_3132506 := by
    simpa [prefixWord, tailWord_3132506, baseEnd_3132506] using wordTrace_append hprefix tailTrace_3132506
  have hstable : (prefixWord ++ tailWord_3132506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132506).length < 2 ^ (prefixWord ++ tailWord_3132506).sum := by decide
  have hdescent : baseEnd_3132506 < baseStart_3132506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132539 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 4, 6]
def baseStart_3132539 : Nat := 118140960795 + 3132539 * 2 ^ 59
def prefixEnd_3132539 : Nat := 4983230072969 + 3 ^ 40 * 3132539 * 2
def baseEnd_3132539 : Nat := 536166058651541553485407

theorem tailTrace_3132539 : CollatzResearch.WordTrace tailWord_3132539 prefixEnd_3132539 536166058651541553485407 := by
  unfold tailWord_3132539
  simp only [CollatzResearch.WordTrace]
  refine ⟨114253083598353672913176671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76168722398902448608784447 114253083598353672913176671)
  ·
    refine ⟨171379625397530509369765007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114253083598353672913176671 171379625397530509369765007)
    ·
      refine ⟨257069438096295764054647511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171379625397530509369765007 257069438096295764054647511)
      ·
        refine ⟨385604157144443646081971267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257069438096295764054647511 385604157144443646081971267)
        ·
          refine ⟨578406235716665469122956901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385604157144443646081971267 578406235716665469122956901)
          ·
            refine ⟨108451169196874775460554419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 578406235716665469122956901 108451169196874775460554419)
            ·
              refine ⟨162676753795312163190831629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108451169196874775460554419 162676753795312163190831629)
              ·
                refine ⟨61003782673242061196561861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162676753795312163190831629 61003782673242061196561861)
                ·
                  refine ⟨11438209251232886474355349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61003782673242061196561861 11438209251232886474355349)
                  ·
                    refine ⟨536166058651541553485407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11438209251232886474355349 536166058651541553485407)
                    ·
                      rfl

theorem cell23_3132539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 6].length) (baseStart_3132539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132539 prefixEnd_3132539 := by exact prefixLift 3132539
  have htrace : WordTrace (prefixWord ++ tailWord_3132539) baseStart_3132539 baseEnd_3132539 := by
    simpa [prefixWord, tailWord_3132539, baseEnd_3132539] using wordTrace_append hprefix tailTrace_3132539
  have hstable : (prefixWord ++ tailWord_3132539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132539).length < 2 ^ (prefixWord ++ tailWord_3132539).sum := by decide
  have hdescent : baseEnd_3132539 < baseStart_3132539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132567 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 1, 3, 2]
def baseStart_3132567 : Nat := 118140960795 + 3132567 * 2 ^ 59
def prefixEnd_3132567 : Nat := 4983230072969 + 3 ^ 40 * 3132567 * 2
def baseEnd_3132567 : Nat := 1608512553412950550906093

theorem tailTrace_3132567 : CollatzResearch.WordTrace tailWord_3132567 prefixEnd_3132567 1608512553412950550906093 := by
  unfold tailWord_3132567
  simp only [CollatzResearch.WordTrace]
  refine ⟨114254104842252233695195955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76169403228168155796797303 114254104842252233695195955)
  ·
    refine ⟨171381157263378350542793933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114254104842252233695195955 171381157263378350542793933)
    ·
      refine ⟨64267933973766881453547725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171381157263378350542793933 64267933973766881453547725)
      ·
        refine ⟨24100475240162580545080397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64267933973766881453547725 24100475240162580545080397)
        ·
          refine ⟨9037678215060967704405149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24100475240162580545080397 9037678215060967704405149)
          ·
            refine ⟨3389129330647862889151931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9037678215060967704405149 3389129330647862889151931)
            ·
              refine ⟨5083693995971794333727897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389129330647862889151931 5083693995971794333727897)
              ·
                refine ⟨3812770496978845750295923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5083693995971794333727897 3812770496978845750295923)
                ·
                  refine ⟨5719155745468268625443885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3812770496978845750295923 5719155745468268625443885)
                  ·
                    refine ⟨2144683404550600734541457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5719155745468268625443885 2144683404550600734541457)
                    ·
                      refine ⟨1608512553412950550906093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2144683404550600734541457 1608512553412950550906093)
                      ·
                        rfl

theorem cell23_3132567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_3132567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132567 prefixEnd_3132567 := by exact prefixLift 3132567
  have htrace : WordTrace (prefixWord ++ tailWord_3132567) baseStart_3132567 baseEnd_3132567 := by
    simpa [prefixWord, tailWord_3132567, baseEnd_3132567] using wordTrace_append hprefix tailTrace_3132567
  have hstable : (prefixWord ++ tailWord_3132567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132567).length < 2 ^ (prefixWord ++ tailWord_3132567).sum := by decide
  have hdescent : baseEnd_3132567 < baseStart_3132567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132580 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 1, 4, 2]
def baseStart_3132580 : Nat := 118140960795 + 3132580 * 2 ^ 59
def prefixEnd_3132580 : Nat := 4983230072969 + 3 ^ 40 * 3132580 * 2
def baseEnd_3132580 : Nat := 1608519228661459000043533

theorem tailTrace_3132580 : CollatzResearch.WordTrace tailWord_3132580 prefixEnd_3132580 1608519228661459000043533 := by
  unfold tailWord_3132580
  simp only [CollatzResearch.WordTrace]
  refine ⟨57127289495602568457709597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76169719327470091276946129 57127289495602568457709597)
  ·
    refine ⟨21422733560850963171641099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57127289495602568457709597 21422733560850963171641099)
    ·
      refine ⟨32134100341276444757461649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21422733560850963171641099 32134100341276444757461649)
      ·
        refine ⟨24100575255957333568096237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32134100341276444757461649 24100575255957333568096237)
        ·
          refine ⟨9037715720984000088036089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24100575255957333568096237 9037715720984000088036089)
          ·
            refine ⟨6778286790738000066027067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9037715720984000088036089 6778286790738000066027067)
            ·
              refine ⟨10167430186107000099040601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6778286790738000066027067 10167430186107000099040601)
              ·
                refine ⟨7625572639580250074280451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10167430186107000099040601 7625572639580250074280451)
                ·
                  refine ⟨11438358959370375111420677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7625572639580250074280451 11438358959370375111420677)
                  ·
                    refine ⟨2144692304881945333391377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11438358959370375111420677 2144692304881945333391377)
                    ·
                      refine ⟨1608519228661459000043533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2144692304881945333391377 1608519228661459000043533)
                      ·
                        rfl

theorem cell23_3132580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_3132580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132580 prefixEnd_3132580 := by exact prefixLift 3132580
  have htrace : WordTrace (prefixWord ++ tailWord_3132580) baseStart_3132580 baseEnd_3132580 := by
    simpa [prefixWord, tailWord_3132580, baseEnd_3132580] using wordTrace_append hprefix tailTrace_3132580
  have hstable : (prefixWord ++ tailWord_3132580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132580).length < 2 ^ (prefixWord ++ tailWord_3132580).sum := by decide
  have hdescent : baseEnd_3132580 < baseStart_3132580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132583 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3132583 : Nat := 118140960795 + 3132583 * 2 ^ 59
def prefixEnd_3132583 : Nat := 4983230072969 + 3 ^ 40 * 3132583 * 2
def baseEnd_3132583 : Nat := 1608520769103422488306019

theorem tailTrace_3132583 : CollatzResearch.WordTrace tailWord_3132583 prefixEnd_3132583 1608520769103422488306019 := by
  unfold tailWord_3132583
  simp only [CollatzResearch.WordTrace]
  refine ⟨114254688410194268427778403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76169792273462845618518935 114254688410194268427778403)
  ·
    refine ⟨171382032615291402641667605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114254688410194268427778403 171382032615291402641667605)
    ·
      refine ⟨8033532778841784498828169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 171382032615291402641667605 8033532778841784498828169)
      ·
        refine ⟨6025149584131338374121127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8033532778841784498828169 6025149584131338374121127)
        ·
          refine ⟨9037724376197007561181691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6025149584131338374121127 9037724376197007561181691)
          ·
            refine ⟨13556586564295511341772537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9037724376197007561181691 13556586564295511341772537)
            ·
              refine ⟨10167439923221633506329403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13556586564295511341772537 10167439923221633506329403)
              ·
                refine ⟨15251159884832450259494105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10167439923221633506329403 15251159884832450259494105)
                ·
                  refine ⟨11438369913624337694620579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15251159884832450259494105 11438369913624337694620579)
                  ·
                    refine ⟨17157554870436506541930869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11438369913624337694620579 17157554870436506541930869)
                    ·
                      refine ⟨1608520769103422488306019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17157554870436506541930869 1608520769103422488306019)
                      ·
                        rfl

theorem cell23_3132583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3132583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132583 prefixEnd_3132583 := by exact prefixLift 3132583
  have htrace : WordTrace (prefixWord ++ tailWord_3132583) baseStart_3132583 baseEnd_3132583 := by
    simpa [prefixWord, tailWord_3132583, baseEnd_3132583] using wordTrace_append hprefix tailTrace_3132583
  have hstable : (prefixWord ++ tailWord_3132583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132583).length < 2 ^ (prefixWord ++ tailWord_3132583).sum := by decide
  have hdescent : baseEnd_3132583 < baseStart_3132583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132616 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 4, 5]
def baseStart_3132616 : Nat := 118140960795 + 3132616 * 2 ^ 59
def prefixEnd_3132616 : Nat := 4983230072969 + 3 ^ 40 * 3132616 * 2
def baseEnd_3132616 : Nat := 536179237988340286397789

theorem tailTrace_3132616 : CollatzResearch.WordTrace tailWord_3132616 prefixEnd_3132616 536179237988340286397789 := by
  unfold tailWord_3132616
  simp only [CollatzResearch.WordTrace]
  refine ⟨57127946009537357531864851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76170594679383143375819801 57127946009537357531864851)
  ·
    refine ⟨85691919014306036297797277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57127946009537357531864851 85691919014306036297797277)
    ·
      refine ⟨32134469630364763611673979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85691919014306036297797277 32134469630364763611673979)
      ·
        refine ⟨48201704445547145417510969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32134469630364763611673979 48201704445547145417510969)
        ·
          refine ⟨36151278334160359063133227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48201704445547145417510969 36151278334160359063133227)
          ·
            refine ⟨54226917501240538594699841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36151278334160359063133227 54226917501240538594699841)
            ·
              refine ⟨40670188125930403946024881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54226917501240538594699841 40670188125930403946024881)
              ·
                refine ⟨30502641094447802959518661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40670188125930403946024881 30502641094447802959518661)
                ·
                  refine ⟨5719245205208963054909749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30502641094447802959518661 5719245205208963054909749)
                  ·
                    refine ⟨536179237988340286397789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5719245205208963054909749 536179237988340286397789)
                    ·
                      rfl

theorem cell23_3132616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_3132616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132616 prefixEnd_3132616 := by exact prefixLift 3132616
  have htrace : WordTrace (prefixWord ++ tailWord_3132616) baseStart_3132616 baseEnd_3132616 := by
    simpa [prefixWord, tailWord_3132616, baseEnd_3132616] using wordTrace_append hprefix tailTrace_3132616
  have hstable : (prefixWord ++ tailWord_3132616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132616).length < 2 ^ (prefixWord ++ tailWord_3132616).sum := by decide
  have hdescent : baseEnd_3132616 < baseStart_3132616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132637 : List Nat := [1, 4, 3, 2, 2, 1, 2, 3, 5]
def baseStart_3132637 : Nat := 118140960795 + 3132637 * 2 ^ 59
def prefixEnd_3132637 : Nat := 4983230072969 + 3 ^ 40 * 3132637 * 2
def baseEnd_3132637 : Nat := 178727610784307253003419

theorem tailTrace_3132637 : CollatzResearch.WordTrace tailWord_3132637 prefixEnd_3132637 178727610784307253003419 := by
  unfold tailWord_3132637
  simp only [CollatzResearch.WordTrace]
  refine ⟨114256657951998635650244165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76171105301332423766829443 114256657951998635650244165)
  ·
    refine ⟨21423123365999744184420781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114256657951998635650244165 21423123365999744184420781)
    ·
      refine ⟨8033671262249904069157793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21423123365999744184420781 8033671262249904069157793)
      ·
        refine ⟨6025253446687428051868345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8033671262249904069157793 6025253446687428051868345)
        ·
          refine ⟨4518940085015571038901259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6025253446687428051868345 4518940085015571038901259)
          ·
            refine ⟨6778410127523356558351889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518940085015571038901259 6778410127523356558351889)
            ·
              refine ⟨5083807595642517418763917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6778410127523356558351889 5083807595642517418763917)
              ·
                refine ⟨1906427848365944032036469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5083807595642517418763917 1906427848365944032036469)
                ·
                  refine ⟨178727610784307253003419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1906427848365944032036469 178727610784307253003419)
                  ·
                    rfl

theorem cell23_3132637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_3132637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132637 prefixEnd_3132637 := by exact prefixLift 3132637
  have htrace : WordTrace (prefixWord ++ tailWord_3132637) baseStart_3132637 baseEnd_3132637 := by
    simpa [prefixWord, tailWord_3132637, baseEnd_3132637] using wordTrace_append hprefix tailTrace_3132637
  have hstable : (prefixWord ++ tailWord_3132637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132637).length < 2 ^ (prefixWord ++ tailWord_3132637).sum := by decide
  have hdescent : baseEnd_3132637 < baseStart_3132637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132666 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_3132666 : Nat := 118140960795 + 3132666 * 2 ^ 59
def prefixEnd_3132666 : Nat := 4983230072969 + 3 ^ 40 * 3132666 * 2
def baseEnd_3132666 : Nat := 1608563387997745663568137

theorem tailTrace_3132666 : CollatzResearch.WordTrace tailWord_3132666 prefixEnd_3132666 1608563387997745663568137 := by
  unfold tailWord_3132666
  simp only [CollatzResearch.WordTrace]
  refine ⟨28564428917223393400762463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76171810445929049068699901 28564428917223393400762463)
  ·
    refine ⟨42846643375835090101143695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28564428917223393400762463 42846643375835090101143695)
    ·
      refine ⟨64269965063752635151715543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42846643375835090101143695 64269965063752635151715543)
      ·
        refine ⟨96404947595628952727573315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64269965063752635151715543 96404947595628952727573315)
        ·
          refine ⟨144607421393443429091359973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96404947595628952727573315 144607421393443429091359973)
          ·
            refine ⟨27113891511270642954629995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144607421393443429091359973 27113891511270642954629995)
            ·
              refine ⟨40670837266905964431944993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27113891511270642954629995 40670837266905964431944993)
              ·
                refine ⟨30503127950179473323958745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40670837266905964431944993 30503127950179473323958745)
                ·
                  refine ⟨22877345962634604992969059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30503127950179473323958745 22877345962634604992969059)
                  ·
                    refine ⟨34316018943951907489453589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22877345962634604992969059 34316018943951907489453589)
                    ·
                      refine ⟨1608563387997745663568137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34316018943951907489453589 1608563387997745663568137)
                      ·
                        rfl

theorem cell23_3132666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_3132666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132666 prefixEnd_3132666 := by exact prefixLift 3132666
  have htrace : WordTrace (prefixWord ++ tailWord_3132666) baseStart_3132666 baseEnd_3132666 := by
    simpa [prefixWord, tailWord_3132666, baseEnd_3132666] using wordTrace_append hprefix tailTrace_3132666
  have hstable : (prefixWord ++ tailWord_3132666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132666).length < 2 ^ (prefixWord ++ tailWord_3132666).sum := by decide
  have hdescent : baseEnd_3132666 < baseStart_3132666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132673 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_3132673 : Nat := 118140960795 + 3132673 * 2 ^ 59
def prefixEnd_3132673 : Nat := 4983230072969 + 3 ^ 40 * 3132673 * 2
def baseEnd_3132673 : Nat := 1608566982362327136180605

theorem tailTrace_3132673 : CollatzResearch.WordTrace tailWord_3132673 prefixEnd_3132673 1608566982362327136180605 := by
  unfold tailWord_3132673
  simp only [CollatzResearch.WordTrace]
  refine ⟨114257970979868213798554673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76171980653245475865703115 114257970979868213798554673)
  ·
    refine ⟨85693478234901160348916005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114257970979868213798554673 85693478234901160348916005)
    ·
      refine ⟨16067527169043967565421751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85693478234901160348916005 16067527169043967565421751)
      ·
        refine ⟨24101290753565951348132627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16067527169043967565421751 24101290753565951348132627)
        ·
          refine ⟨36151936130348927022198941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24101290753565951348132627 36151936130348927022198941)
          ·
            refine ⟨13556976048880847633324603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36151936130348927022198941 13556976048880847633324603)
            ·
              refine ⟨20335464073321271449986905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13556976048880847633324603 20335464073321271449986905)
              ·
                refine ⟨15251598054990953587490179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20335464073321271449986905 15251598054990953587490179)
                ·
                  refine ⟨22877397082486430381235269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15251598054990953587490179 22877397082486430381235269)
                  ·
                    refine ⟨4289511952966205696481613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22877397082486430381235269 4289511952966205696481613)
                    ·
                      refine ⟨1608566982362327136180605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4289511952966205696481613 1608566982362327136180605)
                      ·
                        rfl

theorem cell23_3132673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_3132673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132673 prefixEnd_3132673 := by exact prefixLift 3132673
  have htrace : WordTrace (prefixWord ++ tailWord_3132673) baseStart_3132673 baseEnd_3132673 := by
    simpa [prefixWord, tailWord_3132673, baseEnd_3132673] using wordTrace_append hprefix tailTrace_3132673
  have hstable : (prefixWord ++ tailWord_3132673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132673).length < 2 ^ (prefixWord ++ tailWord_3132673).sum := by decide
  have hdescent : baseEnd_3132673 < baseStart_3132673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132716 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_3132716 : Nat := 118140960795 + 3132716 * 2 ^ 59
def prefixEnd_3132716 : Nat := 4983230072969 + 3 ^ 40 * 3132716 * 2
def baseEnd_3132716 : Nat := 1608589062030470467942907

theorem tailTrace_3132716 : CollatzResearch.WordTrace tailWord_3132716 prefixEnd_3132716 1608589062030470467942907 := by
  unfold tailWord_3132716
  simp only [CollatzResearch.WordTrace]
  refine ⟨57129769659356216071185001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76173026212474954761580001 57129769659356216071185001)
  ·
    refine ⟨42847327244517162053388751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57129769659356216071185001 42847327244517162053388751)
    ·
      refine ⟨64270990866775743080083127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42847327244517162053388751 64270990866775743080083127)
      ·
        refine ⟨96406486300163614620124691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64270990866775743080083127 96406486300163614620124691)
        ·
          refine ⟨144609729450245421930187037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96406486300163614620124691 144609729450245421930187037)
          ·
            refine ⟨54228648543842033223820139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144609729450245421930187037 54228648543842033223820139)
            ·
              refine ⟨81342972815763049835730209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54228648543842033223820139 81342972815763049835730209)
              ·
                refine ⟨61007229611822287376797657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81342972815763049835730209 61007229611822287376797657)
                ·
                  refine ⟨45755422208866715532598243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61007229611822287376797657 45755422208866715532598243)
                  ·
                    refine ⟨68633133313300073298897365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45755422208866715532598243 68633133313300073298897365)
                    ·
                      refine ⟨1608589062030470467942907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68633133313300073298897365 1608589062030470467942907)
                      ·
                        rfl

theorem cell23_3132716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_3132716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132716 prefixEnd_3132716 := by exact prefixLift 3132716
  have htrace : WordTrace (prefixWord ++ tailWord_3132716) baseStart_3132716 baseEnd_3132716 := by
    simpa [prefixWord, tailWord_3132716, baseEnd_3132716] using wordTrace_append hprefix tailTrace_3132716
  have hstable : (prefixWord ++ tailWord_3132716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132716).length < 2 ^ (prefixWord ++ tailWord_3132716).sum := by decide
  have hdescent : baseEnd_3132716 < baseStart_3132716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132730 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2]
def baseStart_3132730 : Nat := 118140960795 + 3132730 * 2 ^ 59
def prefixEnd_3132730 : Nat := 4983230072969 + 3 ^ 40 * 3132730 * 2
def baseEnd_3132730 : Nat := 1608596250759633413167843

theorem tailTrace_3132730 : CollatzResearch.WordTrace tailWord_3132730 prefixEnd_3132730 1608596250759633413167843 := by
  unfold tailWord_3132730
  simp only [CollatzResearch.WordTrace]
  refine ⟨28565012485165428133344911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76173366627107808355586429 28565012485165428133344911)
  ·
    refine ⟨42847518727748142200017367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28565012485165428133344911 42847518727748142200017367)
    ·
      refine ⟨64271278091622213300026051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42847518727748142200017367 64271278091622213300026051)
      ·
        refine ⟨96406917137433319950039077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64271278091622213300026051 96406917137433319950039077)
        ·
          refine ⟨18076296963268747490632327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96406917137433319950039077 18076296963268747490632327)
          ·
            refine ⟨27114445444903121235948491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18076296963268747490632327 27114445444903121235948491)
            ·
              refine ⟨40671668167354681853922737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27114445444903121235948491 40671668167354681853922737)
              ·
                refine ⟨30503751125516011390442053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40671668167354681853922737 30503751125516011390442053)
                ·
                  refine ⟨5719453336034252135707885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30503751125516011390442053 5719453336034252135707885)
                  ·
                    refine ⟨2144795001012844550890457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5719453336034252135707885 2144795001012844550890457)
                    ·
                      refine ⟨1608596250759633413167843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2144795001012844550890457 1608596250759633413167843)
                      ·
                        rfl

theorem cell23_3132730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2].length) (baseStart_3132730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132730 prefixEnd_3132730 := by exact prefixLift 3132730
  have htrace : WordTrace (prefixWord ++ tailWord_3132730) baseStart_3132730 baseEnd_3132730 := by
    simpa [prefixWord, tailWord_3132730, baseEnd_3132730] using wordTrace_append hprefix tailTrace_3132730
  have hstable : (prefixWord ++ tailWord_3132730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132730).length < 2 ^ (prefixWord ++ tailWord_3132730).sum := by decide
  have hdescent : baseEnd_3132730 < baseStart_3132730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132753 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 1, 6]
def baseStart_3132753 : Nat := 118140960795 + 3132753 * 2 ^ 59
def prefixEnd_3132753 : Nat := 4983230072969 + 3 ^ 40 * 3132753 * 2
def baseEnd_3132753 : Nat := 536202686938228941060079

theorem tailTrace_3132753 : CollatzResearch.WordTrace tailWord_3132753 prefixEnd_3132753 536202686938228941060079 := by
  unfold tailWord_3132753
  simp only [CollatzResearch.WordTrace]
  refine ⟨114260888819578387461466913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76173925879718924974311275 114260888819578387461466913)
  ·
    refine ⟨85695666614683790596100185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114260888819578387461466913 85695666614683790596100185)
    ·
      refine ⟨64271749961012842947075139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85695666614683790596100185 64271749961012842947075139)
      ·
        refine ⟨96407624941519264420612709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64271749961012842947075139 96407624941519264420612709)
        ·
          refine ⟨18076429676534862078864883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96407624941519264420612709 18076429676534862078864883)
          ·
            refine ⟨27114644514802293118297325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18076429676534862078864883 27114644514802293118297325)
            ·
              refine ⟨10167991693050859919361497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27114644514802293118297325 10167991693050859919361497)
              ·
                refine ⟨7625993769788144939521123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10167991693050859919361497 7625993769788144939521123)
                ·
                  refine ⟨11438990654682217409281685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7625993769788144939521123 11438990654682217409281685)
                  ·
                    refine ⟨536202686938228941060079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11438990654682217409281685 536202686938228941060079)
                    ·
                      rfl

theorem cell23_3132753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_3132753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132753 prefixEnd_3132753 := by exact prefixLift 3132753
  have htrace : WordTrace (prefixWord ++ tailWord_3132753) baseStart_3132753 baseEnd_3132753 := by
    simpa [prefixWord, tailWord_3132753, baseEnd_3132753] using wordTrace_append hprefix tailTrace_3132753
  have hstable : (prefixWord ++ tailWord_3132753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132753).length < 2 ^ (prefixWord ++ tailWord_3132753).sum := by decide
  have hdescent : baseEnd_3132753 < baseStart_3132753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132757 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 1, 5]
def baseStart_3132757 : Nat := 118140960795 + 3132757 * 2 ^ 59
def prefixEnd_3132757 : Nat := 4983230072969 + 3 ^ 40 * 3132757 * 2
def baseEnd_3132757 : Nat := 536203371579101602510073

theorem tailTrace_3132757 : CollatzResearch.WordTrace tailWord_3132757 prefixEnd_3132757 536203371579101602510073 := by
  unfold tailWord_3132757
  simp only [CollatzResearch.WordTrace]
  refine ⟨114261034711563896144612525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76174023141042597429741683 114261034711563896144612525)
  ·
    refine ⟨42847888016836461054229697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114261034711563896144612525 42847888016836461054229697)
    ·
      refine ⟨32135916012627345790672273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42847888016836461054229697 32135916012627345790672273)
      ·
        refine ⟨24101937009470509343004205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32135916012627345790672273 24101937009470509343004205)
        ·
          refine ⟨9038226378551441003626577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24101937009470509343004205 9038226378551441003626577)
          ·
            refine ⟨6778669783913580752719933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9038226378551441003626577 6778669783913580752719933)
            ·
              refine ⟨2542001168967592782269975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6778669783913580752719933 2542001168967592782269975)
              ·
                refine ⟨3813001753451389173404963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542001168967592782269975 3813001753451389173404963)
                ·
                  refine ⟨5719502630177083760107445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813001753451389173404963 5719502630177083760107445)
                  ·
                    refine ⟨536203371579101602510073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5719502630177083760107445 536203371579101602510073)
                    ·
                      rfl

theorem cell23_3132757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_3132757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132757 prefixEnd_3132757 := by exact prefixLift 3132757
  have htrace : WordTrace (prefixWord ++ tailWord_3132757) baseStart_3132757 baseEnd_3132757 := by
    simpa [prefixWord, tailWord_3132757, baseEnd_3132757] using wordTrace_append hprefix tailTrace_3132757
  have hstable : (prefixWord ++ tailWord_3132757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132757).length < 2 ^ (prefixWord ++ tailWord_3132757).sum := by decide
  have hdescent : baseEnd_3132757 < baseStart_3132757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132765 : List Nat := [1, 4, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3132765 : Nat := 118140960795 + 3132765 * 2 ^ 59
def prefixEnd_3132765 : Nat := 4983230072969 + 3 ^ 40 * 3132765 * 2
def baseEnd_3132765 : Nat := 536204740860846925410061

theorem tailTrace_3132765 : CollatzResearch.WordTrace tailWord_3132765 prefixEnd_3132765 536204740860846925410061 := by
  unfold tailWord_3132765
  simp only [CollatzResearch.WordTrace]
  refine ⟨114261326495534913510903749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76174217663689942340602499 114261326495534913510903749)
  ·
    refine ⟨21423998717912796283294453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114261326495534913510903749 21423998717912796283294453)
    ·
      refine ⟨2008499879804324651558855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21423998717912796283294453 2008499879804324651558855)
      ·
        refine ⟨3012749819706486977338283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008499879804324651558855 3012749819706486977338283)
        ·
          refine ⟨4519124729559730466007425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012749819706486977338283 4519124729559730466007425)
          ·
            refine ⟨3389343547169797849505569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4519124729559730466007425 3389343547169797849505569)
            ·
              refine ⟨2542007660377348387129177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3389343547169797849505569 2542007660377348387129177)
              ·
                refine ⟨1906505745283011290346883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2542007660377348387129177 1906505745283011290346883)
                ·
                  refine ⟨2859758617924516935520325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906505745283011290346883 2859758617924516935520325)
                  ·
                    refine ⟨536204740860846925410061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2859758617924516935520325 536204740860846925410061)
                    ·
                      rfl

theorem cell23_3132765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3132765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132765 prefixEnd_3132765 := by exact prefixLift 3132765
  have htrace : WordTrace (prefixWord ++ tailWord_3132765) baseStart_3132765 baseEnd_3132765 := by
    simpa [prefixWord, tailWord_3132765, baseEnd_3132765] using wordTrace_append hprefix tailTrace_3132765
  have hstable : (prefixWord ++ tailWord_3132765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132765).length < 2 ^ (prefixWord ++ tailWord_3132765).sum := by decide
  have hdescent : baseEnd_3132765 < baseStart_3132765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132771 : List Nat := [1, 1, 1, 5, 2, 4, 2, 2, 1, 1, 3]
def baseStart_3132771 : Nat := 118140960795 + 3132771 * 2 ^ 59
def prefixEnd_3132771 : Nat := 4983230072969 + 3 ^ 40 * 3132771 * 2
def baseEnd_3132771 : Nat := 1608617303466467752755155

theorem tailTrace_3132771 : CollatzResearch.WordTrace tailWord_3132771 prefixEnd_3132771 1608617303466467752755155 := by
  unfold tailWord_3132771
  simp only [CollatzResearch.WordTrace]
  refine ⟨114261545333513176535622167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76174363555675451023748111 114261545333513176535622167)
  ·
    refine ⟨171392318000269764803433251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114261545333513176535622167 171392318000269764803433251)
    ·
      refine ⟨257088477000404647205149877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171392318000269764803433251 257088477000404647205149877)
      ·
        refine ⟨24102044718787935675482801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257088477000404647205149877 24102044718787935675482801)
        ·
          refine ⟨18076533539090951756612101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24102044718787935675482801 18076533539090951756612101)
          ·
            refine ⟨3389350038579553454364769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18076533539090951756612101 3389350038579553454364769)
            ·
              refine ⟨2542012528934665090773577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3389350038579553454364769 2542012528934665090773577)
              ·
                refine ⟨1906509396700998818080183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2542012528934665090773577 1906509396700998818080183)
                ·
                  refine ⟨2859764095051498227120275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906509396700998818080183 2859764095051498227120275)
                  ·
                    refine ⟨4289646142577247340680413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2859764095051498227120275 4289646142577247340680413)
                    ·
                      refine ⟨1608617303466467752755155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4289646142577247340680413 1608617303466467752755155)
                      ·
                        rfl

theorem cell23_3132771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_3132771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132771 prefixEnd_3132771 := by exact prefixLift 3132771
  have htrace : WordTrace (prefixWord ++ tailWord_3132771) baseStart_3132771 baseEnd_3132771 := by
    simpa [prefixWord, tailWord_3132771, baseEnd_3132771] using wordTrace_append hprefix tailTrace_3132771
  have hstable : (prefixWord ++ tailWord_3132771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132771).length < 2 ^ (prefixWord ++ tailWord_3132771).sum := by decide
  have hdescent : baseEnd_3132771 < baseStart_3132771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132773 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_3132773 : Nat := 118140960795 + 3132773 * 2 ^ 59
def prefixEnd_3132773 : Nat := 4983230072969 + 3 ^ 40 * 3132773 * 2
def baseEnd_3132773 : Nat := 1608618330427776744930145

theorem tailTrace_3132773 : CollatzResearch.WordTrace tailWord_3132773 prefixEnd_3132773 1608618330427776744930145 := by
  unfold tailWord_3132773
  simp only [CollatzResearch.WordTrace]
  refine ⟨114261618279505930877194973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76174412186337287251463315 114261618279505930877194973)
  ·
    refine ⟨42848106854814724078948115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114261618279505930877194973 42848106854814724078948115)
    ·
      refine ⟨64272160282222086118422173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42848106854814724078948115 64272160282222086118422173)
      ·
        refine ⟨24102060105833282294408315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64272160282222086118422173 24102060105833282294408315)
        ·
          refine ⟨36153090158749923441612473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24102060105833282294408315 36153090158749923441612473)
          ·
            refine ⟨27114817619062442581209355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36153090158749923441612473 27114817619062442581209355)
            ·
              refine ⟨40672226428593663871814033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27114817619062442581209355 40672226428593663871814033)
              ·
                refine ⟨30504169821445247903860525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40672226428593663871814033 30504169821445247903860525)
                ·
                  refine ⟨11439063683041967963947697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30504169821445247903860525 11439063683041967963947697)
                  ·
                    refine ⟨8579297762281475972960773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11439063683041967963947697 8579297762281475972960773)
                    ·
                      refine ⟨1608618330427776744930145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8579297762281475972960773 1608618330427776744930145)
                      ·
                        rfl

theorem cell23_3132773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_3132773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132773 prefixEnd_3132773 := by exact prefixLift 3132773
  have htrace : WordTrace (prefixWord ++ tailWord_3132773) baseStart_3132773 baseEnd_3132773 := by
    simpa [prefixWord, tailWord_3132773, baseEnd_3132773] using wordTrace_append hprefix tailTrace_3132773
  have hstable : (prefixWord ++ tailWord_3132773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132773).length < 2 ^ (prefixWord ++ tailWord_3132773).sum := by decide
  have hdescent : baseEnd_3132773 < baseStart_3132773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132780 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 3]
def baseStart_3132780 : Nat := 118140960795 + 3132780 * 2 ^ 59
def prefixEnd_3132780 : Nat := 4983230072969 + 3 ^ 40 * 3132780 * 2
def baseEnd_3132780 : Nat := 1608621924792358217542613

theorem tailTrace_3132780 : CollatzResearch.WordTrace tailWord_3132780 prefixEnd_3132780 1608621924792358217542613 := by
  unfold tailWord_3132780
  simp only [CollatzResearch.WordTrace]
  refine ⟨57130936795240285536349897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76174582393653714048466529 57130936795240285536349897)
  ·
    refine ⟨42848202596430214152262423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57130936795240285536349897 42848202596430214152262423)
    ·
      refine ⟨64272303894645321228393635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42848202596430214152262423 64272303894645321228393635)
      ·
        refine ⟨96408455841967981842590453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64272303894645321228393635 96408455841967981842590453)
        ·
          refine ⟨9038292735184498297742855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96408455841967981842590453 9038292735184498297742855)
          ·
            refine ⟨13557439102776747446614283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9038292735184498297742855 13557439102776747446614283)
            ·
              refine ⟨20336158654165121169921425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13557439102776747446614283 20336158654165121169921425)
              ·
                refine ⟨15252118990623840877441069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20336158654165121169921425 15252118990623840877441069)
                ·
                  refine ⟨5719544621483940329040401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15252118990623840877441069 5719544621483940329040401)
                  ·
                    refine ⟨4289658466112955246780301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5719544621483940329040401 4289658466112955246780301)
                    ·
                      refine ⟨1608621924792358217542613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4289658466112955246780301 1608621924792358217542613)
                      ·
                        rfl

theorem cell23_3132780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_3132780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132780 prefixEnd_3132780 := by exact prefixLift 3132780
  have htrace : WordTrace (prefixWord ++ tailWord_3132780) baseStart_3132780 baseEnd_3132780 := by
    simpa [prefixWord, tailWord_3132780, baseEnd_3132780] using wordTrace_append hprefix tailTrace_3132780
  have hstable : (prefixWord ++ tailWord_3132780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132780).length < 2 ^ (prefixWord ++ tailWord_3132780).sum := by decide
  have hdescent : baseEnd_3132780 < baseStart_3132780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132798 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3132798 : Nat := 118140960795 + 3132798 * 2 ^ 59
def prefixEnd_3132798 : Nat := 4983230072969 + 3 ^ 40 * 3132798 * 2
def baseEnd_3132798 : Nat := 1608631167444139147117531

theorem tailTrace_3132798 : CollatzResearch.WordTrace tailWord_3132798 prefixEnd_3132798 1608631167444139147117531 := by
  unfold tailWord_3132798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14282816263051920018356881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76175020069610240097903365 14282816263051920018356881)
  ·
    refine ⟨10712112197288940013767661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14282816263051920018356881 10712112197288940013767661)
    ·
      refine ⟨4017042073983352505162873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10712112197288940013767661 4017042073983352505162873)
      ·
        refine ⟨3012781555487514378872155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4017042073983352505162873 3012781555487514378872155)
        ·
          refine ⟨4519172333231271568308233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012781555487514378872155 4519172333231271568308233)
          ·
            refine ⟨3389379249923453676231175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4519172333231271568308233 3389379249923453676231175)
            ·
              refine ⟨5084068874885180514346763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389379249923453676231175 5084068874885180514346763)
              ·
                refine ⟨7626103312327770771520145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5084068874885180514346763 7626103312327770771520145)
                ·
                  refine ⟨5719577484245828078640109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7626103312327770771520145 5719577484245828078640109)
                  ·
                    refine ⟨2144841556592185529490041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5719577484245828078640109 2144841556592185529490041)
                    ·
                      refine ⟨1608631167444139147117531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2144841556592185529490041 1608631167444139147117531)
                      ·
                        rfl

theorem cell23_3132798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3132798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132798 prefixEnd_3132798 := by exact prefixLift 3132798
  have htrace : WordTrace (prefixWord ++ tailWord_3132798) baseStart_3132798 baseEnd_3132798 := by
    simpa [prefixWord, tailWord_3132798, baseEnd_3132798] using wordTrace_append hprefix tailTrace_3132798
  have hstable : (prefixWord ++ tailWord_3132798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132798).length < 2 ^ (prefixWord ++ tailWord_3132798).sum := by decide
  have hdescent : baseEnd_3132798 < baseStart_3132798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132814 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3132814 : Nat := 118140960795 + 3132814 * 2 ^ 59
def prefixEnd_3132814 : Nat := 4983230072969 + 3 ^ 40 * 3132814 * 2
def baseEnd_3132814 : Nat := 1608639383134611084517457

theorem tailTrace_3132814 : CollatzResearch.WordTrace tailWord_3132814 prefixEnd_3132814 1608639383134611084517457 := by
  unfold tailWord_3132814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14282889209044674359929687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76175409114904929919624997 14282889209044674359929687)
  ·
    refine ⟨21424333813567011539894531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14282889209044674359929687 21424333813567011539894531)
    ·
      refine ⟨32136500720350517309841797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21424333813567011539894531 32136500720350517309841797)
      ·
        refine ⟨6025593885065721995595337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32136500720350517309841797 6025593885065721995595337)
        ·
          refine ⟨4519195413799291496696503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6025593885065721995595337 4519195413799291496696503)
          ·
            refine ⟨6778793120698937245044755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4519195413799291496696503 6778793120698937245044755)
            ·
              refine ⟨10168189681048405867567133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6778793120698937245044755 10168189681048405867567133)
              ·
                refine ⟨3813071130393152200337675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10168189681048405867567133 3813071130393152200337675)
                ·
                  refine ⟨5719606695589728300506513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813071130393152200337675 5719606695589728300506513)
                  ·
                    refine ⟨4289705021692296225379885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5719606695589728300506513 4289705021692296225379885)
                    ·
                      refine ⟨1608639383134611084517457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4289705021692296225379885 1608639383134611084517457)
                      ·
                        rfl

theorem cell23_3132814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3132814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132814 prefixEnd_3132814 := by exact prefixLift 3132814
  have htrace : WordTrace (prefixWord ++ tailWord_3132814) baseStart_3132814 baseEnd_3132814 := by
    simpa [prefixWord, tailWord_3132814, baseEnd_3132814] using wordTrace_append hprefix tailTrace_3132814
  have hstable : (prefixWord ++ tailWord_3132814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132814).length < 2 ^ (prefixWord ++ tailWord_3132814).sum := by decide
  have hdescent : baseEnd_3132814 < baseStart_3132814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132863 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 4]
def baseStart_3132863 : Nat := 118140960795 + 3132863 * 2 ^ 59
def prefixEnd_3132863 : Nat := 4983230072969 + 3 ^ 40 * 3132863 * 2
def baseEnd_3132863 : Nat := 1608664543686681392804731

theorem tailTrace_3132863 : CollatzResearch.WordTrace tailWord_3132863 prefixEnd_3132863 1608664543686681392804731 := by
  unfold tailWord_3132863
  simp only [CollatzResearch.WordTrace]
  refine ⟨114264900849179876247971243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76176600566119917498647495 114264900849179876247971243)
  ·
    refine ⟨171397351273769814371956865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114264900849179876247971243 171397351273769814371956865)
    ·
      refine ⟨128548013455327360778967649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171397351273769814371956865 128548013455327360778967649)
      ·
        refine ⟨96411010091495520584225737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128548013455327360778967649 96411010091495520584225737)
        ·
          refine ⟨72308257568621640438169303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96411010091495520584225737 72308257568621640438169303)
          ·
            refine ⟨108462386352932460657253955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72308257568621640438169303 108462386352932460657253955)
            ·
              refine ⟨162693579529398690985880933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108462386352932460657253955 162693579529398690985880933)
              ·
                refine ⟨30505046161762254559852675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162693579529398690985880933 30505046161762254559852675)
                ·
                  refine ⟨45757569242643381839779013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30505046161762254559852675 45757569242643381839779013)
                  ·
                    refine ⟨8579544232995634094958565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45757569242643381839779013 8579544232995634094958565)
                    ·
                      refine ⟨1608664543686681392804731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8579544232995634094958565 1608664543686681392804731)
                      ·
                        rfl

theorem cell23_3132863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_3132863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132863 prefixEnd_3132863 := by exact prefixLift 3132863
  have htrace : WordTrace (prefixWord ++ tailWord_3132863) baseStart_3132863 baseEnd_3132863 := by
    simpa [prefixWord, tailWord_3132863, baseEnd_3132863] using wordTrace_append hprefix tailTrace_3132863
  have hstable : (prefixWord ++ tailWord_3132863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132863).length < 2 ^ (prefixWord ++ tailWord_3132863).sum := by decide
  have hdescent : baseEnd_3132863 < baseStart_3132863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132867 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 4, 2, 2]
def baseStart_3132867 : Nat := 118140960795 + 3132867 * 2 ^ 59
def prefixEnd_3132867 : Nat := 4983230072969 + 3 ^ 40 * 3132867 * 2
def baseEnd_3132867 : Nat := 1608666597609299377154713

theorem tailTrace_3132867 : CollatzResearch.WordTrace tailWord_3132867 prefixEnd_3132867 1608666597609299377154713 := by
  unfold tailWord_3132867
  simp only [CollatzResearch.WordTrace]
  refine ⟨114265046741165384931116855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76176697827443589954077903 114265046741165384931116855)
  ·
    refine ⟨171397570111748077396675283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114265046741165384931116855 171397570111748077396675283)
    ·
      refine ⟨257096355167622116095012925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171397570111748077396675283 257096355167622116095012925)
      ·
        refine ⟨96411133187858293535629847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257096355167622116095012925 96411133187858293535629847)
        ·
          refine ⟨144616699781787440303444771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96411133187858293535629847 144616699781787440303444771)
          ·
            refine ⟨216925049672681160455167157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144616699781787440303444771 216925049672681160455167157)
            ·
              refine ⟨20336723406813858792671921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216925049672681160455167157 20336723406813858792671921)
              ·
                refine ⟨15252542555110394094503941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20336723406813858792671921 15252542555110394094503941)
                ·
                  refine ⟨2859851729083198892719489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15252542555110394094503941 2859851729083198892719489)
                  ·
                    refine ⟨2144888796812399169539617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2859851729083198892719489 2144888796812399169539617)
                    ·
                      refine ⟨1608666597609299377154713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2144888796812399169539617 1608666597609299377154713)
                      ·
                        rfl

theorem cell23_3132867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 2, 2].length) (baseStart_3132867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132867 prefixEnd_3132867 := by exact prefixLift 3132867
  have htrace : WordTrace (prefixWord ++ tailWord_3132867) baseStart_3132867 baseEnd_3132867 := by
    simpa [prefixWord, tailWord_3132867, baseEnd_3132867] using wordTrace_append hprefix tailTrace_3132867
  have hstable : (prefixWord ++ tailWord_3132867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132867).length < 2 ^ (prefixWord ++ tailWord_3132867).sum := by decide
  have hdescent : baseEnd_3132867 < baseStart_3132867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132890 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 7]
def baseStart_3132890 : Nat := 118140960795 + 3132890 * 2 ^ 59
def prefixEnd_3132890 : Nat := 4983230072969 + 3 ^ 40 * 3132890 * 2
def baseEnd_3132890 : Nat := 178742045296039198574123

theorem tailTrace_3132890 : CollatzResearch.WordTrace tailWord_3132890 prefixEnd_3132890 178742045296039198574123 := by
  unfold tailWord_3132890
  simp only [CollatzResearch.WordTrace]
  refine ⟨28566471405020514964801031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76177257080054706572802749 28566471405020514964801031)
  ·
    refine ⟨42849707107530772447201547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28566471405020514964801031 42849707107530772447201547)
    ·
      refine ⟨64274560661296158670802321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42849707107530772447201547 64274560661296158670802321)
      ·
        refine ⟨48205920495972119003101741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64274560661296158670802321 48205920495972119003101741)
        ·
          refine ⟨18077220185989544626163153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48205920495972119003101741 18077220185989544626163153)
          ·
            refine ⟨13557915139492158469622365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18077220185989544626163153 13557915139492158469622365)
            ·
              refine ⟨5084218177309559426108387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13557915139492158469622365 5084218177309559426108387)
              ·
                refine ⟨7626327265964339139162581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5084218177309559426108387 7626327265964339139162581)
                ·
                  refine ⟨178742045296039198574123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7626327265964339139162581 178742045296039198574123)
                  ·
                    rfl

theorem cell23_3132890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_3132890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132890 prefixEnd_3132890 := by exact prefixLift 3132890
  have htrace : WordTrace (prefixWord ++ tailWord_3132890) baseStart_3132890 baseEnd_3132890 := by
    simpa [prefixWord, tailWord_3132890, baseEnd_3132890] using wordTrace_append hprefix tailTrace_3132890
  have hstable : (prefixWord ++ tailWord_3132890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132890).length < 2 ^ (prefixWord ++ tailWord_3132890).sum := by decide
  have hdescent : baseEnd_3132890 < baseStart_3132890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132900 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_3132900 : Nat := 118140960795 + 3132900 * 2 ^ 59
def prefixEnd_3132900 : Nat := 4983230072969 + 3 ^ 40 * 3132900 * 2
def baseEnd_3132900 : Nat := 1608683542470897748042061

theorem tailTrace_3132900 : CollatzResearch.WordTrace tailWord_3132900 prefixEnd_3132900 1608683542470897748042061 := by
  unfold tailWord_3132900
  simp only [CollatzResearch.WordTrace]
  refine ⟨57133125175022915783534077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76177500233363887711378769 57133125175022915783534077)
  ·
    refine ⟨21424921940633593418825279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57133125175022915783534077 21424921940633593418825279)
    ·
      refine ⟨32137382910950390128237919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21424921940633593418825279 32137382910950390128237919)
      ·
        refine ⟨48206074366425585192356879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32137382910950390128237919 48206074366425585192356879)
        ·
          refine ⟨72309111549638377788535319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48206074366425585192356879 72309111549638377788535319)
          ·
            refine ⟨108463667324457566682802979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72309111549638377788535319 108463667324457566682802979)
            ·
              refine ⟨162695500986686350024204469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108463667324457566682802979 162695500986686350024204469)
              ·
                refine ⟨15252703217501845314769169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162695500986686350024204469 15252703217501845314769169)
                ·
                  refine ⟨11439527413126383986076877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15252703217501845314769169 11439527413126383986076877)
                  ·
                    refine ⟨4289822779922393994778829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11439527413126383986076877 4289822779922393994778829)
                    ·
                      refine ⟨1608683542470897748042061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4289822779922393994778829 1608683542470897748042061)
                      ·
                        rfl

theorem cell23_3132900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_3132900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132900 prefixEnd_3132900 := by exact prefixLift 3132900
  have htrace : WordTrace (prefixWord ++ tailWord_3132900) baseStart_3132900 baseEnd_3132900 := by
    simpa [prefixWord, tailWord_3132900, baseEnd_3132900] using wordTrace_append hprefix tailTrace_3132900
  have hstable : (prefixWord ++ tailWord_3132900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132900).length < 2 ^ (prefixWord ++ tailWord_3132900).sum := by decide
  have hdescent : baseEnd_3132900 < baseStart_3132900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132901 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 2, 2, 2]
def baseStart_3132901 : Nat := 118140960795 + 3132901 * 2 ^ 59
def prefixEnd_3132901 : Nat := 4983230072969 + 3 ^ 40 * 3132901 * 2
def baseEnd_3132901 : Nat := 1608684055951552244129557

theorem tailTrace_3132901 : CollatzResearch.WordTrace tailWord_3132901 prefixEnd_3132901 1608684055951552244129557 := by
  unfold tailWord_3132901
  simp only [CollatzResearch.WordTrace]
  refine ⟨114266286823042208737854557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76177524548694805825236371 114266286823042208737854557)
  ·
    refine ⟨42849857558640828276695459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114266286823042208737854557 42849857558640828276695459)
    ·
      refine ⟨64274786337961242415043189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42849857558640828276695459 64274786337961242415043189)
      ·
        refine ⟨6025761219183866476410299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64274786337961242415043189 6025761219183866476410299)
        ·
          refine ⟨9038641828775799714615449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6025761219183866476410299 9038641828775799714615449)
          ·
            refine ⟨6778981371581849785961587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9038641828775799714615449 6778981371581849785961587)
            ·
              refine ⟨10168472057372774678942381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6778981371581849785961587 10168472057372774678942381)
              ·
                refine ⟨3813177021514790504603393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10168472057372774678942381 3813177021514790504603393)
                ·
                  refine ⟨2859882766136092878452545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3813177021514790504603393 2859882766136092878452545)
                  ·
                    refine ⟨2144912074602069658839409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2859882766136092878452545 2144912074602069658839409)
                    ·
                      refine ⟨1608684055951552244129557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2144912074602069658839409 1608684055951552244129557)
                      ·
                        rfl

theorem cell23_3132901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_3132901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132901 prefixEnd_3132901 := by exact prefixLift 3132901
  have htrace : WordTrace (prefixWord ++ tailWord_3132901) baseStart_3132901 baseEnd_3132901 := by
    simpa [prefixWord, tailWord_3132901, baseEnd_3132901] using wordTrace_append hprefix tailTrace_3132901
  have hstable : (prefixWord ++ tailWord_3132901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132901).length < 2 ^ (prefixWord ++ tailWord_3132901).sum := by decide
  have hdescent : baseEnd_3132901 < baseStart_3132901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132920 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 2, 5]
def baseStart_3132920 : Nat := 118140960795 + 3132920 * 2 ^ 59
def prefixEnd_3132920 : Nat := 4983230072969 + 3 ^ 40 * 3132920 * 2
def baseEnd_3132920 : Nat := 536231270694662556597323

theorem tailTrace_3132920 : CollatzResearch.WordTrace tailWord_3132920 prefixEnd_3132920 536231270694662556597323 := by
  unfold tailWord_3132920
  simp only [CollatzResearch.WordTrace]
  refine ⟨57133489904986687491398107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76177986539982249988530809 57133489904986687491398107)
  ·
    refine ⟨85700234857480031237097161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57133489904986687491398107 85700234857480031237097161)
    ·
      refine ⟨64275176143110023427822871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85700234857480031237097161 64275176143110023427822871)
      ·
        refine ⟨96412764214665035141734307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64275176143110023427822871 96412764214665035141734307)
        ·
          refine ⟨144619146321997552712601461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96412764214665035141734307 144619146321997552712601461)
          ·
            refine ⟨13558044967687270566806387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144619146321997552712601461 13558044967687270566806387)
            ·
              refine ⟨20337067451530905850209581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13558044967687270566806387 20337067451530905850209581)
              ·
                refine ⟨7626400294324089693828593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20337067451530905850209581 7626400294324089693828593)
                ·
                  refine ⟨5719800220743067270371445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7626400294324089693828593 5719800220743067270371445)
                  ·
                    refine ⟨536231270694662556597323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5719800220743067270371445 536231270694662556597323)
                    ·
                      rfl

theorem cell23_3132920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_3132920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132920 prefixEnd_3132920 := by exact prefixLift 3132920
  have htrace : WordTrace (prefixWord ++ tailWord_3132920) baseStart_3132920 baseEnd_3132920 := by
    simpa [prefixWord, tailWord_3132920, baseEnd_3132920] using wordTrace_append hprefix tailTrace_3132920
  have hstable : (prefixWord ++ tailWord_3132920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132920).length < 2 ^ (prefixWord ++ tailWord_3132920).sum := by decide
  have hdescent : baseEnd_3132920 < baseStart_3132920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132974 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3132974 : Nat := 118140960795 + 3132974 * 2 ^ 59
def prefixEnd_3132974 : Nat := 4983230072969 + 3 ^ 40 * 3132974 * 2
def baseEnd_3132974 : Nat := 1608721540039330458516721

theorem tailTrace_3132974 : CollatzResearch.WordTrace tailWord_3132974 prefixEnd_3132974 1608721540039330458516721 := by
  unfold tailWord_3132974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14283618668972217775657747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76179299567851828136841317 14283618668972217775657747)
  ·
    refine ⟨21425428003458326663486621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14283618668972217775657747 21425428003458326663486621)
    ·
      refine ⟨8034535501296872498807483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21425428003458326663486621 8034535501296872498807483)
      ·
        refine ⟨12051803251945308748211225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8034535501296872498807483 12051803251945308748211225)
        ·
          refine ⟨9038852438958981561158419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12051803251945308748211225 9038852438958981561158419)
          ·
            refine ⟨13558278658438472341737629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9038852438958981561158419 13558278658438472341737629)
            ·
              refine ⟨5084354496914427128151611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13558278658438472341737629 5084354496914427128151611)
              ·
                refine ⟨7626531745371640692227417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5084354496914427128151611 7626531745371640692227417)
                ·
                  refine ⟨5719898809028730519170563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7626531745371640692227417 5719898809028730519170563)
                  ·
                    refine ⟨8579848213543095778755845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5719898809028730519170563 8579848213543095778755845)
                    ·
                      refine ⟨1608721540039330458516721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8579848213543095778755845 1608721540039330458516721)
                      ·
                        rfl

theorem cell23_3132974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3132974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132974 prefixEnd_3132974 := by exact prefixLift 3132974
  have htrace : WordTrace (prefixWord ++ tailWord_3132974) baseStart_3132974 baseEnd_3132974 := by
    simpa [prefixWord, tailWord_3132974, baseEnd_3132974] using wordTrace_append hprefix tailTrace_3132974
  have hstable : (prefixWord ++ tailWord_3132974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132974).length < 2 ^ (prefixWord ++ tailWord_3132974).sum := by decide
  have hdescent : baseEnd_3132974 < baseStart_3132974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3132984 : List Nat := [2, 1, 2, 1, 4, 2, 1, 5, 1, 4]
def baseStart_3132984 : Nat := 118140960795 + 3132984 * 2 ^ 59
def prefixEnd_3132984 : Nat := 4983230072969 + 3 ^ 40 * 3132984 * 2
def baseEnd_3132984 : Nat := 536242224948625139797225

theorem tailTrace_3132984 : CollatzResearch.WordTrace tailWord_3132984 prefixEnd_3132984 536242224948625139797225 := by
  unfold tailWord_3132984
  simp only [CollatzResearch.WordTrace]
  refine ⟨57134657040870756956563003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76179542721161009275417337 57134657040870756956563003)
  ·
    refine ⟨85701985561306135434844505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57134657040870756956563003 85701985561306135434844505)
    ·
      refine ⟨64276489170979601576133379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85701985561306135434844505 64276489170979601576133379)
      ·
        refine ⟨96414733756469402364200069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64276489170979601576133379 96414733756469402364200069)
        ·
          refine ⟨18077762579338012943287513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96414733756469402364200069 18077762579338012943287513)
          ·
            refine ⟨13558321934503509707465635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18077762579338012943287513 13558321934503509707465635)
            ·
              refine ⟨20337482901755264561198453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13558321934503509707465635 20337482901755264561198453)
              ·
                refine ⟨1906639022039556052612355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20337482901755264561198453 1906639022039556052612355)
                ·
                  refine ⟨2859958533059334078918533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906639022039556052612355 2859958533059334078918533)
                  ·
                    refine ⟨536242224948625139797225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2859958533059334078918533 536242224948625139797225)
                    ·
                      rfl

theorem cell23_3132984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_3132984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3132984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3132984 prefixEnd_3132984 := by exact prefixLift 3132984
  have htrace : WordTrace (prefixWord ++ tailWord_3132984) baseStart_3132984 baseEnd_3132984 := by
    simpa [prefixWord, tailWord_3132984, baseEnd_3132984] using wordTrace_append hprefix tailTrace_3132984
  have hstable : (prefixWord ++ tailWord_3132984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3132984).length < 2 ^ (prefixWord ++ tailWord_3132984).sum := by decide
  have hdescent : baseEnd_3132984 < baseStart_3132984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3132984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133027 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 1, 5]
def baseStart_3133027 : Nat := 118140960795 + 3133027 * 2 ^ 59
def prefixEnd_3133027 : Nat := 4983230072969 + 3 ^ 40 * 3133027 * 2
def baseEnd_3133027 : Nat := 536249584838006250384659

theorem tailTrace_3133027 : CollatzResearch.WordTrace tailWord_3133027 prefixEnd_3133027 536249584838006250384659 := by
  unfold tailWord_3133027
  simp only [CollatzResearch.WordTrace]
  refine ⟨114270882420585732256941335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76180588280390488171294223 114270882420585732256941335)
  ·
    refine ⟨171406323630878598385412003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114270882420585732256941335 171406323630878598385412003)
    ·
      refine ⟨257109485446317897578118005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171406323630878598385412003 257109485446317897578118005)
      ·
        refine ⟨24104014260592302897948563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257109485446317897578118005 24104014260592302897948563)
        ·
          refine ⟨36156021390888454346922845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24104014260592302897948563 36156021390888454346922845)
          ·
            refine ⟨13558508021583170380096067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36156021390888454346922845 13558508021583170380096067)
            ·
              refine ⟨20337762032374755570144101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13558508021583170380096067 20337762032374755570144101)
              ·
                refine ⟨3813330381070266669402019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20337762032374755570144101 3813330381070266669402019)
                ·
                  refine ⟨5719995571605400004103029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813330381070266669402019 5719995571605400004103029)
                  ·
                    refine ⟨536249584838006250384659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5719995571605400004103029 536249584838006250384659)
                    ·
                      rfl

theorem cell23_3133027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 5].length) (baseStart_3133027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133027 prefixEnd_3133027 := by exact prefixLift 3133027
  have htrace : WordTrace (prefixWord ++ tailWord_3133027) baseStart_3133027 baseEnd_3133027 := by
    simpa [prefixWord, tailWord_3133027, baseEnd_3133027] using wordTrace_append hprefix tailTrace_3133027
  have hstable : (prefixWord ++ tailWord_3133027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133027).length < 2 ^ (prefixWord ++ tailWord_3133027).sum := by decide
  have hdescent : baseEnd_3133027 < baseStart_3133027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133034 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_3133034 : Nat := 118140960795 + 3133034 * 2 ^ 59
def prefixEnd_3133034 : Nat := 4983230072969 + 3 ^ 40 * 3133034 * 2
def baseEnd_3133034 : Nat := 1608752348878600223766445

theorem tailTrace_3133034 : CollatzResearch.WordTrace tailWord_3133034 prefixEnd_3133034 1608752348878600223766445 := by
  unfold tailWord_3133034
  simp only [CollatzResearch.WordTrace]
  refine ⟨28567784432890093113111539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76180758487706914968297437 28567784432890093113111539)
  ·
    refine ⟨42851676649335139669667309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28567784432890093113111539 42851676649335139669667309)
    ·
      refine ⟨16069378743500677376125241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42851676649335139669667309 16069378743500677376125241)
      ·
        refine ⟨12052034057625508032093931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16069378743500677376125241 12052034057625508032093931)
        ·
          refine ⟨18078051086438262048140897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12052034057625508032093931 18078051086438262048140897)
          ·
            refine ⟨13558538314828696536105673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18078051086438262048140897 13558538314828696536105673)
            ·
              refine ⟨10168903736121522402079255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13558538314828696536105673 10168903736121522402079255)
              ·
                refine ⟨15253355604182283603118883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10168903736121522402079255 15253355604182283603118883)
                ·
                  refine ⟨22880033406273425404678325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15253355604182283603118883 22880033406273425404678325)
                  ·
                    refine ⟨2145003131838133631688593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22880033406273425404678325 2145003131838133631688593)
                    ·
                      refine ⟨1608752348878600223766445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145003131838133631688593 1608752348878600223766445)
                      ·
                        rfl

theorem cell23_3133034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_3133034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133034 prefixEnd_3133034 := by exact prefixLift 3133034
  have htrace : WordTrace (prefixWord ++ tailWord_3133034) baseStart_3133034 baseEnd_3133034 := by
    simpa [prefixWord, tailWord_3133034, baseEnd_3133034] using wordTrace_append hprefix tailTrace_3133034
  have hstable : (prefixWord ++ tailWord_3133034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133034).length < 2 ^ (prefixWord ++ tailWord_3133034).sum := by decide
  have hdescent : baseEnd_3133034 < baseStart_3133034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133067 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 3]
def baseStart_3133067 : Nat := 118140960795 + 3133067 * 2 ^ 59
def prefixEnd_3133067 : Nat := 4983230072969 + 3 ^ 40 * 3133067 * 2
def baseEnd_3133067 : Nat := 1608769293740198594653793

theorem tailTrace_3133067 : CollatzResearch.WordTrace tailWord_3133067 prefixEnd_3133067 1608769293740198594653793 := by
  unfold tailWord_3133067
  simp only [CollatzResearch.WordTrace]
  refine ⟨114272341340440819088397455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76181560893627212725598303 114272341340440819088397455)
  ·
    refine ⟨171408512010661228632596183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114272341340440819088397455 171408512010661228632596183)
    ·
      refine ⟨257112768015991842948894275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171408512010661228632596183 257112768015991842948894275)
      ·
        refine ⟨385669152023987764423341413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257112768015991842948894275 385669152023987764423341413)
        ·
          refine ⟨72312966004497705829376515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385669152023987764423341413 72312966004497705829376515)
          ·
            refine ⟨108469449006746558744064773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72312966004497705829376515 108469449006746558744064773)
            ·
              refine ⟨20338021688764979764512145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108469449006746558744064773 20338021688764979764512145)
              ·
                refine ⟨15253516266573734823384109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20338021688764979764512145 15253516266573734823384109)
                ·
                  refine ⟨5720068599965150558769041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15253516266573734823384109 5720068599965150558769041)
                  ·
                    refine ⟨4290051449973862919076781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5720068599965150558769041 4290051449973862919076781)
                    ·
                      refine ⟨1608769293740198594653793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4290051449973862919076781 1608769293740198594653793)
                      ·
                        rfl

theorem cell23_3133067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 3].length) (baseStart_3133067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133067 prefixEnd_3133067 := by exact prefixLift 3133067
  have htrace : WordTrace (prefixWord ++ tailWord_3133067) baseStart_3133067 baseEnd_3133067 := by
    simpa [prefixWord, tailWord_3133067, baseEnd_3133067] using wordTrace_append hprefix tailTrace_3133067
  have hstable : (prefixWord ++ tailWord_3133067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133067).length < 2 ^ (prefixWord ++ tailWord_3133067).sum := by decide
  have hdescent : baseEnd_3133067 < baseStart_3133067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133100 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_3133100 : Nat := 118140960795 + 3133100 * 2 ^ 59
def prefixEnd_3133100 : Nat := 4983230072969 + 3 ^ 40 * 3133100 * 2
def baseEnd_3133100 : Nat := 536262079533932321847047

theorem tailTrace_3133100 : CollatzResearch.WordTrace tailWord_3133100 prefixEnd_3133100 536262079533932321847047 := by
  unfold tailWord_3133100
  simp only [CollatzResearch.WordTrace]
  refine ⟨57136772474660632862174377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76182363299547510482899169 57136772474660632862174377)
  ·
    refine ⟨42852579355995474646630783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57136772474660632862174377 42852579355995474646630783)
    ·
      refine ⟨64278869033993211969946175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42852579355995474646630783 64278869033993211969946175)
      ·
        refine ⟨96418303550989817954919263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64278869033993211969946175 96418303550989817954919263)
        ·
          refine ⟨144627455326484726932378895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96418303550989817954919263 144627455326484726932378895)
          ·
            refine ⟨216941182989727090398568343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144627455326484726932378895 216941182989727090398568343)
            ·
              refine ⟨325411774484590635597852515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216941182989727090398568343 325411774484590635597852515)
              ·
                refine ⟨488117661726885953396778773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325411774484590635597852515 488117661726885953396778773)
                ·
                  refine ⟨22880515393447779065474005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 488117661726885953396778773 22880515393447779065474005)
                  ·
                    refine ⟨536262079533932321847047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22880515393447779065474005 536262079533932321847047)
                    ·
                      rfl

theorem cell23_3133100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_3133100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133100 prefixEnd_3133100 := by exact prefixLift 3133100
  have htrace : WordTrace (prefixWord ++ tailWord_3133100) baseStart_3133100 baseEnd_3133100 := by
    simpa [prefixWord, tailWord_3133100, baseEnd_3133100] using wordTrace_append hprefix tailTrace_3133100
  have hstable : (prefixWord ++ tailWord_3133100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133100).length < 2 ^ (prefixWord ++ tailWord_3133100).sum := by decide
  have hdescent : baseEnd_3133100 < baseStart_3133100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133157 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3133157 : Nat := 118140960795 + 3133157 * 2 ^ 59
def prefixEnd_3133157 : Nat := 4983230072969 + 3 ^ 40 * 3133157 * 2
def baseEnd_3133157 : Nat := 1608815506999103242528379

theorem tailTrace_3133157 : CollatzResearch.WordTrace tailWord_3133157 prefixEnd_3133157 1608815506999103242528379 := by
  unfold tailWord_3133157
  simp only [CollatzResearch.WordTrace]
  refine ⟨114275623910114764459173725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76183749273409842972782483 114275623910114764459173725)
  ·
    refine ⟨42853358966293036672190147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114275623910114764459173725 42853358966293036672190147)
    ·
      refine ⟨64280038449439555008285221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42853358966293036672190147 64280038449439555008285221)
      ·
        refine ⟨12052507209269916564053479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64280038449439555008285221 12052507209269916564053479)
        ·
          refine ⟨18078760813904874846080219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12052507209269916564053479 18078760813904874846080219)
          ·
            refine ⟨27118141220857312269120329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18078760813904874846080219 27118141220857312269120329)
            ·
              refine ⟨20338605915642984201840247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27118141220857312269120329 20338605915642984201840247)
              ·
                refine ⟨30507908873464476302760371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20338605915642984201840247 30507908873464476302760371)
                ·
                  refine ⟨45761863310196714454140557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30507908873464476302760371 45761863310196714454140557)
                  ·
                    refine ⟨17160698741323767920302709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45761863310196714454140557 17160698741323767920302709)
                    ·
                      refine ⟨1608815506999103242528379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17160698741323767920302709 1608815506999103242528379)
                      ·
                        rfl

theorem cell23_3133157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3133157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133157 prefixEnd_3133157 := by exact prefixLift 3133157
  have htrace : WordTrace (prefixWord ++ tailWord_3133157) baseStart_3133157 baseEnd_3133157 := by
    simpa [prefixWord, tailWord_3133157, baseEnd_3133157] using wordTrace_append hprefix tailTrace_3133157
  have hstable : (prefixWord ++ tailWord_3133157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133157).length < 2 ^ (prefixWord ++ tailWord_3133157).sum := by decide
  have hdescent : baseEnd_3133157 < baseStart_3133157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133167 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 4]
def baseStart_3133167 : Nat := 118140960795 + 3133167 * 2 ^ 59
def prefixEnd_3133167 : Nat := 4983230072969 + 3 ^ 40 * 3133167 * 2
def baseEnd_3133167 : Nat := 1608820641805648203403333

theorem tailTrace_3133167 : CollatzResearch.WordTrace tailWord_3133167 prefixEnd_3133167 1608820641805648203403333 := by
  unfold tailWord_3133167
  simp only [CollatzResearch.WordTrace]
  refine ⟨114275988640078536167037755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76183992426719024111358503 114275988640078536167037755)
  ·
    refine ⟨171413982960117804250556633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114275988640078536167037755 171413982960117804250556633)
    ·
      refine ⟨128560487220088353187917475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171413982960117804250556633 128560487220088353187917475)
      ·
        refine ⟨192840730830132529781876213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128560487220088353187917475 192840730830132529781876213)
        ·
          refine ⟨18078818515324924667050895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192840730830132529781876213 18078818515324924667050895)
          ·
            refine ⟨27118227772987387000576343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18078818515324924667050895 27118227772987387000576343)
            ·
              refine ⟨40677341659481080500864515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27118227772987387000576343 40677341659481080500864515)
              ·
                refine ⟨61016012489221620751296773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40677341659481080500864515 61016012489221620751296773)
                ·
                  refine ⟨11440502341729053890868145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61016012489221620751296773 11440502341729053890868145)
                  ·
                    refine ⟨8580376756296790418151109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11440502341729053890868145 8580376756296790418151109)
                    ·
                      refine ⟨1608820641805648203403333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8580376756296790418151109 1608820641805648203403333)
                      ·
                        rfl

theorem cell23_3133167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_3133167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133167 prefixEnd_3133167 := by exact prefixLift 3133167
  have htrace : WordTrace (prefixWord ++ tailWord_3133167) baseStart_3133167 baseEnd_3133167 := by
    simpa [prefixWord, tailWord_3133167, baseEnd_3133167] using wordTrace_append hprefix tailTrace_3133167
  have hstable : (prefixWord ++ tailWord_3133167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133167).length < 2 ^ (prefixWord ++ tailWord_3133167).sum := by decide
  have hdescent : baseEnd_3133167 < baseStart_3133167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133188 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_3133188 : Nat := 118140960795 + 3133188 * 2 ^ 59
def prefixEnd_3133188 : Nat := 4983230072969 + 3 ^ 40 * 3133188 * 2
def baseEnd_3133188 : Nat := 1608831424899392621240737

theorem tailTrace_3133188 : CollatzResearch.WordTrace tailWord_3133188 prefixEnd_3133188 1608831424899392621240737 := by
  unfold tailWord_3133188
  simp only [CollatzResearch.WordTrace]
  refine ⟨57138377286501228376776109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76184503048668304502368145 57138377286501228376776109)
  ·
    refine ⟨21426891482437960641291041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57138377286501228376776109 21426891482437960641291041)
    ·
      refine ⟨16070168611828470480968281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21426891482437960641291041 16070168611828470480968281)
      ·
        refine ⟨12052626458871352860726211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16070168611828470480968281 12052626458871352860726211)
        ·
          refine ⟨18078939688307029291089317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12052626458871352860726211 18078939688307029291089317)
          ·
            refine ⟨3389801191557567992079247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18078939688307029291089317 3389801191557567992079247)
            ·
              refine ⟨5084701787336351988118871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389801191557567992079247 5084701787336351988118871)
              ·
                refine ⟨7627052681004527982178307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5084701787336351988118871 7627052681004527982178307)
                ·
                  refine ⟨11440579021506791973267461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7627052681004527982178307 11440579021506791973267461)
                  ·
                    refine ⟨2145108566532523494987649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11440579021506791973267461 2145108566532523494987649)
                    ·
                      refine ⟨1608831424899392621240737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145108566532523494987649 1608831424899392621240737)
                      ·
                        rfl

theorem cell23_3133188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_3133188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133188 prefixEnd_3133188 := by exact prefixLift 3133188
  have htrace : WordTrace (prefixWord ++ tailWord_3133188) baseStart_3133188 baseEnd_3133188 := by
    simpa [prefixWord, tailWord_3133188, baseEnd_3133188] using wordTrace_append hprefix tailTrace_3133188
  have hstable : (prefixWord ++ tailWord_3133188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133188).length < 2 ^ (prefixWord ++ tailWord_3133188).sum := by decide
  have hdescent : baseEnd_3133188 < baseStart_3133188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133224 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 4, 5]
def baseStart_3133224 : Nat := 118140960795 + 3133224 * 2 ^ 59
def prefixEnd_3133224 : Nat := 4983230072969 + 3 ^ 40 * 3133224 * 2
def baseEnd_3133224 : Nat := 536283303400984826796857

theorem tailTrace_3133224 : CollatzResearch.WordTrace tailWord_3133224 prefixEnd_3133224 536283303400984826796857 := by
  unfold tailWord_3133224
  simp only [CollatzResearch.WordTrace]
  refine ⟨57139033800436017450931363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76185378400581356601241817 57139033800436017450931363)
  ·
    refine ⟨85708550700654026176397045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57139033800436017450931363 85708550700654026176397045)
    ·
      refine ⟨8035176628186314954037223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85708550700654026176397045 8035176628186314954037223)
      ·
        refine ⟨12052764942279472431055835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8035176628186314954037223 12052764942279472431055835)
        ·
          refine ⟨18079147413419208646583753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12052764942279472431055835 18079147413419208646583753)
          ·
            refine ⟨13559360560064406484937815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18079147413419208646583753 13559360560064406484937815)
            ·
              refine ⟨20339040840096609727406723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13559360560064406484937815 20339040840096609727406723)
              ·
                refine ⟨30508561260144914591110085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20339040840096609727406723 30508561260144914591110085)
                ·
                  refine ⟨5720355236277171485833141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30508561260144914591110085 5720355236277171485833141)
                  ·
                    refine ⟨536283303400984826796857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5720355236277171485833141 536283303400984826796857)
                    ·
                      rfl

theorem cell23_3133224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_3133224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133224 prefixEnd_3133224 := by exact prefixLift 3133224
  have htrace : WordTrace (prefixWord ++ tailWord_3133224) baseStart_3133224 baseEnd_3133224 := by
    simpa [prefixWord, tailWord_3133224, baseEnd_3133224] using wordTrace_append hprefix tailTrace_3133224
  have hstable : (prefixWord ++ tailWord_3133224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133224).length < 2 ^ (prefixWord ++ tailWord_3133224).sum := by decide
  have hdescent : baseEnd_3133224 < baseStart_3133224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133234 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_3133234 : Nat := 118140960795 + 3133234 * 2 ^ 59
def prefixEnd_3133234 : Nat := 4983230072969 + 3 ^ 40 * 3133234 * 2
def baseEnd_3133234 : Nat := 1608855045009499441265525

theorem tailTrace_3133234 : CollatzResearch.WordTrace tailWord_3133234 prefixEnd_3133234 1608855045009499441265525 := by
  unfold tailWord_3133234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28569608082708951652431689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76185621553890537739817837 28569608082708951652431689)
  ·
    refine ⟨21427206062031713739323767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28569608082708951652431689 21427206062031713739323767)
    ·
      refine ⟨32140809093047570608985651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21427206062031713739323767 32140809093047570608985651)
      ·
        refine ⟨48211213639571355913478477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32140809093047570608985651 48211213639571355913478477)
        ·
          refine ⟨18079205114839258467554429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48211213639571355913478477 18079205114839258467554429)
          ·
            refine ⟨6779701918064721925332911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18079205114839258467554429 6779701918064721925332911)
            ·
              refine ⟨10169552877097082887999367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6779701918064721925332911 10169552877097082887999367)
              ·
                refine ⟨15254329315645624331999051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10169552877097082887999367 15254329315645624331999051)
                ·
                  refine ⟨22881493973468436497998577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15254329315645624331999051 22881493973468436497998577)
                  ·
                    refine ⟨17161120480101327373498933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22881493973468436497998577 17161120480101327373498933)
                    ·
                      refine ⟨1608855045009499441265525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17161120480101327373498933 1608855045009499441265525)
                      ·
                        rfl

theorem cell23_3133234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_3133234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133234 prefixEnd_3133234 := by exact prefixLift 3133234
  have htrace : WordTrace (prefixWord ++ tailWord_3133234) baseStart_3133234 baseEnd_3133234 := by
    simpa [prefixWord, tailWord_3133234, baseEnd_3133234] using wordTrace_append hprefix tailTrace_3133234
  have hstable : (prefixWord ++ tailWord_3133234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133234).length < 2 ^ (prefixWord ++ tailWord_3133234).sum := by decide
  have hdescent : baseEnd_3133234 < baseStart_3133234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133288 : List Nat := [2, 1, 4, 2, 1, 1, 3, 4, 1, 4]
def baseStart_3133288 : Nat := 118140960795 + 3133288 * 2 ^ 59
def prefixEnd_3133288 : Nat := 4983230072969 + 3 ^ 40 * 3133288 * 2
def baseEnd_3133288 : Nat := 536294257654947409996759

theorem tailTrace_3133288 : CollatzResearch.WordTrace tailWord_3133288 prefixEnd_3133288 536294257654947409996759 := by
  unfold tailWord_3133288
  simp only [CollatzResearch.WordTrace]
  refine ⟨57140200936320086916096259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76186934581760115888128345 57140200936320086916096259)
  ·
    refine ⟨85710301404480130374144389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57140200936320086916096259 85710301404480130374144389)
    ·
      refine ⟨16070681513340024445152073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85710301404480130374144389 16070681513340024445152073)
      ·
        refine ⟨12053011135005018333864055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16070681513340024445152073 12053011135005018333864055)
        ·
          refine ⟨18079516702507527500796083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12053011135005018333864055 18079516702507527500796083)
          ·
            refine ⟨27119275053761291251194125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18079516702507527500796083 27119275053761291251194125)
            ·
              refine ⟨10169728145160484219197797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27119275053761291251194125 10169728145160484219197797)
              ·
                refine ⟨1906824027217590791099587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10169728145160484219197797 1906824027217590791099587)
                ·
                  refine ⟨2860236040826386186649381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906824027217590791099587 2860236040826386186649381)
                  ·
                    refine ⟨536294257654947409996759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2860236040826386186649381 536294257654947409996759)
                    ·
                      rfl

theorem cell23_3133288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_3133288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133288 prefixEnd_3133288 := by exact prefixLift 3133288
  have htrace : WordTrace (prefixWord ++ tailWord_3133288) baseStart_3133288 baseEnd_3133288 := by
    simpa [prefixWord, tailWord_3133288, baseEnd_3133288] using wordTrace_append hprefix tailTrace_3133288
  have hstable : (prefixWord ++ tailWord_3133288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133288).length < 2 ^ (prefixWord ++ tailWord_3133288).sum := by decide
  have hdescent : baseEnd_3133288 < baseStart_3133288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133307 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 7]
def baseStart_3133307 : Nat := 118140960795 + 3133307 * 2 ^ 59
def prefixEnd_3133307 : Nat := 4983230072969 + 3 ^ 40 * 3133307 * 2
def baseEnd_3133307 : Nat := 1608892529097277655652689

theorem tailTrace_3133307 : CollatzResearch.WordTrace tailWord_3133307 prefixEnd_3133307 1608892529097277655652689 := by
  unfold tailWord_3133307
  simp only [CollatzResearch.WordTrace]
  refine ⟨114281094859571340077134175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76187396573047560051422783 114281094859571340077134175)
  ·
    refine ⟨171421642289357010115701263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114281094859571340077134175 171421642289357010115701263)
    ·
      refine ⟨257132463434035515173551895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171421642289357010115701263 257132463434035515173551895)
      ·
        refine ⟨385698695151053272760327843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257132463434035515173551895 385698695151053272760327843)
        ·
          refine ⟨578548042726579909140491765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385698695151053272760327843 578548042726579909140491765)
          ·
            refine ⟨54238879005616866481921103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 578548042726579909140491765 54238879005616866481921103)
            ·
              refine ⟨81358318508425299722881655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54238879005616866481921103 81358318508425299722881655)
              ·
                refine ⟨122037477762637949584322483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81358318508425299722881655 122037477762637949584322483)
                ·
                  refine ⟨183056216643956924376483725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122037477762637949584322483 183056216643956924376483725)
                  ·
                    refine ⟨68646081241483846641181397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183056216643956924376483725 68646081241483846641181397)
                    ·
                      refine ⟨1608892529097277655652689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68646081241483846641181397 1608892529097277655652689)
                      ·
                        rfl

theorem cell23_3133307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_3133307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133307 prefixEnd_3133307 := by exact prefixLift 3133307
  have htrace : WordTrace (prefixWord ++ tailWord_3133307) baseStart_3133307 baseEnd_3133307 := by
    simpa [prefixWord, tailWord_3133307, baseEnd_3133307] using wordTrace_append hprefix tailTrace_3133307
  have hstable : (prefixWord ++ tailWord_3133307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133307).length < 2 ^ (prefixWord ++ tailWord_3133307).sum := by decide
  have hdescent : baseEnd_3133307 < baseStart_3133307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133321 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 1, 5, 2]
def baseStart_3133321 : Nat := 118140960795 + 3133321 * 2 ^ 59
def prefixEnd_3133321 : Nat := 4983230072969 + 3 ^ 40 * 3133321 * 2
def baseEnd_3133321 : Nat := 1608899717826440600877625

theorem tailTrace_3133321 : CollatzResearch.WordTrace tailWord_3133321 prefixEnd_3133321 1608899717826440600877625 := by
  unfold tailWord_3133321
  simp only [CollatzResearch.WordTrace]
  refine ⟨114281605481520620468143817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76187736987680413645429211 114281605481520620468143817)
  ·
    refine ⟨85711204111140465351107863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114281605481520620468143817 85711204111140465351107863)
    ·
      refine ⟨128566806166710698026661795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85711204111140465351107863 128566806166710698026661795)
      ·
        refine ⟨192850209250066047039992693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128566806166710698026661795 192850209250066047039992693)
        ·
          refine ⟨18079707117193691909999315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192850209250066047039992693 18079707117193691909999315)
          ·
            refine ⟨27119560675790537864998973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18079707117193691909999315 27119560675790537864998973)
            ·
              refine ⟨10169835253421451699374615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27119560675790537864998973 10169835253421451699374615)
              ·
                refine ⟨15254752880132177549061923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10169835253421451699374615 15254752880132177549061923)
                ·
                  refine ⟨22882129320198266323592885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15254752880132177549061923 22882129320198266323592885)
                  ·
                    refine ⟨2145199623768587467836833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22882129320198266323592885 2145199623768587467836833)
                    ·
                      refine ⟨1608899717826440600877625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145199623768587467836833 1608899717826440600877625)
                      ·
                        rfl

theorem cell23_3133321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 5, 2].length) (baseStart_3133321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133321 prefixEnd_3133321 := by exact prefixLift 3133321
  have htrace : WordTrace (prefixWord ++ tailWord_3133321) baseStart_3133321 baseEnd_3133321 := by
    simpa [prefixWord, tailWord_3133321, baseEnd_3133321] using wordTrace_append hprefix tailTrace_3133321
  have hstable : (prefixWord ++ tailWord_3133321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133321).length < 2 ^ (prefixWord ++ tailWord_3133321).sum := by decide
  have hdescent : baseEnd_3133321 < baseStart_3133321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133327 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 4, 10]
def baseStart_3133327 : Nat := 118140960795 + 3133327 * 2 ^ 59
def prefixEnd_3133327 : Nat := 4983230072969 + 3 ^ 40 * 3133327 * 2
def baseEnd_3133327 : Nat := 536300932903455859134199

theorem tailTrace_3133327 : CollatzResearch.WordTrace tailWord_3133327 prefixEnd_3133327 536300932903455859134199 := by
  unfold tailWord_3133327
  simp only [CollatzResearch.WordTrace]
  refine ⟨114281824319498883492862235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76187882879665922328574823 114281824319498883492862235)
  ·
    refine ⟨171422736479248325239293353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114281824319498883492862235 171422736479248325239293353)
    ·
      refine ⟨128567052359436243929470015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171422736479248325239293353 128567052359436243929470015)
      ·
        refine ⟨192850578539154365894205023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128567052359436243929470015 192850578539154365894205023)
        ·
          refine ⟨289275867808731548841307535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192850578539154365894205023 289275867808731548841307535)
          ·
            refine ⟨433913801713097323261961303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289275867808731548841307535 433913801713097323261961303)
            ·
              refine ⟨650870702569645984892941955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433913801713097323261961303 650870702569645984892941955)
              ·
                refine ⟨976306053854468977339412933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650870702569645984892941955 976306053854468977339412933)
                ·
                  refine ⟨183057385097712933251139925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 976306053854468977339412933 183057385097712933251139925)
                  ·
                    refine ⟨536300932903455859134199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 183057385097712933251139925 536300932903455859134199)
                    ·
                      rfl

theorem cell23_3133327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_3133327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133327 prefixEnd_3133327 := by exact prefixLift 3133327
  have htrace : WordTrace (prefixWord ++ tailWord_3133327) baseStart_3133327 baseEnd_3133327 := by
    simpa [prefixWord, tailWord_3133327, baseEnd_3133327] using wordTrace_append hprefix tailTrace_3133327
  have hstable : (prefixWord ++ tailWord_3133327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133327).length < 2 ^ (prefixWord ++ tailWord_3133327).sum := by decide
  have hdescent : baseEnd_3133327 < baseStart_3133327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133328 : List Nat := [2, 1, 1, 1, 1, 1, 2, 9, 1, 1, 3]
def baseStart_3133328 : Nat := 118140960795 + 3133328 * 2 ^ 59
def prefixEnd_3133328 : Nat := 4983230072969 + 3 ^ 40 * 3133328 * 2
def baseEnd_3133328 : Nat := 1608903312191022073490093

theorem tailTrace_3133328 : CollatzResearch.WordTrace tailWord_3133328 prefixEnd_3133328 1608903312191022073490093 := by
  unfold tailWord_3133328
  simp only [CollatzResearch.WordTrace]
  refine ⟨57140930396247630331824319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76187907194996840442432425 57140930396247630331824319)
  ·
    refine ⟨85711395594371445497736479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57140930396247630331824319 85711395594371445497736479)
    ·
      refine ⟨128567093391557168246604719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85711395594371445497736479 128567093391557168246604719)
      ·
        refine ⟨192850640087335752369907079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128567093391557168246604719 192850640087335752369907079)
        ·
          refine ⟨289275960131003628554860619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192850640087335752369907079 289275960131003628554860619)
          ·
            refine ⟨433913940196505442832290929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289275960131003628554860619 433913940196505442832290929)
            ·
              refine ⟨325435455147379082124218197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433913940196505442832290929 325435455147379082124218197)
              ·
                refine ⟨1906848370004174309321591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 325435455147379082124218197 1906848370004174309321591)
                ·
                  refine ⟨2860272555006261463982387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906848370004174309321591 2860272555006261463982387)
                  ·
                    refine ⟨4290408832509392195973581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2860272555006261463982387 4290408832509392195973581)
                    ·
                      refine ⟨1608903312191022073490093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4290408832509392195973581 1608903312191022073490093)
                      ·
                        rfl

theorem cell23_3133328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 1, 1, 3].length) (baseStart_3133328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133328 prefixEnd_3133328 := by exact prefixLift 3133328
  have htrace : WordTrace (prefixWord ++ tailWord_3133328) baseStart_3133328 baseEnd_3133328 := by
    simpa [prefixWord, tailWord_3133328, baseEnd_3133328] using wordTrace_append hprefix tailTrace_3133328
  have hstable : (prefixWord ++ tailWord_3133328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133328).length < 2 ^ (prefixWord ++ tailWord_3133328).sum := by decide
  have hdescent : baseEnd_3133328 < baseStart_3133328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133345 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3133345 : Nat := 118140960795 + 3133345 * 2 ^ 59
def prefixEnd_3133345 : Nat := 4983230072969 + 3 ^ 40 * 3133345 * 2
def baseEnd_3133345 : Nat := 1608912041362148506977515

theorem tailTrace_3133345 : CollatzResearch.WordTrace tailWord_3133345 prefixEnd_3133345 1608912041362148506977515 := by
  unfold tailWord_3133345
  simp only [CollatzResearch.WordTrace]
  refine ⟨114282480833433672567017489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76188320555622448378011659 114282480833433672567017489)
  ·
    refine ⟨85711860625075254425263117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114282480833433672567017489 85711860625075254425263117)
    ·
      refine ⟨32141947734403220409473669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85711860625075254425263117 32141947734403220409473669)
      ·
        refine ⟨6026615200200603826776313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32141947734403220409473669 6026615200200603826776313)
        ·
          refine ⟨4519961400150452870082235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6026615200200603826776313 4519961400150452870082235)
          ·
            refine ⟨6779942100225679305123353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4519961400150452870082235 6779942100225679305123353)
            ·
              refine ⟨5084956575169259478842515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6779942100225679305123353 5084956575169259478842515)
              ·
                refine ⟨7627434862753889218263773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5084956575169259478842515 7627434862753889218263773)
                ·
                  refine ⟨2860288073532708456848915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7627434862753889218263773 2860288073532708456848915)
                  ·
                    refine ⟨4290432110299062685273373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2860288073532708456848915 4290432110299062685273373)
                    ·
                      refine ⟨1608912041362148506977515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4290432110299062685273373 1608912041362148506977515)
                      ·
                        rfl

theorem cell23_3133345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3133345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133345 prefixEnd_3133345 := by exact prefixLift 3133345
  have htrace : WordTrace (prefixWord ++ tailWord_3133345) baseStart_3133345 baseEnd_3133345 := by
    simpa [prefixWord, tailWord_3133345, baseEnd_3133345] using wordTrace_append hprefix tailTrace_3133345
  have hstable : (prefixWord ++ tailWord_3133345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133345).length < 2 ^ (prefixWord ++ tailWord_3133345).sum := by decide
  have hdescent : baseEnd_3133345 < baseStart_3133345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133361 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 1, 6]
def baseStart_3133361 : Nat := 118140960795 + 3133361 * 2 ^ 59
def prefixEnd_3133361 : Nat := 4983230072969 + 3 ^ 40 * 3133361 * 2
def baseEnd_3133361 : Nat := 536306752350873481459147

theorem tailTrace_3133361 : CollatzResearch.WordTrace tailWord_3133361 prefixEnd_3133361 536306752350873481459147 := by
  unfold tailWord_3133361
  simp only [CollatzResearch.WordTrace]
  refine ⟨114283064401375707299599937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76188709600917138199733291 114283064401375707299599937)
  ·
    refine ⟨85712298301031780474699953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114283064401375707299599937 85712298301031780474699953)
    ·
      refine ⟨64284223725773835356024965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85712298301031780474699953 64284223725773835356024965)
      ·
        refine ⟨12053291948582594129254681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64284223725773835356024965 12053291948582594129254681)
        ·
          refine ⟨9039968961436945596941011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12053291948582594129254681 9039968961436945596941011)
          ·
            refine ⟨13559953442155418395411517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9039968961436945596941011 13559953442155418395411517)
            ·
              refine ⟨5084982540808281898279319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13559953442155418395411517 5084982540808281898279319)
              ·
                refine ⟨7627473811212422847418979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5084982540808281898279319 7627473811212422847418979)
                ·
                  refine ⟨11441210716818634271128469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7627473811212422847418979 11441210716818634271128469)
                  ·
                    refine ⟨536306752350873481459147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11441210716818634271128469 536306752350873481459147)
                    ·
                      rfl

theorem cell23_3133361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_3133361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133361 prefixEnd_3133361 := by exact prefixLift 3133361
  have htrace : WordTrace (prefixWord ++ tailWord_3133361) baseStart_3133361 baseEnd_3133361 := by
    simpa [prefixWord, tailWord_3133361, baseEnd_3133361] using wordTrace_append hprefix tailTrace_3133361
  have hstable : (prefixWord ++ tailWord_3133361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133361).length < 2 ^ (prefixWord ++ tailWord_3133361).sum := by decide
  have hdescent : baseEnd_3133361 < baseStart_3133361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133368 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 3, 2, 2]
def baseStart_3133368 : Nat := 118140960795 + 3133368 * 2 ^ 59
def prefixEnd_3133368 : Nat := 4983230072969 + 3 ^ 40 * 3133368 * 2
def baseEnd_3133368 : Nat := 1608923851417201916989909

theorem tailTrace_3133368 : CollatzResearch.WordTrace tailWord_3133368 prefixEnd_3133368 1608923851417201916989909 := by
  unfold tailWord_3133368
  simp only [CollatzResearch.WordTrace]
  refine ⟨57141659856175173747552379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76188879808233564996736505 57141659856175173747552379)
  ·
    refine ⟨85712489784262760621328569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57141659856175173747552379 85712489784262760621328569)
    ·
      refine ⟨64284367338197070465996427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85712489784262760621328569 64284367338197070465996427)
      ·
        refine ⟨96426551007295605698994641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64284367338197070465996427 96426551007295605698994641)
        ·
          refine ⟨72319913255471704274245981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96426551007295605698994641 72319913255471704274245981)
          ·
            refine ⟨27119967470801889102842243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72319913255471704274245981 27119967470801889102842243)
            ·
              refine ⟨40679951206202833654263365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27119967470801889102842243 40679951206202833654263365)
              ·
                refine ⟨7627490851163031310174381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40679951206202833654263365 7627490851163031310174381)
                ·
                  refine ⟨2860309069186136741315393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7627490851163031310174381 2860309069186136741315393)
                  ·
                    refine ⟨2145231801889602555986545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2860309069186136741315393 2145231801889602555986545)
                    ·
                      refine ⟨1608923851417201916989909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145231801889602555986545 1608923851417201916989909)
                      ·
                        rfl

theorem cell23_3133368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3, 2, 2].length) (baseStart_3133368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133368 prefixEnd_3133368 := by exact prefixLift 3133368
  have htrace : WordTrace (prefixWord ++ tailWord_3133368) baseStart_3133368 baseEnd_3133368 := by
    simpa [prefixWord, tailWord_3133368, baseEnd_3133368] using wordTrace_append hprefix tailTrace_3133368
  have hstable : (prefixWord ++ tailWord_3133368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133368).length < 2 ^ (prefixWord ++ tailWord_3133368).sum := by decide
  have hdescent : baseEnd_3133368 < baseStart_3133368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133371 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 1, 2, 3]
def baseStart_3133371 : Nat := 118140960795 + 3133371 * 2 ^ 59
def prefixEnd_3133371 : Nat := 4983230072969 + 3 ^ 40 * 3133371 * 2
def baseEnd_3133371 : Nat := 1608925391859165405252395

theorem tailTrace_3133371 : CollatzResearch.WordTrace tailWord_3133371 prefixEnd_3133371 1608925391859165405252395 := by
  unfold tailWord_3133371
  simp only [CollatzResearch.WordTrace]
  refine ⟨114283429131339479007463967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76188952754226319338309311 114283429131339479007463967)
  ·
    refine ⟨171425143697009218511195951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114283429131339479007463967 171425143697009218511195951)
    ·
      refine ⟨257137715545513827766793927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171425143697009218511195951 257137715545513827766793927)
      ·
        refine ⟨385706573318270741650190891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257137715545513827766793927 385706573318270741650190891)
        ·
          refine ⟨578559859977406112475286337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385706573318270741650190891 578559859977406112475286337)
          ·
            refine ⟨433919894983054584356464753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578559859977406112475286337 433919894983054584356464753)
            ·
              refine ⟨325439921237290938267348565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433919894983054584356464753 325439921237290938267348565)
              ·
                refine ⟨3813749076999503182820491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 325439921237290938267348565 3813749076999503182820491)
                ·
                  refine ⟨5720623615499254774230737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813749076999503182820491 5720623615499254774230737)
                  ·
                    refine ⟨4290467711624441080673053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5720623615499254774230737 4290467711624441080673053)
                    ·
                      refine ⟨1608925391859165405252395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4290467711624441080673053 1608925391859165405252395)
                      ·
                        rfl

theorem cell23_3133371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 2, 3].length) (baseStart_3133371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133371 prefixEnd_3133371 := by exact prefixLift 3133371
  have htrace : WordTrace (prefixWord ++ tailWord_3133371) baseStart_3133371 baseEnd_3133371 := by
    simpa [prefixWord, tailWord_3133371, baseEnd_3133371] using wordTrace_append hprefix tailTrace_3133371
  have hstable : (prefixWord ++ tailWord_3133371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133371).length < 2 ^ (prefixWord ++ tailWord_3133371).sum := by decide
  have hdescent : baseEnd_3133371 < baseStart_3133371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133388 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3133388 : Nat := 118140960795 + 3133388 * 2 ^ 59
def prefixEnd_3133388 : Nat := 4983230072969 + 3 ^ 40 * 3133388 * 2
def baseEnd_3133388 : Nat := 1608934121030291838739817

theorem tailTrace_3133388 : CollatzResearch.WordTrace tailWord_3133388 prefixEnd_3133388 1608934121030291838739817 := by
  unfold tailWord_3133388
  simp only [CollatzResearch.WordTrace]
  refine ⟨57142024586138945455416409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76189366114851927273888545 57142024586138945455416409)
  ·
    refine ⟨42856518439604209091562307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57142024586138945455416409 42856518439604209091562307)
    ·
      refine ⟨64284777659406313637343461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42856518439604209091562307 64284777659406313637343461)
      ·
        refine ⟨12053395811138683807001899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64284777659406313637343461 12053395811138683807001899)
        ·
          refine ⟨18080093716708025710502849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12053395811138683807001899 18080093716708025710502849)
          ·
            refine ⟨13560070287531019282877137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18080093716708025710502849 13560070287531019282877137)
            ·
              refine ⟨10170052715648264462157853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13560070287531019282877137 10170052715648264462157853)
              ·
                refine ⟨3813769768368099173309195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10170052715648264462157853 3813769768368099173309195)
                ·
                  refine ⟨5720654652552148759963793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813769768368099173309195 5720654652552148759963793)
                  ·
                    refine ⟨4290490989414111569972845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5720654652552148759963793 4290490989414111569972845)
                    ·
                      refine ⟨1608934121030291838739817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4290490989414111569972845 1608934121030291838739817)
                      ·
                        rfl

theorem cell23_3133388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3133388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133388 prefixEnd_3133388 := by exact prefixLift 3133388
  have htrace : WordTrace (prefixWord ++ tailWord_3133388) baseStart_3133388 baseEnd_3133388 := by
    simpa [prefixWord, tailWord_3133388, baseEnd_3133388] using wordTrace_append hprefix tailTrace_3133388
  have hstable : (prefixWord ++ tailWord_3133388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133388).length < 2 ^ (prefixWord ++ tailWord_3133388).sum := by decide
  have hdescent : baseEnd_3133388 < baseStart_3133388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133402 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2]
def baseStart_3133402 : Nat := 118140960795 + 3133402 * 2 ^ 59
def prefixEnd_3133402 : Nat := 4983230072969 + 3 ^ 40 * 3133402 * 2
def baseEnd_3133402 : Nat := 1608941309759454783964753

theorem tailTrace_3133402 : CollatzResearch.WordTrace tailWord_3133402 prefixEnd_3133402 1608941309759454783964753 := by
  unfold tailWord_3133402
  simp only [CollatzResearch.WordTrace]
  refine ⟨28571139948556792825460615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76189706529484780867894973 28571139948556792825460615)
  ·
    refine ⟨42856709922835189238190923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28571139948556792825460615 42856709922835189238190923)
    ·
      refine ⟨64285064884252783857286385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42856709922835189238190923 64285064884252783857286385)
      ·
        refine ⟨48213798663189587892964789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64285064884252783857286385 48213798663189587892964789)
        ·
          refine ⟨4520043624674023864965449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48213798663189587892964789 4520043624674023864965449)
          ·
            refine ⟨3390032718505517898724087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4520043624674023864965449 3390032718505517898724087)
            ·
              refine ⟨5085049077758276848086131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390032718505517898724087 5085049077758276848086131)
              ·
                refine ⟨7627573616637415272129197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5085049077758276848086131 7627573616637415272129197)
                ·
                  refine ⟨2860340106239030727048449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7627573616637415272129197 2860340106239030727048449)
                  ·
                    refine ⟨2145255079679273045286337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2860340106239030727048449 2145255079679273045286337)
                    ·
                      refine ⟨1608941309759454783964753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145255079679273045286337 1608941309759454783964753)
                      ·
                        rfl

theorem cell23_3133402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_3133402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133402 prefixEnd_3133402 := by exact prefixLift 3133402
  have htrace : WordTrace (prefixWord ++ tailWord_3133402) baseStart_3133402 baseEnd_3133402 := by
    simpa [prefixWord, tailWord_3133402, baseEnd_3133402] using wordTrace_append hprefix tailTrace_3133402
  have hstable : (prefixWord ++ tailWord_3133402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133402).length < 2 ^ (prefixWord ++ tailWord_3133402).sum := by decide
  have hdescent : baseEnd_3133402 < baseStart_3133402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133434 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_3133434 : Nat := 118140960795 + 3133434 * 2 ^ 59
def prefixEnd_3133434 : Nat := 4983230072969 + 3 ^ 40 * 3133434 * 2
def baseEnd_3133434 : Nat := 536319247046799552921535

theorem tailTrace_3133434 : CollatzResearch.WordTrace tailWord_3133434 prefixEnd_3133434 536319247046799552921535 := by
  unfold tailWord_3133434
  simp only [CollatzResearch.WordTrace]
  refine ⟨28571431732527810191751839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76190484620074160511338237 28571431732527810191751839)
  ·
    refine ⟨42857147598791715287627759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28571431732527810191751839 42857147598791715287627759)
    ·
      refine ⟨64285721398187572931441639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42857147598791715287627759 64285721398187572931441639)
      ·
        refine ⟨96428582097281359397162459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64285721398187572931441639 96428582097281359397162459)
        ·
          refine ⟨144642873145922039095743689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96428582097281359397162459 144642873145922039095743689)
          ·
            refine ⟨108482154859441529321807767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144642873145922039095743689 108482154859441529321807767)
            ·
              refine ⟨162723232289162293982711651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108482154859441529321807767 162723232289162293982711651)
              ·
                refine ⟨244084848433743440974067477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162723232289162293982711651 244084848433743440974067477)
                ·
                  refine ⟨11441477270331723795659413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 244084848433743440974067477 11441477270331723795659413)
                  ·
                    refine ⟨536319247046799552921535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11441477270331723795659413 536319247046799552921535)
                    ·
                      rfl

theorem cell23_3133434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_3133434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133434 prefixEnd_3133434 := by exact prefixLift 3133434
  have htrace : WordTrace (prefixWord ++ tailWord_3133434) baseStart_3133434 baseEnd_3133434 := by
    simpa [prefixWord, tailWord_3133434, baseEnd_3133434] using wordTrace_append hprefix tailTrace_3133434
  have hstable : (prefixWord ++ tailWord_3133434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133434).length < 2 ^ (prefixWord ++ tailWord_3133434).sum := by decide
  have hdescent : baseEnd_3133434 < baseStart_3133434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133446 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3133446 : Nat := 118140960795 + 3133446 * 2 ^ 59
def prefixEnd_3133446 : Nat := 4983230072969 + 3 ^ 40 * 3133446 * 2
def baseEnd_3133446 : Nat := 536321300969417537271517

theorem tailTrace_3133446 : CollatzResearch.WordTrace tailWord_3133446 prefixEnd_3133446 536321300969417537271517 := by
  unfold tailWord_3133446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3571442643939617713013881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76190776404045177877629461 3571442643939617713013881)
  ·
    refine ⟨2678581982954713284760411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3571442643939617713013881 2678581982954713284760411)
    ·
      refine ⟨4017872974432069927140617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2678581982954713284760411 4017872974432069927140617)
      ·
        refine ⟨3013404730824052445355463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4017872974432069927140617 3013404730824052445355463)
        ·
          refine ⟨4520107096236078668033195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013404730824052445355463 4520107096236078668033195)
          ·
            refine ⟨6780160644354118002049793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4520107096236078668033195 6780160644354118002049793)
            ·
              refine ⟨5085120483265588501537345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6780160644354118002049793 5085120483265588501537345)
              ·
                refine ⟨3813840362449191376153009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5085120483265588501537345 3813840362449191376153009)
                ·
                  refine ⟨2860380271836893532114757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3813840362449191376153009 2860380271836893532114757)
                  ·
                    refine ⟨536321300969417537271517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2860380271836893532114757 536321300969417537271517)
                    ·
                      rfl

theorem cell23_3133446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3133446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133446 prefixEnd_3133446 := by exact prefixLift 3133446
  have htrace : WordTrace (prefixWord ++ tailWord_3133446) baseStart_3133446 baseEnd_3133446 := by
    simpa [prefixWord, tailWord_3133446, baseEnd_3133446] using wordTrace_append hprefix tailTrace_3133446
  have hstable : (prefixWord ++ tailWord_3133446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133446).length < 2 ^ (prefixWord ++ tailWord_3133446).sum := by decide
  have hdescent : baseEnd_3133446 < baseStart_3133446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133453 : List Nat := [1, 7, 1, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3133453 : Nat := 118140960795 + 3133453 * 2 ^ 59
def prefixEnd_3133453 : Nat := 4983230072969 + 3 ^ 40 * 3133453 * 2
def baseEnd_3133453 : Nat := 1608967497272834084427019

theorem tailTrace_3133453 : CollatzResearch.WordTrace tailWord_3133453 prefixEnd_3133453 1608967497272834084427019 := by
  unfold tailWord_3133453
  simp only [CollatzResearch.WordTrace]
  refine ⟨114286419917042407011949013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76190946611361604674632675 114286419917042407011949013)
  ·
    refine ⟨2678587966805681414342555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 114286419917042407011949013 2678587966805681414342555)
    ·
      refine ⟨4017881950208522121513833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2678587966805681414342555 4017881950208522121513833)
      ·
        refine ⟨3013411462656391591135375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4017881950208522121513833 3013411462656391591135375)
        ·
          refine ⟨4520117193984587386703063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013411462656391591135375 4520117193984587386703063)
          ·
            refine ⟨6780175790976881080054595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4520117193984587386703063 6780175790976881080054595)
            ·
              refine ⟨10170263686465321620081893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6780175790976881080054595 10170263686465321620081893)
              ·
                refine ⟨1906924441212247803765355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10170263686465321620081893 1906924441212247803765355)
                ·
                  refine ⟨2860386661818371705648033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906924441212247803765355 2860386661818371705648033)
                  ·
                    refine ⟨2145289996363778779236025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2860386661818371705648033 2145289996363778779236025)
                    ·
                      refine ⟨1608967497272834084427019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145289996363778779236025 1608967497272834084427019)
                      ·
                        rfl

theorem cell23_3133453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3133453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133453 prefixEnd_3133453 := by exact prefixLift 3133453
  have htrace : WordTrace (prefixWord ++ tailWord_3133453) baseStart_3133453 baseEnd_3133453 := by
    simpa [prefixWord, tailWord_3133453, baseEnd_3133453] using wordTrace_append hprefix tailTrace_3133453
  have hstable : (prefixWord ++ tailWord_3133453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133453).length < 2 ^ (prefixWord ++ tailWord_3133453).sum := by decide
  have hdescent : baseEnd_3133453 < baseStart_3133453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133471 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 4]
def baseStart_3133471 : Nat := 118140960795 + 3133471 * 2 ^ 59
def prefixEnd_3133471 : Nat := 4983230072969 + 3 ^ 40 * 3133471 * 2
def baseEnd_3133471 : Nat := 1608976739924615014001935

theorem tailTrace_3133471 : CollatzResearch.WordTrace tailWord_3133471 prefixEnd_3133471 1608976739924615014001935 := by
  unfold tailWord_3133471
  simp only [CollatzResearch.WordTrace]
  refine ⟨114287076430977196086104267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76191384287318130724069511 114287076430977196086104267)
  ·
    refine ⟨171430614646465794129156401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114287076430977196086104267 171430614646465794129156401)
    ·
      refine ⟨128572960984849345596867301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171430614646465794129156401 128572960984849345596867301)
      ·
        refine ⟨24107430184659252299412619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128572960984849345596867301 24107430184659252299412619)
        ·
          refine ⟨36161145276988878449118929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24107430184659252299412619 36161145276988878449118929)
          ·
            refine ⟨27120858957741658836839197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36161145276988878449118929 27120858957741658836839197)
            ·
              refine ⟨10170322109153122063814699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27120858957741658836839197 10170322109153122063814699)
              ·
                refine ⟨15255483163729683095722049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10170322109153122063814699 15255483163729683095722049)
                ·
                  refine ⟨11441612372797262321791537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15255483163729683095722049 11441612372797262321791537)
                  ·
                    refine ⟨8581209279597946741343653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11441612372797262321791537 8581209279597946741343653)
                    ·
                      refine ⟨1608976739924615014001935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8581209279597946741343653 1608976739924615014001935)
                      ·
                        rfl

theorem cell23_3133471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_3133471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133471 prefixEnd_3133471 := by exact prefixLift 3133471
  have htrace : WordTrace (prefixWord ++ tailWord_3133471) baseStart_3133471 baseEnd_3133471 := by
    simpa [prefixWord, tailWord_3133471, baseEnd_3133471] using wordTrace_append hprefix tailTrace_3133471
  have hstable : (prefixWord ++ tailWord_3133471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133471).length < 2 ^ (prefixWord ++ tailWord_3133471).sum := by decide
  have hdescent : baseEnd_3133471 < baseStart_3133471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133475 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 2, 2, 2]
def baseStart_3133475 : Nat := 118140960795 + 3133475 * 2 ^ 59
def prefixEnd_3133475 : Nat := 4983230072969 + 3 ^ 40 * 3133475 * 2
def baseEnd_3133475 : Nat := 1608978793847232998351917

theorem tailTrace_3133475 : CollatzResearch.WordTrace tailWord_3133475 prefixEnd_3133475 1608978793847232998351917 := by
  unfold tailWord_3133475
  simp only [CollatzResearch.WordTrace]
  refine ⟨114287222322962704769249879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76191481548641803179499919 114287222322962704769249879)
  ·
    refine ⟨171430833484444057153874819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114287222322962704769249879 171430833484444057153874819)
    ·
      refine ⟨257146250226666085730812229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171430833484444057153874819 257146250226666085730812229)
      ·
        refine ⟨48214921917499891074527293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257146250226666085730812229 48214921917499891074527293)
        ·
          refine ⟨18080595719062459152947735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48214921917499891074527293 18080595719062459152947735)
          ·
            refine ⟨27120893578593688729421603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18080595719062459152947735 27120893578593688729421603)
            ·
              refine ⟨40681340367890533094132405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27120893578593688729421603 40681340367890533094132405)
              ·
                refine ⟨3813875659489737477574913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40681340367890533094132405 3813875659489737477574913)
                ·
                  refine ⟨2860406744617303108181185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3813875659489737477574913 2860406744617303108181185)
                  ·
                    refine ⟨2145305058462977331135889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2860406744617303108181185 2145305058462977331135889)
                    ·
                      refine ⟨1608978793847232998351917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145305058462977331135889 1608978793847232998351917)
                      ·
                        rfl

theorem cell23_3133475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_3133475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133475 prefixEnd_3133475 := by exact prefixLift 3133475
  have htrace : WordTrace (prefixWord ++ tailWord_3133475) baseStart_3133475 baseEnd_3133475 := by
    simpa [prefixWord, tailWord_3133475, baseEnd_3133475] using wordTrace_append hprefix tailTrace_3133475
  have hstable : (prefixWord ++ tailWord_3133475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133475).length < 2 ^ (prefixWord ++ tailWord_3133475).sum := by decide
  have hdescent : baseEnd_3133475 < baseStart_3133475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133511 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 4, 5]
def baseStart_3133511 : Nat := 118140960795 + 3133511 * 2 ^ 59
def prefixEnd_3133511 : Nat := 4983230072969 + 3 ^ 40 * 3133511 * 2
def baseEnd_3133511 : Nat := 536332426383598285833917

theorem tailTrace_3133511 : CollatzResearch.WordTrace tailWord_3133511 prefixEnd_3133511 536332426383598285833917 := by
  unfold tailWord_3133511
  simp only [CollatzResearch.WordTrace]
  refine ⟨114288535350832282917560387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76192356900554855278373591 114288535350832282917560387)
  ·
    refine ⟨171432803026248424376340581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114288535350832282917560387 171432803026248424376340581)
    ·
      refine ⟨32143650567421579570563859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171432803026248424376340581 32143650567421579570563859)
      ·
        refine ⟨48215475851132369355845789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32143650567421579570563859 48215475851132369355845789)
        ·
          refine ⟨18080803444174638508442171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48215475851132369355845789 18080803444174638508442171)
          ·
            refine ⟨27121205166261957762663257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18080803444174638508442171 27121205166261957762663257)
            ·
              refine ⟨20340903874696468321997443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27121205166261957762663257 20340903874696468321997443)
              ·
                refine ⟨30511355812044702482996165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20340903874696468321997443 30511355812044702482996165)
                ·
                  refine ⟨5720879214758381715561781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30511355812044702482996165 5720879214758381715561781)
                  ·
                    refine ⟨536332426383598285833917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5720879214758381715561781 536332426383598285833917)
                    ·
                      rfl

theorem cell23_3133511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_3133511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133511 prefixEnd_3133511 := by exact prefixLift 3133511
  have htrace : WordTrace (prefixWord ++ tailWord_3133511) baseStart_3133511 baseEnd_3133511 := by
    simpa [prefixWord, tailWord_3133511, baseEnd_3133511] using wordTrace_append hprefix tailTrace_3133511
  have hstable : (prefixWord ++ tailWord_3133511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133511).length < 2 ^ (prefixWord ++ tailWord_3133511).sum := by decide
  have hdescent : baseEnd_3133511 < baseStart_3133511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133571 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 8]
def baseStart_3133571 : Nat := 118140960795 + 3133571 * 2 ^ 59
def prefixEnd_3133571 : Nat := 4983230072969 + 3 ^ 40 * 3133571 * 2
def baseEnd_3133571 : Nat := 178780898665562735861275

theorem tailTrace_3133571 : CollatzResearch.WordTrace tailWord_3133571 prefixEnd_3133571 178780898665562735861275 := by
  unfold tailWord_3133571
  simp only [CollatzResearch.WordTrace]
  refine ⟨114290723730614913164744567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76193815820409942109829711 114290723730614913164744567)
  ·
    refine ⟨171436085595922369747116851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114290723730614913164744567 171436085595922369747116851)
    ·
      refine ⟨257154128393883554620675277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171436085595922369747116851 257154128393883554620675277)
      ·
        refine ⟨96432798147706332982753229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257154128393883554620675277 96432798147706332982753229)
        ·
          refine ⟨36162299305389874868532461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96432798147706332982753229 36162299305389874868532461)
          ·
            refine ⟨13560862239521203075699673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36162299305389874868532461 13560862239521203075699673)
            ·
              refine ⟨10170646679640902306774755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13560862239521203075699673 10170646679640902306774755)
              ·
                refine ⟨15255970019461353460162133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10170646679640902306774755 15255970019461353460162133)
                ·
                  refine ⟨178780898665562735861275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15255970019461353460162133 178780898665562735861275)
                  ·
                    rfl

theorem cell23_3133571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 8].length) (baseStart_3133571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133571 prefixEnd_3133571 := by exact prefixLift 3133571
  have htrace : WordTrace (prefixWord ++ tailWord_3133571) baseStart_3133571 baseEnd_3133571 := by
    simpa [prefixWord, tailWord_3133571, baseEnd_3133571] using wordTrace_append hprefix tailTrace_3133571
  have hstable : (prefixWord ++ tailWord_3133571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133571).length < 2 ^ (prefixWord ++ tailWord_3133571).sum := by decide
  have hdescent : baseEnd_3133571 < baseStart_3133571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133575 : List Nat := [1, 1, 4, 2, 1, 1, 2, 6, 1, 4]
def baseStart_3133575 : Nat := 118140960795 + 3133575 * 2 ^ 59
def prefixEnd_3133575 : Nat := 4983230072969 + 3 ^ 40 * 3133575 * 2
def baseEnd_3133575 : Nat := 536343380637560869033819

theorem tailTrace_3133575 : CollatzResearch.WordTrace tailWord_3133575 prefixEnd_3133575 536343380637560869033819 := by
  unfold tailWord_3133575
  simp only [CollatzResearch.WordTrace]
  refine ⟨114290869622600421847890179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76193913081733614565260119 114290869622600421847890179)
  ·
    refine ⟨171436304433900632771835269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114290869622600421847890179 171436304433900632771835269)
    ·
      refine ⟨32144307081356368644719113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171436304433900632771835269 32144307081356368644719113)
      ·
        refine ⟨24108230311017276483539335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32144307081356368644719113 24108230311017276483539335)
        ·
          refine ⟨36162345466525914725309003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24108230311017276483539335 36162345466525914725309003)
          ·
            refine ⟨54243518199788872087963505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36162345466525914725309003 54243518199788872087963505)
            ·
              refine ⟨40682638649841654065972629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54243518199788872087963505 40682638649841654065972629)
              ·
                refine ⟨1906998686711327534342467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40682638649841654065972629 1906998686711327534342467)
                ·
                  refine ⟨2860498030066991301513701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906998686711327534342467 2860498030066991301513701)
                  ·
                    refine ⟨536343380637560869033819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2860498030066991301513701 536343380637560869033819)
                    ·
                      rfl

theorem cell23_3133575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_3133575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133575 prefixEnd_3133575 := by exact prefixLift 3133575
  have htrace : WordTrace (prefixWord ++ tailWord_3133575) baseStart_3133575 baseEnd_3133575 := by
    simpa [prefixWord, tailWord_3133575, baseEnd_3133575] using wordTrace_append hprefix tailTrace_3133575
  have hstable : (prefixWord ++ tailWord_3133575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133575).length < 2 ^ (prefixWord ++ tailWord_3133575).sum := by decide
  have hdescent : baseEnd_3133575 < baseStart_3133575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133602 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3133602 : Nat := 118140960795 + 3133602 * 2 ^ 59
def prefixEnd_3133602 : Nat := 4983230072969 + 3 ^ 40 * 3133602 * 2
def baseEnd_3133602 : Nat := 1609044005890354001463833

theorem tailTrace_3133602 : CollatzResearch.WordTrace tailWord_3133602 prefixEnd_3133602 1609044005890354001463833 := by
  unfold tailWord_3133602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28572963598375651364780765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76194569595668403639415373 28572963598375651364780765)
  ·
    refine ⟨10714861349390869261792787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28572963598375651364780765 10714861349390869261792787)
    ·
      refine ⟨16072292024086303892689181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10714861349390869261792787 16072292024086303892689181)
      ·
        refine ⟨6027109509032363959758443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16072292024086303892689181 6027109509032363959758443)
        ·
          refine ⟨9040664263548545939637665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6027109509032363959758443 9040664263548545939637665)
          ·
            refine ⟨6780498197661409454728249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9040664263548545939637665 6780498197661409454728249)
            ·
              refine ⟨5085373648246057091046187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6780498197661409454728249 5085373648246057091046187)
              ·
                refine ⟨7628060472369085636569281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5085373648246057091046187 7628060472369085636569281)
                ·
                  refine ⟨5721045354276814227426961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7628060472369085636569281 5721045354276814227426961)
                  ·
                    refine ⟨4290784015707610670570221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5721045354276814227426961 4290784015707610670570221)
                    ·
                      refine ⟨1609044005890354001463833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4290784015707610670570221 1609044005890354001463833)
                      ·
                        rfl

theorem cell23_3133602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3133602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133602 prefixEnd_3133602 := by exact prefixLift 3133602
  have htrace : WordTrace (prefixWord ++ tailWord_3133602) baseStart_3133602 baseEnd_3133602 := by
    simpa [prefixWord, tailWord_3133602, baseEnd_3133602] using wordTrace_append hprefix tailTrace_3133602
  have hstable : (prefixWord ++ tailWord_3133602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133602).length < 2 ^ (prefixWord ++ tailWord_3133602).sum := by decide
  have hdescent : baseEnd_3133602 < baseStart_3133602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133625 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 2, 3, 2]
def baseStart_3133625 : Nat := 118140960795 + 3133625 * 2 ^ 59
def prefixEnd_3133625 : Nat := 4983230072969 + 3 ^ 40 * 3133625 * 2
def baseEnd_3133625 : Nat := 1609055815945407411476227

theorem tailTrace_3133625 : CollatzResearch.WordTrace tailWord_3133625 prefixEnd_3133625 1609055815945407411476227 := by
  unfold tailWord_3133625
  simp only [CollatzResearch.WordTrace]
  refine ⟨114292693272419280387210329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76195128848279520258140219 114292693272419280387210329)
  ·
    refine ⟨85719519954314460290407747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114292693272419280387210329 85719519954314460290407747)
    ·
      refine ⟨128579279931471690435611621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85719519954314460290407747 128579279931471690435611621)
      ·
        refine ⟨24108614987150941956677179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128579279931471690435611621 24108614987150941956677179)
        ·
          refine ⟨36162922480726412935015769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24108614987150941956677179 36162922480726412935015769)
          ·
            refine ⟨27122191860544809701261827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36162922480726412935015769 27122191860544809701261827)
            ·
              refine ⟨40683287790817214551892741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27122191860544809701261827 40683287790817214551892741)
              ·
                refine ⟨7628116460778227728479889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40683287790817214551892741 7628116460778227728479889)
                ·
                  refine ⟨5721087345583670796359917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7628116460778227728479889 5721087345583670796359917)
                  ·
                    refine ⟨2145407754593876548634969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5721087345583670796359917 2145407754593876548634969)
                    ·
                      refine ⟨1609055815945407411476227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145407754593876548634969 1609055815945407411476227)
                      ·
                        rfl

theorem cell23_3133625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_3133625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133625 prefixEnd_3133625 := by exact prefixLift 3133625
  have htrace : WordTrace (prefixWord ++ tailWord_3133625) baseStart_3133625 baseEnd_3133625 := by
    simpa [prefixWord, tailWord_3133625, baseEnd_3133625] using wordTrace_append hprefix tailTrace_3133625
  have hstable : (prefixWord ++ tailWord_3133625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133625).length < 2 ^ (prefixWord ++ tailWord_3133625).sum := by decide
  have hdescent : baseEnd_3133625 < baseStart_3133625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133631 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 5, 6]
def baseStart_3133631 : Nat := 118140960795 + 3133631 * 2 ^ 59
def prefixEnd_3133631 : Nat := 4983230072969 + 3 ^ 40 * 3133631 * 2
def baseEnd_3133631 : Nat := 536352965609778129333733

theorem tailTrace_3133631 : CollatzResearch.WordTrace tailWord_3133631 prefixEnd_3133631 536352965609778129333733 := by
  unfold tailWord_3133631
  simp only [CollatzResearch.WordTrace]
  refine ⟨114292912110397543411928747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76195274740265028941285831 114292912110397543411928747)
  ·
    refine ⟨171439368165596315117893121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114292912110397543411928747 171439368165596315117893121)
    ·
      refine ⟨128579526124197236338419841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171439368165596315117893121 128579526124197236338419841)
      ·
        refine ⟨96434644593147927253814881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128579526124197236338419841 96434644593147927253814881)
        ·
          refine ⟨72325983444860945440361161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96434644593147927253814881 72325983444860945440361161)
          ·
            refine ⟨54244487583645709080270871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72325983444860945440361161 54244487583645709080270871)
            ·
              refine ⟨81366731375468563620406307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54244487583645709080270871 81366731375468563620406307)
              ·
                refine ⟨122050097063202845430609461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81366731375468563620406307 122050097063202845430609461)
                ·
                  refine ⟨11442196599675266759119637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122050097063202845430609461 11442196599675266759119637)
                  ·
                    refine ⟨536352965609778129333733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11442196599675266759119637 536352965609778129333733)
                    ·
                      rfl

theorem cell23_3133631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_3133631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133631 prefixEnd_3133631 := by exact prefixLift 3133631
  have htrace : WordTrace (prefixWord ++ tailWord_3133631) baseStart_3133631 baseEnd_3133631 := by
    simpa [prefixWord, tailWord_3133631, baseEnd_3133631] using wordTrace_append hprefix tailTrace_3133631
  have hstable : (prefixWord ++ tailWord_3133631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133631).length < 2 ^ (prefixWord ++ tailWord_3133631).sum := by decide
  have hdescent : baseEnd_3133631 < baseStart_3133631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
