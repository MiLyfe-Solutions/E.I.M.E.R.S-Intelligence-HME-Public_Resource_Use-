import V185TrunkScan19Chunk048

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_491490 : List Nat := [3, 3, 3, 1, 2, 1, 6]
def baseStart_491490 : Nat := 118140960795 + 491490 * 2 ^ 59
def prefixEnd_491490 : Nat := 4983230072969 + 3 ^ 40 * 491490 * 2
def baseEnd_491490 : Nat := 49850984074743165790555

theorem tailTrace_491490 : CollatzResearch.WordTrace tailWord_491490 prefixEnd_491490 49850984074743165790555 := by
  unfold tailWord_491490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4481528247355786163579981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11950741992948763102879949 4481528247355786163579981)
  ·
    refine ⟨1680573092758419811342493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4481528247355786163579981 1680573092758419811342493)
    ·
      refine ⟨630214909784407429253435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1680573092758419811342493 630214909784407429253435)
      ·
        refine ⟨945322364676611143880153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630214909784407429253435 945322364676611143880153)
        ·
          refine ⟨708991773507458357910115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945322364676611143880153 708991773507458357910115)
          ·
            refine ⟨1063487660261187536865173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708991773507458357910115 1063487660261187536865173)
            ·
              refine ⟨49850984074743165790555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1063487660261187536865173 49850984074743165790555)
              ·
                rfl

theorem cell19_491490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_491490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491490 prefixEnd_491490 := by exact prefixLift 491490
  have htrace : WordTrace (prefixWord ++ tailWord_491490) baseStart_491490 baseEnd_491490 := by
    simpa [prefixWord, tailWord_491490, baseEnd_491490] using wordTrace_append hprefix tailTrace_491490
  have hstable : (prefixWord ++ tailWord_491490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491490).length < 2 ^ (prefixWord ++ tailWord_491490).sum := by decide
  have hdescent : baseEnd_491490 < baseStart_491490 := by decide
  rcases family_descends (prefixWord ++ tailWord_491490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491524 : List Nat := [2, 3, 2, 4, 2, 1, 2, 3]
def baseStart_491524 : Nat := 118140960795 + 491524 * 2 ^ 59
def prefixEnd_491524 : Nat := 4983230072969 + 3 ^ 40 * 491524 * 2
def baseEnd_491524 : Nat := 149563297908527492616017

theorem tailTrace_491524 : CollatzResearch.WordTrace tailWord_491524 prefixEnd_491524 149563297908527492616017 := by
  unfold tailWord_491524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8963676535649984230528813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11951568714199978974038417 8963676535649984230528813)
  ·
    refine ⟨3361378700868744086448305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8963676535649984230528813 3361378700868744086448305)
    ·
      refine ⟨2521034025651558064836229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3361378700868744086448305 2521034025651558064836229)
      ·
        refine ⟨472693879809667137156793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2521034025651558064836229 472693879809667137156793)
        ·
          refine ⟨354520409857250352867595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472693879809667137156793 354520409857250352867595)
          ·
            refine ⟨531780614785875529301393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354520409857250352867595 531780614785875529301393)
            ·
              refine ⟨398835461089406646976045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531780614785875529301393 398835461089406646976045)
              ·
                refine ⟨149563297908527492616017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398835461089406646976045 149563297908527492616017)
                ·
                  rfl

theorem cell19_491524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_491524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491524 prefixEnd_491524 := by exact prefixLift 491524
  have htrace : WordTrace (prefixWord ++ tailWord_491524) baseStart_491524 baseEnd_491524 := by
    simpa [prefixWord, tailWord_491524, baseEnd_491524] using wordTrace_append hprefix tailTrace_491524
  have hstable : (prefixWord ++ tailWord_491524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491524).length < 2 ^ (prefixWord ++ tailWord_491524).sum := by decide
  have hdescent : baseEnd_491524 < baseStart_491524 := by decide
  rcases family_descends (prefixWord ++ tailWord_491524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491530 : List Nat := [3, 1, 2, 2, 4, 1, 1, 5]
def baseStart_491530 : Nat := 118140960795 + 491530 * 2 ^ 59
def prefixEnd_491530 : Nat := 4983230072969 + 3 ^ 40 * 491530 * 2
def baseEnd_491530 : Nat := 149565123617521256482667

theorem tailTrace_491530 : CollatzResearch.WordTrace tailWord_491530 prefixEnd_491530 149565123617521256482667 := by
  unfold tailWord_491530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4481892977319557871444011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11951714606185487657184029 4481892977319557871444011)
  ·
    refine ⟨6722839465979336807166017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4481892977319557871444011 6722839465979336807166017)
    ·
      refine ⟨5042129599484502605374513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6722839465979336807166017 5042129599484502605374513)
      ·
        refine ⟨3781597199613376954030885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5042129599484502605374513 3781597199613376954030885)
        ·
          refine ⟨709049474927508178880791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3781597199613376954030885 709049474927508178880791)
          ·
            refine ⟨1063574212391262268321187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709049474927508178880791 1063574212391262268321187)
            ·
              refine ⟨1595361318586893402481781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063574212391262268321187 1595361318586893402481781)
              ·
                refine ⟨149565123617521256482667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1595361318586893402481781 149565123617521256482667)
                ·
                  rfl

theorem cell19_491530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_491530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491530 prefixEnd_491530 := by exact prefixLift 491530
  have htrace : WordTrace (prefixWord ++ tailWord_491530) baseStart_491530 baseEnd_491530 := by
    simpa [prefixWord, tailWord_491530, baseEnd_491530] using wordTrace_append hprefix tailTrace_491530
  have hstable : (prefixWord ++ tailWord_491530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491530).length < 2 ^ (prefixWord ++ tailWord_491530).sum := by decide
  have hdescent : baseEnd_491530 < baseStart_491530 := by decide
  rcases family_descends (prefixWord ++ tailWord_491530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491532 : List Nat := [2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_491532 : Nat := 118140960795 + 491532 * 2 ^ 59
def prefixEnd_491532 : Nat := 4983230072969 + 3 ^ 40 * 491532 * 2
def baseEnd_491532 : Nat := 149565732187185844438217

theorem tailTrace_491532 : CollatzResearch.WordTrace tailWord_491532 prefixEnd_491532 149565732187185844438217 := by
  unfold tailWord_491532
  simp only [CollatzResearch.WordTrace]
  refine ⟨8963822427635492913674425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11951763236847323884899233 8963822427635492913674425)
  ·
    refine ⟨6722866820726619685255819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8963822427635492913674425 6722866820726619685255819)
    ·
      refine ⟨10084300231089929527883729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6722866820726619685255819 10084300231089929527883729)
      ·
        refine ⟨7563225173317447145912797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10084300231089929527883729 7563225173317447145912797)
        ·
          refine ⟨2836209439994042679717299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7563225173317447145912797 2836209439994042679717299)
          ·
            refine ⟨4254314159991064019575949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836209439994042679717299 4254314159991064019575949)
            ·
              refine ⟨1595367809996649007340981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4254314159991064019575949 1595367809996649007340981)
              ·
                refine ⟨149565732187185844438217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1595367809996649007340981 149565732187185844438217)
                ·
                  rfl

theorem cell19_491532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_491532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491532 prefixEnd_491532 := by exact prefixLift 491532
  have htrace : WordTrace (prefixWord ++ tailWord_491532) baseStart_491532 baseEnd_491532 := by
    simpa [prefixWord, tailWord_491532, baseEnd_491532] using wordTrace_append hprefix tailTrace_491532
  have hstable : (prefixWord ++ tailWord_491532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491532).length < 2 ^ (prefixWord ++ tailWord_491532).sum := by decide
  have hdescent : baseEnd_491532 < baseStart_491532 := by decide
  rcases family_descends (prefixWord ++ tailWord_491532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491549 : List Nat := [1, 4, 2, 2, 2, 3, 5]
def baseStart_491549 : Nat := 118140960795 + 491549 * 2 ^ 59
def prefixEnd_491549 : Nat := 4983230072969 + 3 ^ 40 * 491549 * 2
def baseEnd_491549 : Nat := 49856968343111614020131

theorem tailTrace_491549 : CollatzResearch.WordTrace tailWord_491549 prefixEnd_491549 49856968343111614020131 := by
  unfold tailWord_491549
  simp only [CollatzResearch.WordTrace]
  refine ⟨17928264896209397730717701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11952176597472931820478467 17928264896209397730717701)
  ·
    refine ⟨3361549668039262074509569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17928264896209397730717701 3361549668039262074509569)
    ·
      refine ⟨2521162251029446555882177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3361549668039262074509569 2521162251029446555882177)
      ·
        refine ⟨1890871688272084916911633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2521162251029446555882177 1890871688272084916911633)
        ·
          refine ⟨1418153766204063687683725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1890871688272084916911633 1418153766204063687683725)
          ·
            refine ⟨531807662326523882881397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1418153766204063687683725 531807662326523882881397)
            ·
              refine ⟨49856968343111614020131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 531807662326523882881397 49856968343111614020131)
              ·
                rfl

theorem cell19_491549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_491549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491549 prefixEnd_491549 := by exact prefixLift 491549
  have htrace : WordTrace (prefixWord ++ tailWord_491549) baseStart_491549 baseEnd_491549 := by
    simpa [prefixWord, tailWord_491549, baseEnd_491549] using wordTrace_append hprefix tailTrace_491549
  have hstable : (prefixWord ++ tailWord_491549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491549).length < 2 ^ (prefixWord ++ tailWord_491549).sum := by decide
  have hdescent : baseEnd_491549 < baseStart_491549 := by decide
  rcases family_descends (prefixWord ++ tailWord_491549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491570 : List Nat := [3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_491570 : Nat := 118140960795 + 491570 * 2 ^ 59
def prefixEnd_491570 : Nat := 4983230072969 + 3 ^ 40 * 491570 * 2
def baseEnd_491570 : Nat := 149577295010813015593669

theorem tailTrace_491570 : CollatzResearch.WordTrace tailWord_491570 prefixEnd_491570 149577295010813015593669 := by
  unfold tailWord_491570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4482257707283329579308041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11952687219422212211488109 4482257707283329579308041)
  ·
    refine ⟨3361693280462497184481031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4482257707283329579308041 3361693280462497184481031)
    ·
      refine ⟨5042539920693745776721547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3361693280462497184481031 5042539920693745776721547)
      ·
        refine ⟨7563809881040618665082321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5042539920693745776721547 7563809881040618665082321)
        ·
          refine ⟨5672857410780463998811741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7563809881040618665082321 5672857410780463998811741)
          ·
            refine ⟨2127321529042673999554403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5672857410780463998811741 2127321529042673999554403)
            ·
              refine ⟨3190982293564010999331605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127321529042673999554403 3190982293564010999331605)
              ·
                refine ⟨149577295010813015593669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3190982293564010999331605 149577295010813015593669)
                ·
                  rfl

theorem cell19_491570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_491570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491570 prefixEnd_491570 := by exact prefixLift 491570
  have htrace : WordTrace (prefixWord ++ tailWord_491570) baseStart_491570 baseEnd_491570 := by
    simpa [prefixWord, tailWord_491570, baseEnd_491570] using wordTrace_append hprefix tailTrace_491570
  have hstable : (prefixWord ++ tailWord_491570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491570).length < 2 ^ (prefixWord ++ tailWord_491570).sum := by decide
  have hdescent : baseEnd_491570 < baseStart_491570 := by decide
  rcases family_descends (prefixWord ++ tailWord_491570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491644 : List Nat := [2, 2, 2, 1, 1, 5, 3, 3]
def baseStart_491644 : Nat := 118140960795 + 491644 * 2 ^ 59
def prefixEnd_491644 : Nat := 4983230072969 + 3 ^ 40 * 491644 * 2
def baseEnd_491644 : Nat := 149599812088402769949023

theorem tailTrace_491644 : CollatzResearch.WordTrace tailWord_491644 prefixEnd_491644 149599812088402769949023 := by
  unfold tailWord_491644
  simp only [CollatzResearch.WordTrace]
  refine ⟨8965864915432614477712993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11954486553910152636950657 8965864915432614477712993)
  ·
    refine ⟨6724398686574460858284745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8965864915432614477712993 6724398686574460858284745)
    ·
      refine ⟨5043299014930845643713559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6724398686574460858284745 5043299014930845643713559)
      ·
        refine ⟨7564948522396268465570339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5043299014930845643713559 7564948522396268465570339)
        ·
          refine ⟨11347422783594402698355509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7564948522396268465570339 11347422783594402698355509)
          ·
            refine ⟨1063820885961975252970829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11347422783594402698355509 1063820885961975252970829)
            ·
              refine ⟨398932832235740719864061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1063820885961975252970829 398932832235740719864061)
              ·
                refine ⟨149599812088402769949023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398932832235740719864061 149599812088402769949023)
                ·
                  rfl

theorem cell19_491644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_491644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491644 prefixEnd_491644 := by exact prefixLift 491644
  have htrace : WordTrace (prefixWord ++ tailWord_491644) baseStart_491644 baseEnd_491644 := by
    simpa [prefixWord, tailWord_491644, baseEnd_491644] using wordTrace_append hprefix tailTrace_491644
  have hstable : (prefixWord ++ tailWord_491644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491644).length < 2 ^ (prefixWord ++ tailWord_491644).sum := by decide
  have hdescent : baseEnd_491644 < baseStart_491644 := by decide
  rcases family_descends (prefixWord ++ tailWord_491644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491697 : List Nat := [1, 2, 2, 5, 3, 1, 2, 3]
def baseStart_491697 : Nat := 118140960795 + 491697 * 2 ^ 59
def prefixEnd_491697 : Nat := 4983230072969 + 3 ^ 40 * 491697 * 2
def baseEnd_491697 : Nat := 149615939184514350771101

theorem tailTrace_491697 : CollatzResearch.WordTrace tailWord_491697 prefixEnd_491697 149615939184514350771101 := by
  unfold tailWord_491697
  simp only [CollatzResearch.WordTrace]
  refine ⟨17933662899673219007105345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11955775266448812671403563 17933662899673219007105345)
  ·
    refine ⟨13450247174754914255329009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17933662899673219007105345 13450247174754914255329009)
    ·
      refine ⟨10087685381066185691496757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13450247174754914255329009 10087685381066185691496757)
      ·
        refine ⟨945720504474954908577821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10087685381066185691496757 945720504474954908577821)
        ·
          refine ⟨354645189178108090716683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 945720504474954908577821 354645189178108090716683)
          ·
            refine ⟨531967783767162136075025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354645189178108090716683 531967783767162136075025)
            ·
              refine ⟨398975837825371602056269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531967783767162136075025 398975837825371602056269)
              ·
                refine ⟨149615939184514350771101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398975837825371602056269 149615939184514350771101)
                ·
                  rfl

theorem cell19_491697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 3].length) (baseStart_491697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491697 prefixEnd_491697 := by exact prefixLift 491697
  have htrace : WordTrace (prefixWord ++ tailWord_491697) baseStart_491697 baseEnd_491697 := by
    simpa [prefixWord, tailWord_491697, baseEnd_491697] using wordTrace_append hprefix tailTrace_491697
  have hstable : (prefixWord ++ tailWord_491697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491697).length < 2 ^ (prefixWord ++ tailWord_491697).sum := by decide
  have hdescent : baseEnd_491697 < baseStart_491697 := by decide
  rcases family_descends (prefixWord ++ tailWord_491697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491703 : List Nat := [1, 1, 3, 1, 4, 3, 1, 5]
def baseStart_491703 : Nat := 118140960795 + 491703 * 2 ^ 59
def prefixEnd_491703 : Nat := 4983230072969 + 3 ^ 40 * 491703 * 2
def baseEnd_491703 : Nat := 149617764893508114637751

theorem tailTrace_491703 : CollatzResearch.WordTrace tailWord_491703 prefixEnd_491703 149617764893508114637751 := by
  unfold tailWord_491703
  simp only [CollatzResearch.WordTrace]
  refine ⟨17933881737651482031823763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11955921158434321354549175 17933881737651482031823763)
  ·
    refine ⟨26900822606477223047735645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17933881737651482031823763 26900822606477223047735645)
    ·
      refine ⟨10087808477428958642900867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26900822606477223047735645 10087808477428958642900867)
      ·
        refine ⟨15131712716143437964351301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10087808477428958642900867 15131712716143437964351301)
        ·
          refine ⟨2837196134276894618315869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15131712716143437964351301 2837196134276894618315869)
          ·
            refine ⟨1063948550353835481868451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2837196134276894618315869 1063948550353835481868451)
            ·
              refine ⟨1595922825530753222802677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063948550353835481868451 1595922825530753222802677)
              ·
                refine ⟨149617764893508114637751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1595922825530753222802677 149617764893508114637751)
                ·
                  rfl

theorem cell19_491703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_491703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491703 prefixEnd_491703 := by exact prefixLift 491703
  have htrace : WordTrace (prefixWord ++ tailWord_491703) baseStart_491703 baseEnd_491703 := by
    simpa [prefixWord, tailWord_491703, baseEnd_491703] using wordTrace_append hprefix tailTrace_491703
  have hstable : (prefixWord ++ tailWord_491703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491703).length < 2 ^ (prefixWord ++ tailWord_491703).sum := by decide
  have hdescent : baseEnd_491703 < baseStart_491703 := by decide
  rcases family_descends (prefixWord ++ tailWord_491703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491868 : List Nat := [2, 2, 4, 3, 1, 2, 2, 3]
def baseStart_491868 : Nat := 118140960795 + 491868 * 2 ^ 59
def prefixEnd_491868 : Nat := 4983230072969 + 3 ^ 40 * 491868 * 2
def baseEnd_491868 : Nat := 149667971890836620970635

theorem tailTrace_491868 : CollatzResearch.WordTrace tailWord_491868 prefixEnd_491868 149667971890836620970635 := by
  unfold tailWord_491868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8969949891026857605790129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11959933188035810141053505 8969949891026857605790129)
  ·
    refine ⟨6727462418270143204342597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8969949891026857605790129 6727462418270143204342597)
    ·
      refine ⟨1261399203425651850814237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6727462418270143204342597 1261399203425651850814237)
      ·
        refine ⟨473024701284619444055339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1261399203425651850814237 473024701284619444055339)
        ·
          refine ⟨709537051926929166083009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473024701284619444055339 709537051926929166083009)
          ·
            refine ⟨532152788945196874562257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709537051926929166083009 532152788945196874562257)
            ·
              refine ⟨399114591708897655921693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532152788945196874562257 399114591708897655921693)
              ·
                refine ⟨149667971890836620970635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399114591708897655921693 149667971890836620970635)
                ·
                  rfl

theorem cell19_491868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_491868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491868 prefixEnd_491868 := by exact prefixLift 491868
  have htrace : WordTrace (prefixWord ++ tailWord_491868) baseStart_491868 baseEnd_491868 := by
    simpa [prefixWord, tailWord_491868, baseEnd_491868] using wordTrace_append hprefix tailTrace_491868
  have hstable : (prefixWord ++ tailWord_491868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491868).length < 2 ^ (prefixWord ++ tailWord_491868).sum := by decide
  have hdescent : baseEnd_491868 < baseStart_491868 := by decide
  rcases family_descends (prefixWord ++ tailWord_491868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491893 : List Nat := [1, 3, 4, 1, 2, 1, 7]
def baseStart_491893 : Nat := 118140960795 + 491893 * 2 ^ 59
def prefixEnd_491893 : Nat := 4983230072969 + 3 ^ 40 * 491893 * 2
def baseEnd_491893 : Nat := 49891859670547990138337

theorem tailTrace_491893 : CollatzResearch.WordTrace tailWord_491893 prefixEnd_491893 49891859670547990138337 := by
  unfold tailWord_491893
  simp only [CollatzResearch.WordTrace]
  refine ⟨17940811606963144481240333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11960541071308762987493555 17940811606963144481240333)
  ·
    refine ⟨6727804352611179180465125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17940811606963144481240333 6727804352611179180465125)
    ·
      refine ⟨1261463316114596096337211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6727804352611179180465125 1261463316114596096337211)
      ·
        refine ⟨1892194974171894144505817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1261463316114596096337211 1892194974171894144505817)
        ·
          refine ⟨1419146230628920608379363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1892194974171894144505817 1419146230628920608379363)
          ·
            refine ⟨2128719345943380912569045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419146230628920608379363 2128719345943380912569045)
            ·
              refine ⟨49891859670547990138337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2128719345943380912569045 49891859670547990138337)
              ·
                rfl

theorem cell19_491893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_491893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491893 prefixEnd_491893 := by exact prefixLift 491893
  have htrace : WordTrace (prefixWord ++ tailWord_491893) baseStart_491893 baseEnd_491893 := by
    simpa [prefixWord, tailWord_491893, baseEnd_491893] using wordTrace_append hprefix tailTrace_491893
  have hstable : (prefixWord ++ tailWord_491893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491893).length < 2 ^ (prefixWord ++ tailWord_491893).sum := by decide
  have hdescent : baseEnd_491893 < baseStart_491893 := by decide
  rcases family_descends (prefixWord ++ tailWord_491893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491912 : List Nat := [2, 1, 3, 3, 1, 1, 4, 4]
def baseStart_491912 : Nat := 118140960795 + 491912 * 2 ^ 59
def prefixEnd_491912 : Nat := 4983230072969 + 3 ^ 40 * 491912 * 2
def baseEnd_491912 : Nat := 149681360423457555992737

theorem tailTrace_491912 : CollatzResearch.WordTrace tailWord_491912 prefixEnd_491912 149681360423457555992737 := by
  unfold tailWord_491912
  simp only [CollatzResearch.WordTrace]
  refine ⟨8970752296947155363090995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11961003062596207150787993 8970752296947155363090995)
  ·
    refine ⟨13456128445420733044636493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8970752296947155363090995 13456128445420733044636493)
    ·
      refine ⟨5046048167032774891738685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13456128445420733044636493 5046048167032774891738685)
      ·
        refine ⟨1892268062637290584402007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5046048167032774891738685 1892268062637290584402007)
        ·
          refine ⟨2838402093955935876603011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892268062637290584402007 2838402093955935876603011)
          ·
            refine ⟨4257603140933903814904517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838402093955935876603011 4257603140933903814904517)
            ·
              refine ⟨798300588925106965294597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4257603140933903814904517 798300588925106965294597)
              ·
                refine ⟨149681360423457555992737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 798300588925106965294597 149681360423457555992737)
                ·
                  rfl

theorem cell19_491912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_491912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491912 prefixEnd_491912 := by exact prefixLift 491912
  have htrace : WordTrace (prefixWord ++ tailWord_491912) baseStart_491912 baseEnd_491912 := by
    simpa [prefixWord, tailWord_491912, baseEnd_491912] using wordTrace_append hprefix tailTrace_491912
  have hstable : (prefixWord ++ tailWord_491912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491912).length < 2 ^ (prefixWord ++ tailWord_491912).sum := by decide
  have hdescent : baseEnd_491912 < baseStart_491912 := by decide
  rcases family_descends (prefixWord ++ tailWord_491912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491946 : List Nat := [3, 1, 6, 1, 1, 7]
def baseStart_491946 : Nat := 118140960795 + 491946 * 2 ^ 59
def prefixEnd_491946 : Nat := 4983230072969 + 3 ^ 40 * 491946 * 2
def baseEnd_491946 : Nat := 16632411789750616804121

theorem tailTrace_491946 : CollatzResearch.WordTrace tailWord_491946 prefixEnd_491946 16632411789750616804121 := by
  unfold tailWord_491946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4485686168942783633229923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11961829783847423021946461 4485686168942783633229923)
  ·
    refine ⟨6728529253414175449844885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4485686168942783633229923 6728529253414175449844885)
    ·
      refine ⟨315399808753789474211479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6728529253414175449844885 315399808753789474211479)
      ·
        refine ⟨473099713130684211317219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315399808753789474211479 473099713130684211317219)
        ·
          refine ⟨709649569696026316975829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473099713130684211317219 709649569696026316975829)
          ·
            refine ⟨16632411789750616804121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 709649569696026316975829 16632411789750616804121)
            ·
              rfl

theorem cell19_491946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 7].length) (baseStart_491946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491946 prefixEnd_491946 := by exact prefixLift 491946
  have htrace : WordTrace (prefixWord ++ tailWord_491946) baseStart_491946 baseEnd_491946 := by
    simpa [prefixWord, tailWord_491946, baseEnd_491946] using wordTrace_append hprefix tailTrace_491946
  have hstable : (prefixWord ++ tailWord_491946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491946).length < 2 ^ (prefixWord ++ tailWord_491946).sum := by decide
  have hdescent : baseEnd_491946 < baseStart_491946 := by decide
  rcases family_descends (prefixWord ++ tailWord_491946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492028 : List Nat := [2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_492028 : Nat := 118140960795 + 492028 * 2 ^ 59
def prefixEnd_492028 : Nat := 4983230072969 + 3 ^ 40 * 492028 * 2
def baseEnd_492028 : Nat := 149716657464003657414643

theorem tailTrace_492028 : CollatzResearch.WordTrace tailWord_492028 prefixEnd_492028 149716657464003657414643 := by
  unfold tailWord_492028
  simp only [CollatzResearch.WordTrace]
  refine ⟨8972867730737031268702369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11963823640982708358269825 8972867730737031268702369)
  ·
    refine ⟨6729650798052773451526777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8972867730737031268702369 6729650798052773451526777)
    ·
      refine ⟨5047238098539580088645083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6729650798052773451526777 5047238098539580088645083)
      ·
        refine ⟨7570857147809370132967625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5047238098539580088645083 7570857147809370132967625)
        ·
          refine ⟨5678142860857027599725719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7570857147809370132967625 5678142860857027599725719)
          ·
            refine ⟨8517214291285541399588579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5678142860857027599725719 8517214291285541399588579)
            ·
              refine ⟨12775821436928312099382869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8517214291285541399588579 12775821436928312099382869)
              ·
                refine ⟨149716657464003657414643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12775821436928312099382869 149716657464003657414643)
                ·
                  rfl

theorem cell19_492028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_492028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492028 prefixEnd_492028 := by exact prefixLift 492028
  have htrace : WordTrace (prefixWord ++ tailWord_492028) baseStart_492028 baseEnd_492028 := by
    simpa [prefixWord, tailWord_492028, baseEnd_492028] using wordTrace_append hprefix tailTrace_492028
  have hstable : (prefixWord ++ tailWord_492028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492028).length < 2 ^ (prefixWord ++ tailWord_492028).sum := by decide
  have hdescent : baseEnd_492028 < baseStart_492028 := by decide
  rcases family_descends (prefixWord ++ tailWord_492028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492043 : List Nat := [1, 1, 1, 1, 7, 3, 2, 3]
def baseStart_492043 : Nat := 118140960795 + 492043 * 2 ^ 59
def prefixEnd_492043 : Nat := 4983230072969 + 3 ^ 40 * 492043 * 2
def baseEnd_492043 : Nat := 149721221736488067081269

theorem tailTrace_492043 : CollatzResearch.WordTrace tailWord_492043 prefixEnd_492043 149721221736488067081269 := by
  unfold tailWord_492043
  simp only [CollatzResearch.WordTrace]
  refine ⟨17946282556419720099200783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11964188370946480066133855 17946282556419720099200783)
  ·
    refine ⟨26919423834629580148801175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17946282556419720099200783 26919423834629580148801175)
    ·
      refine ⟨40379135751944370223201763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26919423834629580148801175 40379135751944370223201763)
      ·
        refine ⟨60568703627916555334802645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40379135751944370223201763 60568703627916555334802645)
        ·
          refine ⟨1419578991279294265659437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 60568703627916555334802645 1419578991279294265659437)
          ·
            refine ⟨532342121729735349622289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1419578991279294265659437 532342121729735349622289)
            ·
              refine ⟨399256591297301512216717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532342121729735349622289 399256591297301512216717)
              ·
                refine ⟨149721221736488067081269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399256591297301512216717 149721221736488067081269)
                ·
                  rfl

theorem cell19_492043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 3].length) (baseStart_492043 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492043 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492043 prefixEnd_492043 := by exact prefixLift 492043
  have htrace : WordTrace (prefixWord ++ tailWord_492043) baseStart_492043 baseEnd_492043 := by
    simpa [prefixWord, tailWord_492043, baseEnd_492043] using wordTrace_append hprefix tailTrace_492043
  have hstable : (prefixWord ++ tailWord_492043).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492043).length < 2 ^ (prefixWord ++ tailWord_492043).sum := by decide
  have hdescent : baseEnd_492043 < baseStart_492043 := by decide
  rcases family_descends (prefixWord ++ tailWord_492043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492077 : List Nat := [1, 5, 4, 1, 1, 1, 2, 4]
def baseStart_492077 : Nat := 118140960795 + 492077 * 2 ^ 59
def prefixEnd_492077 : Nat := 4983230072969 + 3 ^ 40 * 492077 * 2
def baseEnd_492077 : Nat := 149731567420786062325621

theorem tailTrace_492077 : CollatzResearch.WordTrace tailWord_492077 prefixEnd_492077 149731567420786062325621 := by
  unfold tailWord_492077
  simp only [CollatzResearch.WordTrace]
  refine ⟨17947522638296543905938485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11965015092197695937292323 17947522638296543905938485)
  ·
    refine ⟨1682580247340300991181733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17947522638296543905938485 1682580247340300991181733)
    ·
      refine ⟨315483796376306435846575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1682580247340300991181733 315483796376306435846575)
      ·
        refine ⟨473225694564459653769863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315483796376306435846575 473225694564459653769863)
        ·
          refine ⟨709838541846689480654795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473225694564459653769863 709838541846689480654795)
          ·
            refine ⟨1064757812770034220982193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709838541846689480654795 1064757812770034220982193)
            ·
              refine ⟨798568359577525665736645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064757812770034220982193 798568359577525665736645)
              ·
                refine ⟨149731567420786062325621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 798568359577525665736645 149731567420786062325621)
                ·
                  rfl

theorem cell19_492077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 4].length) (baseStart_492077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492077 prefixEnd_492077 := by exact prefixLift 492077
  have htrace : WordTrace (prefixWord ++ tailWord_492077) baseStart_492077 baseEnd_492077 := by
    simpa [prefixWord, tailWord_492077, baseEnd_492077] using wordTrace_append hprefix tailTrace_492077
  have hstable : (prefixWord ++ tailWord_492077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492077).length < 2 ^ (prefixWord ++ tailWord_492077).sum := by decide
  have hdescent : baseEnd_492077 < baseStart_492077 := by decide
  rcases family_descends (prefixWord ++ tailWord_492077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492136 : List Nat := [2, 1, 4, 3, 3, 1, 1, 4]
def baseStart_492136 : Nat := 118140960795 + 492136 * 2 ^ 59
def prefixEnd_492136 : Nat := 4983230072969 + 3 ^ 40 * 492136 * 2
def baseEnd_492136 : Nat := 149749520225891407014349

theorem tailTrace_492136 : CollatzResearch.WordTrace tailWord_492136 prefixEnd_492136 149749520225891407014349 := by
  unfold tailWord_492136
  simp only [CollatzResearch.WordTrace]
  refine ⟨8974837272541398491168131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11966449696721864654890841 8974837272541398491168131)
  ·
    refine ⟨13462255908812097736752197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8974837272541398491168131 13462255908812097736752197)
    ·
      refine ⟨2524172982902268325641037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13462255908812097736752197 2524172982902268325641037)
      ·
        refine ⟨946564868588350622115389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2524172982902268325641037 946564868588350622115389)
        ·
          refine ⟨354961825720631483293271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 946564868588350622115389 354961825720631483293271)
          ·
            refine ⟨532442738580947224939907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354961825720631483293271 532442738580947224939907)
            ·
              refine ⟨798664107871420837409861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532442738580947224939907 798664107871420837409861)
              ·
                refine ⟨149749520225891407014349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 798664107871420837409861 149749520225891407014349)
                ·
                  rfl

theorem cell19_492136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_492136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492136 prefixEnd_492136 := by exact prefixLift 492136
  have htrace : WordTrace (prefixWord ++ tailWord_492136) baseStart_492136 baseEnd_492136 := by
    simpa [prefixWord, tailWord_492136, baseEnd_492136] using wordTrace_append hprefix tailTrace_492136
  have hstable : (prefixWord ++ tailWord_492136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492136).length < 2 ^ (prefixWord ++ tailWord_492136).sum := by decide
  have hdescent : baseEnd_492136 < baseStart_492136 := by decide
  rcases family_descends (prefixWord ++ tailWord_492136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492157 : List Nat := [1, 4, 1, 1, 5, 1, 3, 3]
def baseStart_492157 : Nat := 118140960795 + 492157 * 2 ^ 59
def prefixEnd_492157 : Nat := 4983230072969 + 3 ^ 40 * 492157 * 2
def baseEnd_492157 : Nat := 149755910207369580547625

theorem tailTrace_492157 : CollatzResearch.WordTrace tailWord_492157 prefixEnd_492157 149755910207369580547625 := by
  unfold tailWord_492157
  simp only [CollatzResearch.WordTrace]
  refine ⟨17950440478006717568850725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11966960318671145045900483 17950440478006717568850725)
  ·
    refine ⟨3365707589626259544159511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17950440478006717568850725 3365707589626259544159511)
    ·
      refine ⟨5048561384439389316239267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3365707589626259544159511 5048561384439389316239267)
      ·
        refine ⟨7572842076659083974358901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5048561384439389316239267 7572842076659083974358901)
        ·
          refine ⟨709953944686789122596147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7572842076659083974358901 709953944686789122596147)
          ·
            refine ⟨1064930917030183683894221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709953944686789122596147 1064930917030183683894221)
            ·
              refine ⟨399349093886318881460333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1064930917030183683894221 399349093886318881460333)
              ·
                refine ⟨149755910207369580547625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399349093886318881460333 149755910207369580547625)
                ·
                  rfl

theorem cell19_492157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 3].length) (baseStart_492157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492157 prefixEnd_492157 := by exact prefixLift 492157
  have htrace : WordTrace (prefixWord ++ tailWord_492157) baseStart_492157 baseEnd_492157 := by
    simpa [prefixWord, tailWord_492157, baseEnd_492157] using wordTrace_append hprefix tailTrace_492157
  have hstable : (prefixWord ++ tailWord_492157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492157).length < 2 ^ (prefixWord ++ tailWord_492157).sum := by decide
  have hdescent : baseEnd_492157 < baseStart_492157 := by decide
  rcases family_descends (prefixWord ++ tailWord_492157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492178 : List Nat := [3, 2, 3, 1, 2, 2, 6]
def baseStart_492178 : Nat := 118140960795 + 492178 * 2 ^ 59
def prefixEnd_492178 : Nat := 4983230072969 + 3 ^ 40 * 492178 * 2
def baseEnd_492178 : Nat := 49920766729615918026967

theorem tailTrace_492178 : CollatzResearch.WordTrace tailWord_492178 prefixEnd_492178 49920766729615918026967 := by
  unfold tailWord_492178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487801602732659538841297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11967470940620425436910125 4487801602732659538841297)
  ·
    refine ⟨3365851202049494654130973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4487801602732659538841297 3365851202049494654130973)
    ·
      refine ⟨1262194200768560495299115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3365851202049494654130973 1262194200768560495299115)
      ·
        refine ⟨1893291301152840742948673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262194200768560495299115 1893291301152840742948673)
        ·
          refine ⟨1419968475864630557211505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1893291301152840742948673 1419968475864630557211505)
          ·
            refine ⟨1064976356898472917908629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1419968475864630557211505 1064976356898472917908629)
            ·
              refine ⟨49920766729615918026967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1064976356898472917908629 49920766729615918026967)
              ·
                rfl

theorem cell19_492178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_492178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492178 prefixEnd_492178 := by exact prefixLift 492178
  have htrace : WordTrace (prefixWord ++ tailWord_492178) baseStart_492178 baseEnd_492178 := by
    simpa [prefixWord, tailWord_492178, baseEnd_492178] using wordTrace_append hprefix tailTrace_492178
  have hstable : (prefixWord ++ tailWord_492178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492178).length < 2 ^ (prefixWord ++ tailWord_492178).sum := by decide
  have hdescent : baseEnd_492178 < baseStart_492178 := by decide
  rcases family_descends (prefixWord ++ tailWord_492178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492218 : List Nat := [3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_492218 : Nat := 118140960795 + 492218 * 2 ^ 59
def prefixEnd_492218 : Nat := 4983230072969 + 3 ^ 40 * 492218 * 2
def baseEnd_492218 : Nat := 149774471582139513191903

theorem tailTrace_492218 : CollatzResearch.WordTrace tailWord_492218 prefixEnd_492218 149774471582139513191903 := by
  unfold tailWord_492218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488166332696431246705327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11968443553857149991214205 4488166332696431246705327)
  ·
    refine ⟨6732249499044646870057991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4488166332696431246705327 6732249499044646870057991)
    ·
      refine ⟨10098374248566970305086987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6732249499044646870057991 10098374248566970305086987)
      ·
        refine ⟨15147561372850455457630481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10098374248566970305086987 15147561372850455457630481)
        ·
          refine ⟨11360671029637841593222861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15147561372850455457630481 11360671029637841593222861)
          ·
            refine ⟨4260251636114190597458573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11360671029637841593222861 4260251636114190597458573)
            ·
              refine ⟨1597594363542821474046965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4260251636114190597458573 1597594363542821474046965)
              ·
                refine ⟨149774471582139513191903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1597594363542821474046965 149774471582139513191903)
                ·
                  rfl

theorem cell19_492218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_492218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492218 prefixEnd_492218 := by exact prefixLift 492218
  have htrace : WordTrace (prefixWord ++ tailWord_492218) baseStart_492218 baseEnd_492218 := by
    simpa [prefixWord, tailWord_492218, baseEnd_492218] using wordTrace_append hprefix tailTrace_492218
  have hstable : (prefixWord ++ tailWord_492218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492218).length < 2 ^ (prefixWord ++ tailWord_492218).sum := by decide
  have hdescent : baseEnd_492218 < baseStart_492218 := by decide
  rcases family_descends (prefixWord ++ tailWord_492218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492252 : List Nat := [2, 2, 5, 1, 1, 2, 2, 4]
def baseStart_492252 : Nat := 118140960795 + 492252 * 2 ^ 59
def prefixEnd_492252 : Nat := 4983230072969 + 3 ^ 40 * 492252 * 2
def baseEnd_492252 : Nat := 149784817266437508436255

theorem tailTrace_492252 : CollatzResearch.WordTrace tailWord_492252 prefixEnd_492252 149784817266437508436255 := by
  unfold tailWord_492252
  simp only [CollatzResearch.WordTrace]
  refine ⟨8976952706331274396779505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11969270275108365862372673 8976952706331274396779505)
  ·
    refine ⟨6732714529748455797584629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8976952706331274396779505 6732714529748455797584629)
    ·
      refine ⟨631191987163917731023559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6732714529748455797584629 631191987163917731023559)
      ·
        refine ⟨946787980745876596535339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631191987163917731023559 946787980745876596535339)
        ·
          refine ⟨1420181971118814894803009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946787980745876596535339 1420181971118814894803009)
          ·
            refine ⟨1065136478339111171102257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1420181971118814894803009 1065136478339111171102257)
            ·
              refine ⟨798852358754333378326693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065136478339111171102257 798852358754333378326693)
              ·
                refine ⟨149784817266437508436255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 798852358754333378326693 149784817266437508436255)
                ·
                  rfl

theorem cell19_492252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_492252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492252 prefixEnd_492252 := by exact prefixLift 492252
  have htrace : WordTrace (prefixWord ++ tailWord_492252) baseStart_492252 baseEnd_492252 := by
    simpa [prefixWord, tailWord_492252, baseEnd_492252] using wordTrace_append hprefix tailTrace_492252
  have hstable : (prefixWord ++ tailWord_492252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492252).length < 2 ^ (prefixWord ++ tailWord_492252).sum := by decide
  have hdescent : baseEnd_492252 < baseStart_492252 := by decide
  rcases family_descends (prefixWord ++ tailWord_492252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492349 : List Nat := [1, 4, 1, 4, 2, 1, 6]
def baseStart_492349 : Nat := 118140960795 + 492349 * 2 ^ 59
def prefixEnd_492349 : Nat := 4983230072969 + 3 ^ 40 * 492349 * 2
def baseEnd_492349 : Nat := 49938110965056674760145

theorem tailTrace_492349 : CollatzResearch.WordTrace tailWord_492349 prefixEnd_492349 49938110965056674760145 := by
  unfold tailWord_492349
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957443293311134359840101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11971628862207422906560067 17957443293311134359840101)
  ·
    refine ⟨3367020617495837692470019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17957443293311134359840101 3367020617495837692470019)
    ·
      refine ⟨5050530926243756538705029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3367020617495837692470019 5050530926243756538705029)
      ·
        refine ⟨946974548670704351007193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5050530926243756538705029 946974548670704351007193)
        ·
          refine ⟨710230911503028263255395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946974548670704351007193 710230911503028263255395)
          ·
            refine ⟨1065346367254542394883093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710230911503028263255395 1065346367254542394883093)
            ·
              refine ⟨49938110965056674760145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1065346367254542394883093 49938110965056674760145)
              ·
                rfl

theorem cell19_492349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_492349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492349 prefixEnd_492349 := by exact prefixLift 492349
  have htrace : WordTrace (prefixWord ++ tailWord_492349) baseStart_492349 baseEnd_492349 := by
    simpa [prefixWord, tailWord_492349, baseEnd_492349] using wordTrace_append hprefix tailTrace_492349
  have hstable : (prefixWord ++ tailWord_492349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492349).length < 2 ^ (prefixWord ++ tailWord_492349).sum := by decide
  have hdescent : baseEnd_492349 < baseStart_492349 := by decide
  rcases family_descends (prefixWord ++ tailWord_492349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492351 : List Nat := [1, 1, 2, 2, 5, 2, 6]
def baseStart_492351 : Nat := 118140960795 + 492351 * 2 ^ 59
def prefixEnd_492351 : Nat := 4983230072969 + 3 ^ 40 * 492351 * 2
def baseEnd_492351 : Nat := 49938313821611537411995

theorem tailTrace_492351 : CollatzResearch.WordTrace tailWord_492351 prefixEnd_492351 49938313821611537411995 := by
  unfold tailWord_492351
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957516239303888701412907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11971677492869259134275271 17957516239303888701412907)
  ·
    refine ⟨26936274358955833052119361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17957516239303888701412907 26936274358955833052119361)
    ·
      refine ⟨20202205769216874789089521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26936274358955833052119361 20202205769216874789089521)
      ·
        refine ⟨15151654326912656091817141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20202205769216874789089521 15151654326912656091817141)
        ·
          refine ⟨1420467593148061508607857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15151654326912656091817141 1420467593148061508607857)
          ·
            refine ⟨1065350694861046131455893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1420467593148061508607857 1065350694861046131455893)
            ·
              refine ⟨49938313821611537411995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1065350694861046131455893 49938313821611537411995)
              ·
                rfl

theorem cell19_492351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_492351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492351 prefixEnd_492351 := by exact prefixLift 492351
  have htrace : WordTrace (prefixWord ++ tailWord_492351) baseStart_492351 baseEnd_492351 := by
    simpa [prefixWord, tailWord_492351, baseEnd_492351] using wordTrace_append hprefix tailTrace_492351
  have hstable : (prefixWord ++ tailWord_492351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492351).length < 2 ^ (prefixWord ++ tailWord_492351).sum := by decide
  have hdescent : baseEnd_492351 < baseStart_492351 := by decide
  rcases family_descends (prefixWord ++ tailWord_492351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492370 : List Nat := [3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_492370 : Nat := 118140960795 + 492370 * 2 ^ 59
def prefixEnd_492370 : Nat := 4983230072969 + 3 ^ 40 * 492370 * 2
def baseEnd_492370 : Nat := 149820722876648197813711

theorem tailTrace_492370 : CollatzResearch.WordTrace tailWord_492370 prefixEnd_492370 149820722876648197813711 := by
  unfold tailWord_492370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4489552306558763736588641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11972139484156703297569709 4489552306558763736588641)
  ·
    refine ⟨3367164229919072802441481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4489552306558763736588641 3367164229919072802441481)
    ·
      refine ⟨2525373172439304601831111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3367164229919072802441481 2525373172439304601831111)
      ·
        refine ⟨3788059758658956902746667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525373172439304601831111 3788059758658956902746667)
        ·
          refine ⟨5682089637988435354120001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3788059758658956902746667 5682089637988435354120001)
          ·
            refine ⟨4261567228491326515590001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5682089637988435354120001 4261567228491326515590001)
            ·
              refine ⟨3196175421368494886692501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261567228491326515590001 3196175421368494886692501)
              ·
                refine ⟨149820722876648197813711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3196175421368494886692501 149820722876648197813711)
                ·
                  rfl

theorem cell19_492370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_492370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492370 prefixEnd_492370 := by exact prefixLift 492370
  have htrace : WordTrace (prefixWord ++ tailWord_492370) baseStart_492370 baseEnd_492370 := by
    simpa [prefixWord, tailWord_492370, baseEnd_492370] using wordTrace_append hprefix tailTrace_492370
  have hstable : (prefixWord ++ tailWord_492370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492370).length < 2 ^ (prefixWord ++ tailWord_492370).sum := by decide
  have hdescent : baseEnd_492370 < baseStart_492370 := by decide
  rcases family_descends (prefixWord ++ tailWord_492370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492387 : List Nat := [1, 1, 1, 5, 3, 1, 4, 3]
def baseStart_492387 : Nat := 118140960795 + 492387 * 2 ^ 59
def prefixEnd_492387 : Nat := 4983230072969 + 3 ^ 40 * 492387 * 2
def baseEnd_492387 : Nat := 149825895718797195435887

theorem tailTrace_492387 : CollatzResearch.WordTrace tailWord_492387 prefixEnd_492387 149825895718797195435887 := by
  unfold tailWord_492387
  simp only [CollatzResearch.WordTrace]
  refine ⟨17958829267173466849723415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11972552844782311233148943 17958829267173466849723415)
  ·
    refine ⟨26938243900760200274585123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17958829267173466849723415 26938243900760200274585123)
    ·
      refine ⟨40407365851140300411877685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26938243900760200274585123 40407365851140300411877685)
      ·
        refine ⟨3788190548544403163613533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40407365851140300411877685 3788190548544403163613533)
        ·
          refine ⟨1420571455704151186355075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3788190548544403163613533 1420571455704151186355075)
          ·
            refine ⟨2130857183556226779532613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420571455704151186355075 2130857183556226779532613)
            ·
              refine ⟨399535721916792521162365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2130857183556226779532613 399535721916792521162365)
              ·
                refine ⟨149825895718797195435887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399535721916792521162365 149825895718797195435887)
                ·
                  rfl

theorem cell19_492387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 3].length) (baseStart_492387 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492387 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492387 prefixEnd_492387 := by exact prefixLift 492387
  have htrace : WordTrace (prefixWord ++ tailWord_492387) baseStart_492387 baseEnd_492387 := by
    simpa [prefixWord, tailWord_492387, baseEnd_492387] using wordTrace_append hprefix tailTrace_492387
  have hstable : (prefixWord ++ tailWord_492387).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492387).length < 2 ^ (prefixWord ++ tailWord_492387).sum := by decide
  have hdescent : baseEnd_492387 < baseStart_492387 := by decide
  rcases family_descends (prefixWord ++ tailWord_492387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492406 : List Nat := [5, 1, 1, 3, 1, 1, 7]
def baseStart_492406 : Nat := 118140960795 + 492406 * 2 ^ 59
def prefixEnd_492406 : Nat := 4983230072969 + 3 ^ 40 * 492406 * 2
def baseEnd_492406 : Nat := 49943892376870260337871

theorem tailTrace_492406 : CollatzResearch.WordTrace tailWord_492406 prefixEnd_492406 49943892376870260337871 := by
  unfold tailWord_492406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1122470140881539568416567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11973014836069755396443381 1122470140881539568416567)
  ·
    refine ⟨1683705211322309352624851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1122470140881539568416567 1683705211322309352624851)
    ·
      refine ⟨2525557816983464028937277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1683705211322309352624851 2525557816983464028937277)
      ·
        refine ⟨947084181368799010851479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2525557816983464028937277 947084181368799010851479)
        ·
          refine ⟨1420626272053198516277219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947084181368799010851479 1420626272053198516277219)
          ·
            refine ⟨2130939408079797774415829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420626272053198516277219 2130939408079797774415829)
            ·
              refine ⟨49943892376870260337871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2130939408079797774415829 49943892376870260337871)
              ·
                rfl

theorem cell19_492406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_492406 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492406 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492406 prefixEnd_492406 := by exact prefixLift 492406
  have htrace : WordTrace (prefixWord ++ tailWord_492406) baseStart_492406 baseEnd_492406 := by
    simpa [prefixWord, tailWord_492406, baseEnd_492406] using wordTrace_append hprefix tailTrace_492406
  have hstable : (prefixWord ++ tailWord_492406).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492406).length < 2 ^ (prefixWord ++ tailWord_492406).sum := by decide
  have hdescent : baseEnd_492406 < baseStart_492406 := by decide
  rcases family_descends (prefixWord ++ tailWord_492406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492461 : List Nat := [1, 5, 2, 3, 2, 6]
def baseStart_492461 : Nat := 118140960795 + 492461 * 2 ^ 59
def prefixEnd_492461 : Nat := 4983230072969 + 3 ^ 40 * 492461 * 2
def baseEnd_492461 : Nat := 16649823644042994421249

theorem tailTrace_492461 : CollatzResearch.WordTrace tailWord_492461 prefixEnd_492461 16649823644042994421249 := by
  unfold tailWord_492461
  simp only [CollatzResearch.WordTrace]
  refine ⟨17961528268905377487917237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11974352179270251658611491 17961528268905377487917237)
  ·
    refine ⟨1683893275209879139492241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17961528268905377487917237 1683893275209879139492241)
    ·
      refine ⟨1262919956407409354619181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1683893275209879139492241 1262919956407409354619181)
      ·
        refine ⟨473594983652778507982193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1262919956407409354619181 473594983652778507982193)
        ·
          refine ⟨355196237739583880986645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473594983652778507982193 355196237739583880986645)
          ·
            refine ⟨16649823644042994421249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 355196237739583880986645 16649823644042994421249)
            ·
              rfl

theorem cell19_492461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 6].length) (baseStart_492461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492461 prefixEnd_492461 := by exact prefixLift 492461
  have htrace : WordTrace (prefixWord ++ tailWord_492461) baseStart_492461 baseEnd_492461 := by
    simpa [prefixWord, tailWord_492461, baseEnd_492461] using wordTrace_append hprefix tailTrace_492461
  have hstable : (prefixWord ++ tailWord_492461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492461).length < 2 ^ (prefixWord ++ tailWord_492461).sum := by decide
  have hdescent : baseEnd_492461 < baseStart_492461 := by decide
  rcases family_descends (prefixWord ++ tailWord_492461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492465 : List Nat := [1, 2, 2, 4, 3, 7]
def baseStart_492465 : Nat := 118140960795 + 492465 * 2 ^ 59
def prefixEnd_492465 : Nat := 4983230072969 + 3 ^ 40 * 492465 * 2
def baseEnd_492465 : Nat := 16649958881746236189149

theorem tailTrace_492465 : CollatzResearch.WordTrace tailWord_492465 prefixEnd_492465 16649958881746236189149 := by
  unfold tailWord_492465
  simp only [CollatzResearch.WordTrace]
  refine ⟨17961674160890886171062849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11974449440593924114041899 17961674160890886171062849)
  ·
    refine ⟨13471255620668164628297137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17961674160890886171062849 13471255620668164628297137)
    ·
      refine ⟨10103441715501123471222853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13471255620668164628297137 10103441715501123471222853)
      ·
        refine ⟨1894395321656460650854285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10103441715501123471222853 1894395321656460650854285)
        ·
          refine ⟨710398245621172744070357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1894395321656460650854285 710398245621172744070357)
          ·
            refine ⟨16649958881746236189149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 710398245621172744070357 16649958881746236189149)
            ·
              rfl

theorem cell19_492465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 7].length) (baseStart_492465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492465 prefixEnd_492465 := by exact prefixLift 492465
  have htrace : WordTrace (prefixWord ++ tailWord_492465) baseStart_492465 baseEnd_492465 := by
    simpa [prefixWord, tailWord_492465, baseEnd_492465] using wordTrace_append hprefix tailTrace_492465
  have hstable : (prefixWord ++ tailWord_492465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492465).length < 2 ^ (prefixWord ++ tailWord_492465).sum := by decide
  have hdescent : baseEnd_492465 < baseStart_492465 := by decide
  rcases family_descends (prefixWord ++ tailWord_492465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492522 : List Nat := [3, 1, 3, 1, 2, 3, 6]
def baseStart_492522 : Nat := 118140960795 + 492522 * 2 ^ 59
def prefixEnd_492522 : Nat := 4983230072969 + 3 ^ 40 * 492522 * 2
def baseEnd_492522 : Nat := 49955658057052294145173

theorem tailTrace_492522 : CollatzResearch.WordTrace tailWord_492522 prefixEnd_492522 49955658057052294145173 := by
  unfold tailWord_492522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490938280421096226471955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11975835414456256603925213 4490938280421096226471955)
  ·
    refine ⟨6736407420631644339707933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4490938280421096226471955 6736407420631644339707933)
    ·
      refine ⟨2526152782736866627390475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6736407420631644339707933 2526152782736866627390475)
      ·
        refine ⟨3789229174105299941085713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2526152782736866627390475 3789229174105299941085713)
        ·
          refine ⟨2841921880578974955814285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3789229174105299941085713 2841921880578974955814285)
          ·
            refine ⟨1065720705217115608430357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2841921880578974955814285 1065720705217115608430357)
            ·
              refine ⟨49955658057052294145173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1065720705217115608430357 49955658057052294145173)
              ·
                rfl

theorem cell19_492522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_492522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492522 prefixEnd_492522 := by exact prefixLift 492522
  have htrace : WordTrace (prefixWord ++ tailWord_492522) baseStart_492522 baseEnd_492522 := by
    simpa [prefixWord, tailWord_492522, baseEnd_492522] using wordTrace_append hprefix tailTrace_492522
  have hstable : (prefixWord ++ tailWord_492522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492522).length < 2 ^ (prefixWord ++ tailWord_492522).sum := by decide
  have hdescent : baseEnd_492522 < baseStart_492522 := by decide
  rcases family_descends (prefixWord ++ tailWord_492522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492558 : List Nat := [4, 1, 1, 2, 2, 2, 4, 3]
def baseStart_492558 : Nat := 118140960795 + 492558 * 2 ^ 59
def prefixEnd_492558 : Nat := 4983230072969 + 3 ^ 40 * 492558 * 2
def baseEnd_492558 : Nat := 149877928425119465635421

theorem tailTrace_492558 : CollatzResearch.WordTrace tailWord_492558 prefixEnd_492558 149877928425119465635421 := by
  unfold tailWord_492558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245633268694245381774791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11976710766369308702798885 2245633268694245381774791)
  ·
    refine ⟨3368449903041368072662187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2245633268694245381774791 3368449903041368072662187)
    ·
      refine ⟨5052674854562052108993281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3368449903041368072662187 5052674854562052108993281)
      ·
        refine ⟨3789506140921539081744961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5052674854562052108993281 3789506140921539081744961)
        ·
          refine ⟨2842129605691154311308721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3789506140921539081744961 2842129605691154311308721)
          ·
            refine ⟨2131597204268365733481541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2842129605691154311308721 2131597204268365733481541)
            ·
              refine ⟨399674475800318575027789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2131597204268365733481541 399674475800318575027789)
              ·
                refine ⟨149877928425119465635421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399674475800318575027789 149877928425119465635421)
                ·
                  rfl

theorem cell19_492558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_492558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492558 prefixEnd_492558 := by exact prefixLift 492558
  have htrace : WordTrace (prefixWord ++ tailWord_492558) baseStart_492558 baseEnd_492558 := by
    simpa [prefixWord, tailWord_492558, baseEnd_492558] using wordTrace_append hprefix tailTrace_492558
  have hstable : (prefixWord ++ tailWord_492558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492558).length < 2 ^ (prefixWord ++ tailWord_492558).sum := by decide
  have hdescent : baseEnd_492558 < baseStart_492558 := by decide
  rcases family_descends (prefixWord ++ tailWord_492558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492579 : List Nat := [1, 1, 1, 4, 3, 4, 5]
def baseStart_492579 : Nat := 118140960795 + 492579 * 2 ^ 59
def prefixEnd_492579 : Nat := 4983230072969 + 3 ^ 40 * 492579 * 2
def baseEnd_492579 : Nat := 49961439468865879722899

theorem tailTrace_492579 : CollatzResearch.WordTrace tailWord_492579 prefixEnd_492579 49961439468865879722899 := by
  unfold tailWord_492579
  simp only [CollatzResearch.WordTrace]
  refine ⟨17965832082477883640712791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11977221388318589093808527 17965832082477883640712791)
  ·
    refine ⟨26948748123716825461069187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17965832082477883640712791 26948748123716825461069187)
    ·
      refine ⟨40423122185575238191603781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26948748123716825461069187 40423122185575238191603781)
      ·
        refine ⟨7579335409795357160925709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40423122185575238191603781 7579335409795357160925709)
        ·
          refine ⟨2842250778673258935347141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7579335409795357160925709 2842250778673258935347141)
          ·
            refine ⟨532922021001236050377589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2842250778673258935347141 532922021001236050377589)
            ·
              refine ⟨49961439468865879722899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 532922021001236050377589 49961439468865879722899)
              ·
                rfl

theorem cell19_492579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_492579 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492579 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492579 prefixEnd_492579 := by exact prefixLift 492579
  have htrace : WordTrace (prefixWord ++ tailWord_492579) baseStart_492579 baseEnd_492579 := by
    simpa [prefixWord, tailWord_492579, baseEnd_492579] using wordTrace_append hprefix tailTrace_492579
  have hstable : (prefixWord ++ tailWord_492579).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492579).length < 2 ^ (prefixWord ++ tailWord_492579).sum := by decide
  have hdescent : baseEnd_492579 < baseStart_492579 := by decide
  rcases family_descends (prefixWord ++ tailWord_492579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492596 : List Nat := [2, 5, 1, 2, 1, 1, 1, 6]
def baseStart_492596 : Nat := 118140960795 + 492596 * 2 ^ 59
def prefixEnd_492596 : Nat := 4983230072969 + 3 ^ 40 * 492596 * 2
def baseEnd_492596 : Nat := 149889491248746636790873

theorem tailTrace_492596 : CollatzResearch.WordTrace tailWord_492596 prefixEnd_492596 149889491248746636790873 := by
  unfold tailWord_492596
  simp only [CollatzResearch.WordTrace]
  refine ⟨8983226061708147772040821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11977634748944197029387761 8983226061708147772040821)
  ·
    refine ⟨842177443285138853628827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8983226061708147772040821 842177443285138853628827)
    ·
      refine ⟨1263266164927708280443241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842177443285138853628827 1263266164927708280443241)
      ·
        refine ⟨947449623695781210332431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1263266164927708280443241 947449623695781210332431)
        ·
          refine ⟨1421174435543671815498647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947449623695781210332431 1421174435543671815498647)
          ·
            refine ⟨2131761653315507723247971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421174435543671815498647 2131761653315507723247971)
            ·
              refine ⟨3197642479973261584871957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131761653315507723247971 3197642479973261584871957)
              ·
                refine ⟨149889491248746636790873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3197642479973261584871957 149889491248746636790873)
                ·
                  rfl

theorem cell19_492596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_492596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492596 prefixEnd_492596 := by exact prefixLift 492596
  have htrace : WordTrace (prefixWord ++ tailWord_492596) baseStart_492596 baseEnd_492596 := by
    simpa [prefixWord, tailWord_492596, baseEnd_492596] using wordTrace_append hprefix tailTrace_492596
  have hstable : (prefixWord ++ tailWord_492596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492596).length < 2 ^ (prefixWord ++ tailWord_492596).sum := by decide
  have hdescent : baseEnd_492596 < baseStart_492596 := by decide
  rcases family_descends (prefixWord ++ tailWord_492596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492653 : List Nat := [1, 5, 1, 1, 2, 4, 1, 4]
def baseStart_492653 : Nat := 118140960795 + 492653 * 2 ^ 59
def prefixEnd_492653 : Nat := 4983230072969 + 3 ^ 40 * 492653 * 2
def baseEnd_492653 : Nat := 149906835484187393524051

theorem tailTrace_492653 : CollatzResearch.WordTrace tailWord_492653 prefixEnd_492653 149906835484187393524051 := by
  unfold tailWord_492653
  simp only [CollatzResearch.WordTrace]
  refine ⟨17968531084209794278906613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11979020722806529519271075 17968531084209794278906613)
  ·
    refine ⟨1684549789144668213647495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17968531084209794278906613 1684549789144668213647495)
    ·
      refine ⟨2526824683717002320471243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1684549789144668213647495 2526824683717002320471243)
      ·
        refine ⟨3790237025575503480706865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2526824683717002320471243 3790237025575503480706865)
        ·
          refine ⟨2842677769181627610530149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3790237025575503480706865 2842677769181627610530149)
          ·
            refine ⟨533002081721555176974403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2842677769181627610530149 533002081721555176974403)
            ·
              refine ⟨799503122582332765461605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533002081721555176974403 799503122582332765461605)
              ·
                refine ⟨149906835484187393524051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 799503122582332765461605 149906835484187393524051)
                ·
                  rfl

theorem cell19_492653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_492653 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492653 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492653 prefixEnd_492653 := by exact prefixLift 492653
  have htrace : WordTrace (prefixWord ++ tailWord_492653) baseStart_492653 baseEnd_492653 := by
    simpa [prefixWord, tailWord_492653, baseEnd_492653] using wordTrace_append hprefix tailTrace_492653
  have hstable : (prefixWord ++ tailWord_492653).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492653).length < 2 ^ (prefixWord ++ tailWord_492653).sum := by decide
  have hdescent : baseEnd_492653 < baseStart_492653 := by decide
  rcases family_descends (prefixWord ++ tailWord_492653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492657 : List Nat := [1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_492657 : Nat := 118140960795 + 492657 * 2 ^ 59
def prefixEnd_492657 : Nat := 4983230072969 + 3 ^ 40 * 492657 * 2
def baseEnd_492657 : Nat := 149908052623516569435151

theorem tailTrace_492657 : CollatzResearch.WordTrace tailWord_492657 prefixEnd_492657 149908052623516569435151 := by
  unfold tailWord_492657
  simp only [CollatzResearch.WordTrace]
  refine ⟨17968676976195302962052225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11979117984130201974701483 17968676976195302962052225)
  ·
    refine ⟨13476507732146477221539169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17968676976195302962052225 13476507732146477221539169)
    ·
      refine ⟨10107380799109857916154377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13476507732146477221539169 10107380799109857916154377)
      ·
        refine ⟨7580535599332393437115783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10107380799109857916154377 7580535599332393437115783)
        ·
          refine ⟨11370803398998590155673675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7580535599332393437115783 11370803398998590155673675)
          ·
            refine ⟨17056205098497885233510513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11370803398998590155673675 17056205098497885233510513)
            ·
              refine ⟨12792153823873413925132885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17056205098497885233510513 12792153823873413925132885)
              ·
                refine ⟨149908052623516569435151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12792153823873413925132885 149908052623516569435151)
                ·
                  rfl

theorem cell19_492657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_492657 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492657 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492657 prefixEnd_492657 := by exact prefixLift 492657
  have htrace : WordTrace (prefixWord ++ tailWord_492657) baseStart_492657 baseEnd_492657 := by
    simpa [prefixWord, tailWord_492657, baseEnd_492657] using wordTrace_append hprefix tailTrace_492657
  have hstable : (prefixWord ++ tailWord_492657).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492657).length < 2 ^ (prefixWord ++ tailWord_492657).sum := by decide
  have hdescent : baseEnd_492657 < baseStart_492657 := by decide
  rcases family_descends (prefixWord ++ tailWord_492657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492729 : List Nat := [1, 2, 1, 4, 1, 5, 2, 3]
def baseStart_492729 : Nat := 118140960795 + 492729 * 2 ^ 59
def prefixEnd_492729 : Nat := 4983230072969 + 3 ^ 40 * 492729 * 2
def baseEnd_492729 : Nat := 149929961131441735834955

theorem tailTrace_492729 : CollatzResearch.WordTrace tailWord_492729 prefixEnd_492729 149929961131441735834955 := by
  unfold tailWord_492729
  simp only [CollatzResearch.WordTrace]
  refine ⟨17971303031934459258673241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11980868687956306172448827 17971303031934459258673241)
  ·
    refine ⟨13478477273950844444004931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17971303031934459258673241 13478477273950844444004931)
    ·
      refine ⟨20217715910926266666007397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13478477273950844444004931 20217715910926266666007397)
      ·
        refine ⟨3790821733298674999876387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20217715910926266666007397 3790821733298674999876387)
        ·
          refine ⟨5686232599948012499814581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790821733298674999876387 5686232599948012499814581)
          ·
            refine ⟨533084306245126171857617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5686232599948012499814581 533084306245126171857617)
            ·
              refine ⟨399813229683844628893213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533084306245126171857617 399813229683844628893213)
              ·
                refine ⟨149929961131441735834955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399813229683844628893213 149929961131441735834955)
                ·
                  rfl

theorem cell19_492729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 3].length) (baseStart_492729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492729 prefixEnd_492729 := by exact prefixLift 492729
  have htrace : WordTrace (prefixWord ++ tailWord_492729) baseStart_492729 baseEnd_492729 := by
    simpa [prefixWord, tailWord_492729, baseEnd_492729] using wordTrace_append hprefix tailTrace_492729
  have hstable : (prefixWord ++ tailWord_492729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492729).length < 2 ^ (prefixWord ++ tailWord_492729).sum := by decide
  have hdescent : baseEnd_492729 < baseStart_492729 := by decide
  rcases family_descends (prefixWord ++ tailWord_492729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492742 : List Nat := [6, 1, 2, 2, 2, 1, 5]
def baseStart_492742 : Nat := 118140960795 + 492742 * 2 ^ 59
def prefixEnd_492742 : Nat := 4983230072969 + 3 ^ 40 * 492742 * 2
def baseEnd_492742 : Nat := 49977972278087185848677

theorem tailTrace_492742 : CollatzResearch.WordTrace tailWord_492742 prefixEnd_492742 49977972278087185848677 := by
  unfold tailWord_492742
  simp only [CollatzResearch.WordTrace]
  refine ⟨561618036902730077465515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11981184787258241652597653 561618036902730077465515)
  ·
    refine ⟨842427055354095116198273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 561618036902730077465515 842427055354095116198273)
    ·
      refine ⟨631820291515571337148705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 842427055354095116198273 631820291515571337148705)
      ·
        refine ⟨473865218636678502861529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631820291515571337148705 473865218636678502861529)
        ·
          refine ⟨355398913977508877146147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473865218636678502861529 355398913977508877146147)
          ·
            refine ⟨533098370966263315719221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355398913977508877146147 533098370966263315719221)
            ·
              refine ⟨49977972278087185848677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 533098370966263315719221 49977972278087185848677)
              ·
                rfl

theorem cell19_492742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 5].length) (baseStart_492742 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492742 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492742 prefixEnd_492742 := by exact prefixLift 492742
  have htrace : WordTrace (prefixWord ++ tailWord_492742) baseStart_492742 baseEnd_492742 := by
    simpa [prefixWord, tailWord_492742, baseEnd_492742] using wordTrace_append hprefix tailTrace_492742
  have hstable : (prefixWord ++ tailWord_492742).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492742).length < 2 ^ (prefixWord ++ tailWord_492742).sum := by decide
  have hdescent : baseEnd_492742 < baseStart_492742 := by decide
  rcases family_descends (prefixWord ++ tailWord_492742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492769 : List Nat := [1, 2, 3, 1, 3, 3, 2, 4]
def baseStart_492769 : Nat := 118140960795 + 492769 * 2 ^ 59
def prefixEnd_492769 : Nat := 4983230072969 + 3 ^ 40 * 492769 * 2
def baseEnd_492769 : Nat := 149942132524733494945957

theorem tailTrace_492769 : CollatzResearch.WordTrace tailWord_492769 prefixEnd_492769 149942132524733494945957 := by
  unfold tailWord_492769
  simp only [CollatzResearch.WordTrace]
  refine ⟨17972761951789546090129361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11981841301193030726752907 17972761951789546090129361)
  ·
    refine ⟨13479571463842159567597021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17972761951789546090129361 13479571463842159567597021)
    ·
      refine ⟨5054839298940809837848883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13479571463842159567597021 5054839298940809837848883)
      ·
        refine ⟨7582258948411214756773325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5054839298940809837848883 7582258948411214756773325)
        ·
          refine ⟨2843347105654205533789997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7582258948411214756773325 2843347105654205533789997)
          ·
            refine ⟨1066255164620327075171249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2843347105654205533789997 1066255164620327075171249)
            ·
              refine ⟨799691373465245306378437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066255164620327075171249 799691373465245306378437)
              ·
                refine ⟨149942132524733494945957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 799691373465245306378437 149942132524733494945957)
                ·
                  rfl

theorem cell19_492769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_492769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492769 prefixEnd_492769 := by exact prefixLift 492769
  have htrace : WordTrace (prefixWord ++ tailWord_492769) baseStart_492769 baseEnd_492769 := by
    simpa [prefixWord, tailWord_492769, baseEnd_492769] using wordTrace_append hprefix tailTrace_492769
  have hstable : (prefixWord ++ tailWord_492769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492769).length < 2 ^ (prefixWord ++ tailWord_492769).sum := by decide
  have hdescent : baseEnd_492769 < baseStart_492769 := by decide
  rcases family_descends (prefixWord ++ tailWord_492769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492826 : List Nat := [3, 1, 1, 3, 3, 1, 3, 4]
def baseStart_492826 : Nat := 118140960795 + 492826 * 2 ^ 59
def prefixEnd_492826 : Nat := 4983230072969 + 3 ^ 40 * 492826 * 2
def baseEnd_492826 : Nat := 149959476760174251679135

theorem tailTrace_492826 : CollatzResearch.WordTrace tailWord_492826 prefixEnd_492826 149959476760174251679135 := by
  unfold tailWord_492826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4493710228145761206238583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11983227275055363216636221 4493710228145761206238583)
  ·
    refine ⟨6740565342218641809357875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4493710228145761206238583 6740565342218641809357875)
    ·
      refine ⟨10110848013327962714036813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6740565342218641809357875 10110848013327962714036813)
      ·
        refine ⟨3791568004997986017763805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10110848013327962714036813 3791568004997986017763805)
        ·
          refine ⟨1421838001874244756661427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3791568004997986017763805 1421838001874244756661427)
          ·
            refine ⟨2132757002811367134992141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421838001874244756661427 2132757002811367134992141)
            ·
              refine ⟨799783876054262675622053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2132757002811367134992141 799783876054262675622053)
              ·
                refine ⟨149959476760174251679135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 799783876054262675622053 149959476760174251679135)
                ·
                  rfl

theorem cell19_492826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_492826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492826 prefixEnd_492826 := by exact prefixLift 492826
  have htrace : WordTrace (prefixWord ++ tailWord_492826) baseStart_492826 baseEnd_492826 := by
    simpa [prefixWord, tailWord_492826, baseEnd_492826] using wordTrace_append hprefix tailTrace_492826
  have hstable : (prefixWord ++ tailWord_492826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492826).length < 2 ^ (prefixWord ++ tailWord_492826).sum := by decide
  have hdescent : baseEnd_492826 < baseStart_492826 := by decide
  rcases family_descends (prefixWord ++ tailWord_492826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492900 : List Nat := [2, 3, 1, 1, 3, 4, 2, 3]
def baseStart_492900 : Nat := 118140960795 + 492900 * 2 ^ 59
def prefixEnd_492900 : Nat := 4983230072969 + 3 ^ 40 * 492900 * 2
def baseEnd_492900 : Nat := 149981993837764006034489

theorem tailTrace_492900 : CollatzResearch.WordTrace tailWord_492900 prefixEnd_492900 149981993837764006034489 := by
  unfold tailWord_492900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8988769957157477731574077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11985026609543303642098769 8988769957157477731574077)
  ·
    refine ⟨3370788733934054149340279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8988769957157477731574077 3370788733934054149340279)
    ·
      refine ⟨5056183100901081224010419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3370788733934054149340279 5056183100901081224010419)
      ·
        refine ⟨7584274651351621836015629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5056183100901081224010419 7584274651351621836015629)
        ·
          refine ⟨2844102994256858188505861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7584274651351621836015629 2844102994256858188505861)
          ·
            refine ⟨533269311423160910344849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2844102994256858188505861 533269311423160910344849)
            ·
              refine ⟨399951983567370682758637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533269311423160910344849 399951983567370682758637)
              ·
                refine ⟨149981993837764006034489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399951983567370682758637 149981993837764006034489)
                ·
                  rfl

theorem cell19_492900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_492900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_492900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_492900 prefixEnd_492900 := by exact prefixLift 492900
  have htrace : WordTrace (prefixWord ++ tailWord_492900) baseStart_492900 baseEnd_492900 := by
    simpa [prefixWord, tailWord_492900, baseEnd_492900] using wordTrace_append hprefix tailTrace_492900
  have hstable : (prefixWord ++ tailWord_492900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492900).length < 2 ^ (prefixWord ++ tailWord_492900).sum := by decide
  have hdescent : baseEnd_492900 < baseStart_492900 := by decide
  rcases family_descends (prefixWord ++ tailWord_492900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493069 : List Nat := [1, 7, 1, 1, 2, 1, 1, 5]
def baseStart_493069 : Nat := 118140960795 + 493069 * 2 ^ 59
def prefixEnd_493069 : Nat := 4983230072969 + 3 ^ 40 * 493069 * 2
def baseEnd_493069 : Nat := 150033417974421688278473

theorem tailTrace_493069 : CollatzResearch.WordTrace tailWord_493069 prefixEnd_493069 150033417974421688278473 := by
  unfold tailWord_493069
  simp only [CollatzResearch.WordTrace]
  refine ⟨17983703850702697326050261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11989135900468464884033507 17983703850702697326050261)
  ·
    refine ⟨421493059000844468579303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17983703850702697326050261 421493059000844468579303)
    ·
      refine ⟨632239588501266702868955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421493059000844468579303 632239588501266702868955)
      ·
        refine ⟨948359382751900054303433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632239588501266702868955 948359382751900054303433)
        ·
          refine ⟨711269537063925040727575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 948359382751900054303433 711269537063925040727575)
          ·
            refine ⟨1066904305595887561091363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711269537063925040727575 1066904305595887561091363)
            ·
              refine ⟨1600356458393831341637045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066904305595887561091363 1600356458393831341637045)
              ·
                refine ⟨150033417974421688278473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1600356458393831341637045 150033417974421688278473)
                ·
                  rfl

theorem cell19_493069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 5].length) (baseStart_493069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493069 prefixEnd_493069 := by exact prefixLift 493069
  have htrace : WordTrace (prefixWord ++ tailWord_493069) baseStart_493069 baseEnd_493069 := by
    simpa [prefixWord, tailWord_493069, baseEnd_493069] using wordTrace_append hprefix tailTrace_493069
  have hstable : (prefixWord ++ tailWord_493069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493069).length < 2 ^ (prefixWord ++ tailWord_493069).sum := by decide
  have hdescent : baseEnd_493069 < baseStart_493069 := by decide
  rcases family_descends (prefixWord ++ tailWord_493069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493075 : List Nat := [1, 1, 1, 2, 1, 7, 1, 5]
def baseStart_493075 : Nat := 118140960795 + 493075 * 2 ^ 59
def prefixEnd_493075 : Nat := 4983230072969 + 3 ^ 40 * 493075 * 2
def baseEnd_493075 : Nat := 150035243683415452145123

theorem tailTrace_493075 : CollatzResearch.WordTrace tailWord_493075 prefixEnd_493075 150035243683415452145123 := by
  unfold tailWord_493075
  simp only [CollatzResearch.WordTrace]
  refine ⟨17983922688680960350768679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11989281792453973567179119 17983922688680960350768679)
  ·
    refine ⟨26975884033021440526153019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17983922688680960350768679 26975884033021440526153019)
    ·
      refine ⟨40463826049532160789229529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26975884033021440526153019 40463826049532160789229529)
      ·
        refine ⟨30347869537149120591922147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40463826049532160789229529 30347869537149120591922147)
        ·
          refine ⟨45521804305723680887883221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30347869537149120591922147 45521804305723680887883221)
          ·
            refine ⟨1066917288415398770809763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45521804305723680887883221 1066917288415398770809763)
            ·
              refine ⟨1600375932623098156214645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066917288415398770809763 1600375932623098156214645)
              ·
                refine ⟨150035243683415452145123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1600375932623098156214645 150035243683415452145123)
                ·
                  rfl

theorem cell19_493075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_493075 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493075 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493075 prefixEnd_493075 := by exact prefixLift 493075
  have htrace : WordTrace (prefixWord ++ tailWord_493075) baseStart_493075 baseEnd_493075 := by
    simpa [prefixWord, tailWord_493075, baseEnd_493075] using wordTrace_append hprefix tailTrace_493075
  have hstable : (prefixWord ++ tailWord_493075).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493075).length < 2 ^ (prefixWord ++ tailWord_493075).sum := by decide
  have hdescent : baseEnd_493075 < baseStart_493075 := by decide
  rcases family_descends (prefixWord ++ tailWord_493075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493086 : List Nat := [4, 3, 3, 1, 1, 2, 5]
def baseStart_493086 : Nat := 118140960795 + 493086 * 2 ^ 59
def prefixEnd_493086 : Nat := 4983230072969 + 3 ^ 40 * 493086 * 2
def baseEnd_493086 : Nat := 50012863605523561966883

theorem tailTrace_493086 : CollatzResearch.WordTrace tailWord_493086 prefixEnd_493086 50012863605523561966883 := by
  unfold tailWord_493086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2248040486455138653677389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11989549261094072819612741 2248040486455138653677389)
  ·
    refine ⟨843015182420676995129021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2248040486455138653677389 843015182420676995129021)
    ·
      refine ⟨316130693407753873173383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 843015182420676995129021 316130693407753873173383)
      ·
        refine ⟨474196040111630809760075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316130693407753873173383 474196040111630809760075)
        ·
          refine ⟨711294060167446214640113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474196040111630809760075 711294060167446214640113)
          ·
            refine ⟨533470545125584660980085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711294060167446214640113 533470545125584660980085)
            ·
              refine ⟨50012863605523561966883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 533470545125584660980085 50012863605523561966883)
              ·
                rfl

theorem cell19_493086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 5].length) (baseStart_493086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493086 prefixEnd_493086 := by exact prefixLift 493086
  have htrace : WordTrace (prefixWord ++ tailWord_493086) baseStart_493086 baseEnd_493086 := by
    simpa [prefixWord, tailWord_493086, baseEnd_493086] using wordTrace_append hprefix tailTrace_493086
  have hstable : (prefixWord ++ tailWord_493086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493086).length < 2 ^ (prefixWord ++ tailWord_493086).sum := by decide
  have hdescent : baseEnd_493086 < baseStart_493086 := by decide
  rcases family_descends (prefixWord ++ tailWord_493086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493113 : List Nat := [1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_493113 : Nat := 118140960795 + 493113 * 2 ^ 59
def prefixEnd_493113 : Nat := 4983230072969 + 3 ^ 40 * 493113 * 2
def baseEnd_493113 : Nat := 150046806507042623300575

theorem tailTrace_493113 : CollatzResearch.WordTrace tailWord_493113 prefixEnd_493113 150046806507042623300575 := by
  unfold tailWord_493113
  simp only [CollatzResearch.WordTrace]
  refine ⟨17985308662543292840651993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11990205775028861893767995 17985308662543292840651993)
  ·
    refine ⟨13488981496907469630488995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17985308662543292840651993 13488981496907469630488995)
    ·
      refine ⟨20233472245361204445733493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13488981496907469630488995 20233472245361204445733493)
      ·
        refine ⟨1896888023002612916787515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20233472245361204445733493 1896888023002612916787515)
        ·
          refine ⟨2845332034503919375181273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896888023002612916787515 2845332034503919375181273)
          ·
            refine ⟨2133999025877939531385955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845332034503919375181273 2133999025877939531385955)
            ·
              refine ⟨3200998538816909297078933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133999025877939531385955 3200998538816909297078933)
              ·
                refine ⟨150046806507042623300575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3200998538816909297078933 150046806507042623300575)
                ·
                  rfl

theorem cell19_493113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_493113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493113 prefixEnd_493113 := by exact prefixLift 493113
  have htrace : WordTrace (prefixWord ++ tailWord_493113) baseStart_493113 baseEnd_493113 := by
    simpa [prefixWord, tailWord_493113, baseEnd_493113] using wordTrace_append hprefix tailTrace_493113
  have hstable : (prefixWord ++ tailWord_493113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493113).length < 2 ^ (prefixWord ++ tailWord_493113).sum := by decide
  have hdescent : baseEnd_493113 < baseStart_493113 := by decide
  rcases family_descends (prefixWord ++ tailWord_493113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493132 : List Nat := [2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_493132 : Nat := 118140960795 + 493132 * 2 ^ 59
def prefixEnd_493132 : Nat := 4983230072969 + 3 ^ 40 * 493132 * 2
def baseEnd_493132 : Nat := 150052587918856208878301

theorem tailTrace_493132 : CollatzResearch.WordTrace tailWord_493132 prefixEnd_493132 150052587918856208878301 := by
  unfold tailWord_493132
  simp only [CollatzResearch.WordTrace]
  refine ⟨8993000824737229542796825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11990667766316306057062433 8993000824737229542796825)
  ·
    refine ⟨6744750618552922157097619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8993000824737229542796825 6744750618552922157097619)
    ·
      refine ⟨10117125927829383235646429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6744750618552922157097619 10117125927829383235646429)
      ·
        refine ⟨3793922222936018713367411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10117125927829383235646429 3793922222936018713367411)
        ·
          refine ⟨5690883334404028070051117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3793922222936018713367411 5690883334404028070051117)
          ·
            refine ⟨2134081250401510526269169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5690883334404028070051117 2134081250401510526269169)
            ·
              refine ⟨1600560937801132894701877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134081250401510526269169 1600560937801132894701877)
              ·
                refine ⟨150052587918856208878301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1600560937801132894701877 150052587918856208878301)
                ·
                  rfl

theorem cell19_493132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_493132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493132 prefixEnd_493132 := by exact prefixLift 493132
  have htrace : WordTrace (prefixWord ++ tailWord_493132) baseStart_493132 baseEnd_493132 := by
    simpa [prefixWord, tailWord_493132, baseEnd_493132] using wordTrace_append hprefix tailTrace_493132
  have hstable : (prefixWord ++ tailWord_493132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493132).length < 2 ^ (prefixWord ++ tailWord_493132).sum := by decide
  have hdescent : baseEnd_493132 < baseStart_493132 := by decide
  rcases family_descends (prefixWord ++ tailWord_493132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493149 : List Nat := [1, 4, 4, 2, 8]
def baseStart_493149 : Nat := 118140960795 + 493149 * 2 ^ 59
def prefixEnd_493149 : Nat := 4983230072969 + 3 ^ 40 * 493149 * 2
def baseEnd_493149 : Nat := 5557694843000192833351

theorem tailTrace_493149 : CollatzResearch.WordTrace tailWord_493149 prefixEnd_493149 5557694843000192833351 := by
  unfold tailWord_493149
  simp only [CollatzResearch.WordTrace]
  refine ⟨17986621690412870988962501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11991081126941913992641667 17986621690412870988962501)
  ·
    refine ⟨3372491566952413310430469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17986621690412870988962501 3372491566952413310430469)
    ·
      refine ⟨632342168803577495705713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3372491566952413310430469 632342168803577495705713)
      ·
        refine ⟨474256626602683121779285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632342168803577495705713 474256626602683121779285)
        ·
          refine ⟨5557694843000192833351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 474256626602683121779285 5557694843000192833351)
          ·
            rfl

theorem cell19_493149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 8].length) (baseStart_493149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493149 prefixEnd_493149 := by exact prefixLift 493149
  have htrace : WordTrace (prefixWord ++ tailWord_493149) baseStart_493149 baseEnd_493149 := by
    simpa [prefixWord, tailWord_493149, baseEnd_493149] using wordTrace_append hprefix tailTrace_493149
  have hstable : (prefixWord ++ tailWord_493149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493149).length < 2 ^ (prefixWord ++ tailWord_493149).sum := by decide
  have hdescent : baseEnd_493149 < baseStart_493149 := by decide
  rcases family_descends (prefixWord ++ tailWord_493149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493166 : List Nat := [4, 1, 2, 2, 3, 2, 1, 4]
def baseStart_493166 : Nat := 118140960795 + 493166 * 2 ^ 59
def prefixEnd_493166 : Nat := 4983230072969 + 3 ^ 40 * 493166 * 2
def baseEnd_493166 : Nat := 150062933603154204122653

theorem tailTrace_493166 : CollatzResearch.WordTrace tailWord_493166 prefixEnd_493166 150062933603154204122653 := by
  unfold tailWord_493166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2248405216418910361541419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11991494487567521928220901 2248405216418910361541419)
  ·
    refine ⟨3372607824628365542312129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2248405216418910361541419 3372607824628365542312129)
    ·
      refine ⟨2529455868471274156734097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3372607824628365542312129 2529455868471274156734097)
      ·
        refine ⟨1897091901353455617550573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2529455868471274156734097 1897091901353455617550573)
        ·
          refine ⟨711409463007545856581465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1897091901353455617550573 711409463007545856581465)
          ·
            refine ⟨533557097255659392436099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711409463007545856581465 533557097255659392436099)
            ·
              refine ⟨800335645883489088654149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533557097255659392436099 800335645883489088654149)
              ·
                refine ⟨150062933603154204122653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 800335645883489088654149 150062933603154204122653)
                ·
                  rfl

theorem cell19_493166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_493166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493166 prefixEnd_493166 := by exact prefixLift 493166
  have htrace : WordTrace (prefixWord ++ tailWord_493166) baseStart_493166 baseEnd_493166 := by
    simpa [prefixWord, tailWord_493166, baseEnd_493166] using wordTrace_append hprefix tailTrace_493166
  have hstable : (prefixWord ++ tailWord_493166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493166).length < 2 ^ (prefixWord ++ tailWord_493166).sum := by decide
  have hdescent : baseEnd_493166 < baseStart_493166 := by decide
  rcases family_descends (prefixWord ++ tailWord_493166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493168 : List Nat := [2, 1, 1, 1, 6, 3, 1, 4]
def baseStart_493168 : Nat := 118140960795 + 493168 * 2 ^ 59
def prefixEnd_493168 : Nat := 4983230072969 + 3 ^ 40 * 493168 * 2
def baseEnd_493168 : Nat := 150063542172818792078203

theorem tailTrace_493168 : CollatzResearch.WordTrace tailWord_493168 prefixEnd_493168 150063542172818792078203 := by
  unfold tailWord_493168
  simp only [CollatzResearch.WordTrace]
  refine ⟨8993657338672018616952079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11991543118229358155936105 8993657338672018616952079)
  ·
    refine ⟨13490486008008027925428119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8993657338672018616952079 13490486008008027925428119)
    ·
      refine ⟨20235729012012041888142179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13490486008008027925428119 20235729012012041888142179)
      ·
        refine ⟨30353593518018062832213269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20235729012012041888142179 30353593518018062832213269)
        ·
          refine ⟨1422824696157096695259997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30353593518018062832213269 1422824696157096695259997)
          ·
            refine ⟨533559261058911260722499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1422824696157096695259997 533559261058911260722499)
            ·
              refine ⟨800338891588366891083749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533559261058911260722499 800338891588366891083749)
              ·
                refine ⟨150063542172818792078203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 800338891588366891083749 150063542172818792078203)
                ·
                  rfl

theorem cell19_493168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_493168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493168 prefixEnd_493168 := by exact prefixLift 493168
  have htrace : WordTrace (prefixWord ++ tailWord_493168) baseStart_493168 baseEnd_493168 := by
    simpa [prefixWord, tailWord_493168, baseEnd_493168] using wordTrace_append hprefix tailTrace_493168
  have hstable : (prefixWord ++ tailWord_493168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493168).length < 2 ^ (prefixWord ++ tailWord_493168).sum := by decide
  have hdescent : baseEnd_493168 < baseStart_493168 := by decide
  rcases family_descends (prefixWord ++ tailWord_493168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493208 : List Nat := [2, 1, 2, 4, 1, 3, 6]
def baseStart_493208 : Nat := 118140960795 + 493208 * 2 ^ 59
def prefixEnd_493208 : Nat := 4983230072969 + 3 ^ 40 * 493208 * 2
def baseEnd_493208 : Nat := 50025237855370183729735

theorem tailTrace_493208 : CollatzResearch.WordTrace tailWord_493208 prefixEnd_493208 50025237855370183729735 := by
  unfold tailWord_493208
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994386798599562032680139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11992515731466082710240185 8994386798599562032680139)
  ·
    refine ⟨13491580197899343049020209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8994386798599562032680139 13491580197899343049020209)
    ·
      refine ⟨10118685148424507286765157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13491580197899343049020209 10118685148424507286765157)
      ·
        refine ⟨1897253465329595116268467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10118685148424507286765157 1897253465329595116268467)
        ·
          refine ⟨2845880197994392674402701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897253465329595116268467 2845880197994392674402701)
          ·
            refine ⟨1067205074247897252901013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2845880197994392674402701 1067205074247897252901013)
            ·
              refine ⟨50025237855370183729735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1067205074247897252901013 50025237855370183729735)
              ·
                rfl

theorem cell19_493208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_493208 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493208 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493208 prefixEnd_493208 := by exact prefixLift 493208
  have htrace : WordTrace (prefixWord ++ tailWord_493208) baseStart_493208 baseEnd_493208 := by
    simpa [prefixWord, tailWord_493208, baseEnd_493208] using wordTrace_append hprefix tailTrace_493208
  have hstable : (prefixWord ++ tailWord_493208).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493208).length < 2 ^ (prefixWord ++ tailWord_493208).sum := by decide
  have hdescent : baseEnd_493208 < baseStart_493208 := by decide
  rcases family_descends (prefixWord ++ tailWord_493208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493244 : List Nat := [2, 2, 2, 3, 1, 2, 4, 3]
def baseStart_493244 : Nat := 118140960795 + 493244 * 2 ^ 59
def prefixEnd_493244 : Nat := 4983230072969 + 3 ^ 40 * 493244 * 2
def baseEnd_493244 : Nat := 150086667820073134389107

theorem tailTrace_493244 : CollatzResearch.WordTrace tailWord_493244 prefixEnd_493244 150086667820073134389107 := by
  unfold tailWord_493244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8995043312534351106835393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11993391083379134809113857 8995043312534351106835393)
  ·
    refine ⟨6746282484400763330126545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8995043312534351106835393 6746282484400763330126545)
    ·
      refine ⟨5059711863300572497594909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6746282484400763330126545 5059711863300572497594909)
      ·
        refine ⟨1897391948737714686598091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5059711863300572497594909 1897391948737714686598091)
        ·
          refine ⟨2846087923106572029897137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897391948737714686598091 2846087923106572029897137)
          ·
            refine ⟨2134565942329929022422853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2846087923106572029897137 2134565942329929022422853)
            ·
              refine ⟨400231114186861691704285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2134565942329929022422853 400231114186861691704285)
              ·
                refine ⟨150086667820073134389107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400231114186861691704285 150086667820073134389107)
                ·
                  rfl

theorem cell19_493244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_493244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493244 prefixEnd_493244 := by exact prefixLift 493244
  have htrace : WordTrace (prefixWord ++ tailWord_493244) baseStart_493244 baseEnd_493244 := by
    simpa [prefixWord, tailWord_493244, baseEnd_493244] using wordTrace_append hprefix tailTrace_493244
  have hstable : (prefixWord ++ tailWord_493244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493244).length < 2 ^ (prefixWord ++ tailWord_493244).sum := by decide
  have hdescent : baseEnd_493244 < baseStart_493244 := by decide
  rcases family_descends (prefixWord ++ tailWord_493244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493261 : List Nat := [1, 6, 2, 1, 1, 3, 5]
def baseStart_493261 : Nat := 118140960795 + 493261 * 2 ^ 59
def prefixEnd_493261 : Nat := 4983230072969 + 3 ^ 40 * 493261 * 2
def baseEnd_493261 : Nat := 50030613554074044003761

theorem tailTrace_493261 : CollatzResearch.WordTrace tailWord_493261 prefixEnd_493261 50030613554074044003761 := by
  unfold tailWord_493261
  simp only [CollatzResearch.WordTrace]
  refine ⟨17990706666007114117039637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11993804444004742744693091 17990706666007114117039637)
  ·
    refine ⟨843314374969083474236233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17990706666007114117039637 843314374969083474236233)
    ·
      refine ⟨632485781226812605677175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 843314374969083474236233 632485781226812605677175)
      ·
        refine ⟨948728671840218908515763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632485781226812605677175 948728671840218908515763)
        ·
          refine ⟨1423093007760328362773645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948728671840218908515763 1423093007760328362773645)
          ·
            refine ⟨533659877910123136040117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1423093007760328362773645 533659877910123136040117)
            ·
              refine ⟨50030613554074044003761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 533659877910123136040117 50030613554074044003761)
              ·
                rfl

theorem cell19_493261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_493261 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493261 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493261 prefixEnd_493261 := by exact prefixLift 493261
  have htrace : WordTrace (prefixWord ++ tailWord_493261) baseStart_493261 baseEnd_493261 := by
    simpa [prefixWord, tailWord_493261, baseEnd_493261] using wordTrace_append hprefix tailTrace_493261
  have hstable : (prefixWord ++ tailWord_493261).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493261).length < 2 ^ (prefixWord ++ tailWord_493261).sum := by decide
  have hdescent : baseEnd_493261 < baseStart_493261 := by decide
  rcases family_descends (prefixWord ++ tailWord_493261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493265 : List Nat := [1, 2, 2, 1, 2, 6, 5]
def baseStart_493265 : Nat := 118140960795 + 493265 * 2 ^ 59
def prefixEnd_493265 : Nat := 4983230072969 + 3 ^ 40 * 493265 * 2
def baseEnd_493265 : Nat := 50031019267183769307461

theorem tailTrace_493265 : CollatzResearch.WordTrace tailWord_493265 prefixEnd_493265 50031019267183769307461 := by
  unfold tailWord_493265
  simp only [CollatzResearch.WordTrace]
  refine ⟨17990852557992622800185249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11993901705328415200123499 17990852557992622800185249)
  ·
    refine ⟨13493139418494467100138937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17990852557992622800185249 13493139418494467100138937)
    ·
      refine ⟨10119854563870850325104203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13493139418494467100138937 10119854563870850325104203)
      ·
        refine ⟨15179781845806275487656305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10119854563870850325104203 15179781845806275487656305)
        ·
          refine ⟨11384836384354706615742229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15179781845806275487656305 11384836384354706615742229)
          ·
            refine ⟨533664205516626872612917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11384836384354706615742229 533664205516626872612917)
            ·
              refine ⟨50031019267183769307461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 533664205516626872612917 50031019267183769307461)
              ·
                rfl

theorem cell19_493265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_493265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493265 prefixEnd_493265 := by exact prefixLift 493265
  have htrace : WordTrace (prefixWord ++ tailWord_493265) baseStart_493265 baseEnd_493265 := by
    simpa [prefixWord, tailWord_493265, baseEnd_493265] using wordTrace_append hprefix tailTrace_493265
  have hstable : (prefixWord ++ tailWord_493265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493265).length < 2 ^ (prefixWord ++ tailWord_493265).sum := by decide
  have hdescent : baseEnd_493265 < baseStart_493265 := by decide
  rcases family_descends (prefixWord ++ tailWord_493265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493284 : List Nat := [2, 3, 1, 1, 1, 3, 4, 4]
def baseStart_493284 : Nat := 118140960795 + 493284 * 2 ^ 59
def prefixEnd_493284 : Nat := 4983230072969 + 3 ^ 40 * 493284 * 2
def baseEnd_493284 : Nat := 150098839213364893500109

theorem tailTrace_493284 : CollatzResearch.WordTrace tailWord_493284 prefixEnd_493284 150098839213364893500109 := by
  unfold tailWord_493284
  simp only [CollatzResearch.WordTrace]
  refine ⟨8995772772461894522563453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11994363696615859363417937 8995772772461894522563453)
  ·
    refine ⟨3373414789673210445961295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8995772772461894522563453 3373414789673210445961295)
    ·
      refine ⟨5060122184509815668941943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3373414789673210445961295 5060122184509815668941943)
      ·
        refine ⟨7590183276764723503412915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5060122184509815668941943 7590183276764723503412915)
        ·
          refine ⟨11385274915147085255119373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7590183276764723503412915 11385274915147085255119373)
          ·
            refine ⟨4269478093180156970669765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11385274915147085255119373 4269478093180156970669765)
            ·
              refine ⟨800527142471279432000581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4269478093180156970669765 800527142471279432000581)
              ·
                refine ⟨150098839213364893500109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 800527142471279432000581 150098839213364893500109)
                ·
                  rfl

theorem cell19_493284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_493284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493284 prefixEnd_493284 := by exact prefixLift 493284
  have htrace : WordTrace (prefixWord ++ tailWord_493284) baseStart_493284 baseEnd_493284 := by
    simpa [prefixWord, tailWord_493284, baseEnd_493284] using wordTrace_append hprefix tailTrace_493284
  have hstable : (prefixWord ++ tailWord_493284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493284).length < 2 ^ (prefixWord ++ tailWord_493284).sum := by decide
  have hdescent : baseEnd_493284 < baseStart_493284 := by decide
  rcases family_descends (prefixWord ++ tailWord_493284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493381 : List Nat := [1, 3, 1, 1, 1, 2, 10]
def baseStart_493381 : Nat := 118140960795 + 493381 * 2 ^ 59
def prefixEnd_493381 : Nat := 4983230072969 + 3 ^ 40 * 493381 * 2
def baseEnd_493381 : Nat := 50042784947365803114763

theorem tailTrace_493381 : CollatzResearch.WordTrace tailWord_493381 prefixEnd_493381 50042784947365803114763 := by
  unfold tailWord_493381
  simp only [CollatzResearch.WordTrace]
  refine ⟨17995083425572374611407997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11996722283714916407605331 17995083425572374611407997)
  ·
    refine ⟨6748156284589640479277999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17995083425572374611407997 6748156284589640479277999)
    ·
      refine ⟨10122234426884460718916999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748156284589640479277999 10122234426884460718916999)
      ·
        refine ⟨15183351640326691078375499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10122234426884460718916999 15183351640326691078375499)
        ·
          refine ⟨22775027460490036617563249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15183351640326691078375499 22775027460490036617563249)
          ·
            refine ⟨17081270595367527463172437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22775027460490036617563249 17081270595367527463172437)
            ·
              refine ⟨50042784947365803114763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17081270595367527463172437 50042784947365803114763)
              ·
                rfl

theorem cell19_493381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_493381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493381 prefixEnd_493381 := by exact prefixLift 493381
  have htrace : WordTrace (prefixWord ++ tailWord_493381) baseStart_493381 baseEnd_493381 := by
    simpa [prefixWord, tailWord_493381, baseEnd_493381] using wordTrace_append hprefix tailTrace_493381
  have hstable : (prefixWord ++ tailWord_493381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493381).length < 2 ^ (prefixWord ++ tailWord_493381).sum := by decide
  have hdescent : baseEnd_493381 < baseStart_493381 := by decide
  rcases family_descends (prefixWord ++ tailWord_493381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493457 : List Nat := [1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_493457 : Nat := 118140960795 + 493457 * 2 ^ 59
def prefixEnd_493457 : Nat := 4983230072969 + 3 ^ 40 * 493457 * 2
def baseEnd_493457 : Nat := 150151480489351751655193

theorem tailTrace_493457 : CollatzResearch.WordTrace tailWord_493457 prefixEnd_493457 150151480489351751655193 := by
  unfold tailWord_493457
  simp only [CollatzResearch.WordTrace]
  refine ⟨17997855373297039591174625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11998570248864693060783083 17997855373297039591174625)
  ·
    refine ⟨13498391529972779693380969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17997855373297039591174625 13498391529972779693380969)
    ·
      refine ⟨10123793647479584770035727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13498391529972779693380969 10123793647479584770035727)
      ·
        refine ⟨15185690471219377155053591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10123793647479584770035727 15185690471219377155053591)
        ·
          refine ⟨22778535706829065732580387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15185690471219377155053591 22778535706829065732580387)
          ·
            refine ⟨34167803560243598598870581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22778535706829065732580387 34167803560243598598870581)
            ·
              refine ⟨3203231583772837368644117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34167803560243598598870581 3203231583772837368644117)
              ·
                refine ⟨150151480489351751655193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3203231583772837368644117 150151480489351751655193)
                ·
                  rfl

theorem cell19_493457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_493457 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493457 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493457 prefixEnd_493457 := by exact prefixLift 493457
  have htrace : WordTrace (prefixWord ++ tailWord_493457) baseStart_493457 baseEnd_493457 := by
    simpa [prefixWord, tailWord_493457, baseEnd_493457] using wordTrace_append hprefix tailTrace_493457
  have hstable : (prefixWord ++ tailWord_493457).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493457).length < 2 ^ (prefixWord ++ tailWord_493457).sum := by decide
  have hdescent : baseEnd_493457 < baseStart_493457 := by decide
  rcases family_descends (prefixWord ++ tailWord_493457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493512 : List Nat := [2, 1, 3, 1, 4, 1, 3, 4]
def baseStart_493512 : Nat := 118140960795 + 493512 * 2 ^ 59
def prefixEnd_493512 : Nat := 4983230072969 + 3 ^ 40 * 493512 * 2
def baseEnd_493512 : Nat := 150168216155127920432821

theorem tailTrace_493512 : CollatzResearch.WordTrace tailWord_493512 prefixEnd_493512 150168216155127920432821 := by
  unfold tailWord_493512
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999930694048891992213395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11999907592065189322951193 8999930694048891992213395)
  ·
    refine ⟨13499896041073337988320093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8999930694048891992213395 13499896041073337988320093)
    ·
      refine ⟨5062461015402501745620035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13499896041073337988320093 5062461015402501745620035)
      ·
        refine ⟨7593691523103752618430053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5062461015402501745620035 7593691523103752618430053)
        ·
          refine ⟨1423817160581953615955635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7593691523103752618430053 1423817160581953615955635)
          ·
            refine ⟨2135725740872930423933453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423817160581953615955635 2135725740872930423933453)
            ·
              refine ⟨800897152827348908975045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2135725740872930423933453 800897152827348908975045)
              ·
                refine ⟨150168216155127920432821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 800897152827348908975045 150168216155127920432821)
                ·
                  rfl

theorem cell19_493512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_493512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493512 prefixEnd_493512 := by exact prefixLift 493512
  have htrace : WordTrace (prefixWord ++ tailWord_493512) baseStart_493512 baseEnd_493512 := by
    simpa [prefixWord, tailWord_493512, baseEnd_493512] using wordTrace_append hprefix tailTrace_493512
  have hstable : (prefixWord ++ tailWord_493512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493512).length < 2 ^ (prefixWord ++ tailWord_493512).sum := by decide
  have hdescent : baseEnd_493512 < baseStart_493512 := by decide
  rcases family_descends (prefixWord ++ tailWord_493512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493529 : List Nat := [1, 2, 1, 2, 6, 1, 3, 3]
def baseStart_493529 : Nat := 118140960795 + 493529 * 2 ^ 59
def prefixEnd_493529 : Nat := 4983230072969 + 3 ^ 40 * 493529 * 2
def baseEnd_493529 : Nat := 150173388997276918054997

theorem tailTrace_493529 : CollatzResearch.WordTrace tailWord_493529 prefixEnd_493529 150173388997276918054997 := by
  unfold tailWord_493529
  simp only [CollatzResearch.WordTrace]
  refine ⟨18000481429036195887795641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12000320952690797258530427 18000481429036195887795641)
  ·
    refine ⟨13500361071777146915846731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18000481429036195887795641 13500361071777146915846731)
    ·
      refine ⟨20250541607665720373770097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13500361071777146915846731 20250541607665720373770097)
      ·
        refine ⟨15187906205749290280327573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20250541607665720373770097 15187906205749290280327573)
        ·
          refine ⟨711933103394497981890355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15187906205749290280327573 711933103394497981890355)
          ·
            refine ⟨1067899655091746972835533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711933103394497981890355 1067899655091746972835533)
            ·
              refine ⟨400462370659405114813325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1067899655091746972835533 400462370659405114813325)
              ·
                refine ⟨150173388997276918054997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400462370659405114813325 150173388997276918054997)
                ·
                  rfl

theorem cell19_493529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 3].length) (baseStart_493529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493529 prefixEnd_493529 := by exact prefixLift 493529
  have htrace : WordTrace (prefixWord ++ tailWord_493529) baseStart_493529 baseEnd_493529 := by
    simpa [prefixWord, tailWord_493529, baseEnd_493529] using wordTrace_append hprefix tailTrace_493529
  have hstable : (prefixWord ++ tailWord_493529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493529).length < 2 ^ (prefixWord ++ tailWord_493529).sum := by decide
  have hdescent : baseEnd_493529 < baseStart_493529 := by decide
  rcases family_descends (prefixWord ++ tailWord_493529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493550 : List Nat := [4, 1, 2, 1, 3, 2, 6]
def baseStart_493550 : Nat := 118140960795 + 493550 * 2 ^ 59
def prefixEnd_493550 : Nat := 4983230072969 + 3 ^ 40 * 493550 * 2
def baseEnd_493550 : Nat := 50059926326251697196091

theorem tailTrace_493550 : CollatzResearch.WordTrace tailWord_493550 prefixEnd_493550 50059926326251697196091 := by
  unfold tailWord_493550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250155920245014559288763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12000831574640077649540069 2250155920245014559288763)
  ·
    refine ⟨3375233880367521838933145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2250155920245014559288763 3375233880367521838933145)
    ·
      refine ⟨2531425410275641379199859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3375233880367521838933145 2531425410275641379199859)
      ·
        refine ⟨3797138115413462068799789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531425410275641379199859 3797138115413462068799789)
        ·
          refine ⟨1423926793280048275799921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3797138115413462068799789 1423926793280048275799921)
          ·
            refine ⟨1067945094960036206849941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423926793280048275799921 1067945094960036206849941)
            ·
              refine ⟨50059926326251697196091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1067945094960036206849941 50059926326251697196091)
              ·
                rfl

theorem cell19_493550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_493550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493550 prefixEnd_493550 := by exact prefixLift 493550
  have htrace : WordTrace (prefixWord ++ tailWord_493550) baseStart_493550 baseEnd_493550 := by
    simpa [prefixWord, tailWord_493550, baseEnd_493550] using wordTrace_append hprefix tailTrace_493550
  have hstable : (prefixWord ++ tailWord_493550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493550).length < 2 ^ (prefixWord ++ tailWord_493550).sum := by decide
  have hdescent : baseEnd_493550 < baseStart_493550 := by decide
  rcases family_descends (prefixWord ++ tailWord_493550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493645 : List Nat := [1, 6, 1, 1, 1, 1, 1, 7]
def baseStart_493645 : Nat := 118140960795 + 493645 * 2 ^ 59
def prefixEnd_493645 : Nat := 4983230072969 + 3 ^ 40 * 493645 * 2
def baseEnd_493645 : Nat := 150208686037823019476903

theorem tailTrace_493645 : CollatzResearch.WordTrace tailWord_493645 prefixEnd_493645 150208686037823019476903 := by
  unfold tailWord_493645
  simp only [CollatzResearch.WordTrace]
  refine ⟨18004712296615947699018389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12003141531077298466012259 18004712296615947699018389)
  ·
    refine ⟨843970888903872548391487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18004712296615947699018389 843970888903872548391487)
    ·
      refine ⟨1265956333355808822587231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843970888903872548391487 1265956333355808822587231)
      ·
        refine ⟨1898934500033713233880847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265956333355808822587231 1898934500033713233880847)
        ·
          refine ⟨2848401750050569850821271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898934500033713233880847 2848401750050569850821271)
          ·
            refine ⟨4272602625075854776231907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848401750050569850821271 4272602625075854776231907)
            ·
              refine ⟨6408903937613782164347861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272602625075854776231907 6408903937613782164347861)
              ·
                refine ⟨150208686037823019476903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6408903937613782164347861 150208686037823019476903)
                ·
                  rfl

theorem cell19_493645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_493645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493645 prefixEnd_493645 := by exact prefixLift 493645
  have htrace : WordTrace (prefixWord ++ tailWord_493645) baseStart_493645 baseEnd_493645 := by
    simpa [prefixWord, tailWord_493645, baseEnd_493645] using wordTrace_append hprefix tailTrace_493645
  have hstable : (prefixWord ++ tailWord_493645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493645).length < 2 ^ (prefixWord ++ tailWord_493645).sum := by decide
  have hdescent : baseEnd_493645 < baseStart_493645 := by decide
  rcases family_descends (prefixWord ++ tailWord_493645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493662 : List Nat := [4, 4, 1, 1, 9]
def baseStart_493662 : Nat := 118140960795 + 493662 * 2 ^ 59
def prefixEnd_493662 : Nat := 4983230072969 + 3 ^ 40 * 493662 * 2
def baseEnd_493662 : Nat := 5563476254813778411077

theorem tailTrace_493662 : CollatzResearch.WordTrace tailWord_493662 prefixEnd_493662 5563476254813778411077 := by
  unfold tailWord_493662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250666542194294950298405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12003554891702906401591493 2250666542194294950298405)
  ·
    refine ⟨421999976661430303180951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2250666542194294950298405 421999976661430303180951)
    ·
      refine ⟨632999964992145454771427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421999976661430303180951 632999964992145454771427)
      ·
        refine ⟨949499947488218182157141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632999964992145454771427 949499947488218182157141)
        ·
          refine ⟨5563476254813778411077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 949499947488218182157141 5563476254813778411077)
          ·
            rfl

theorem cell19_493662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 9].length) (baseStart_493662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493662 prefixEnd_493662 := by exact prefixLift 493662
  have htrace : WordTrace (prefixWord ++ tailWord_493662) baseStart_493662 baseEnd_493662 := by
    simpa [prefixWord, tailWord_493662, baseEnd_493662] using wordTrace_append hprefix tailTrace_493662
  have hstable : (prefixWord ++ tailWord_493662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493662).length < 2 ^ (prefixWord ++ tailWord_493662).sum := by decide
  have hdescent : baseEnd_493662 < baseStart_493662 := by decide
  rcases family_descends (prefixWord ++ tailWord_493662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493778 : List Nat := [3, 2, 2, 2, 1, 4, 5]
def baseStart_493778 : Nat := 118140960795 + 493778 * 2 ^ 59
def prefixEnd_493778 : Nat := 4983230072969 + 3 ^ 40 * 493778 * 2
def baseEnd_493778 : Nat := 50083051973506039506995

theorem tailTrace_493778 : CollatzResearch.WordTrace tailWord_493778 prefixEnd_493778 50083051973506039506995 := by
  unfold tailWord_493778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4502390801283527853402497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12006375470089407609073325 4502390801283527853402497)
  ·
    refine ⟨3376793100962645890051873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4502390801283527853402497 3376793100962645890051873)
    ·
      refine ⟨2532594825721984417538905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3376793100962645890051873 2532594825721984417538905)
      ·
        refine ⟨1899446119291488313154179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2532594825721984417538905 1899446119291488313154179)
        ·
          refine ⟨2849169178937232469731269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1899446119291488313154179 2849169178937232469731269)
          ·
            refine ⟨534219221050731088074613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2849169178937232469731269 534219221050731088074613)
            ·
              refine ⟨50083051973506039506995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 534219221050731088074613 50083051973506039506995)
              ·
                rfl

theorem cell19_493778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_493778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493778 prefixEnd_493778 := by exact prefixLift 493778
  have htrace : WordTrace (prefixWord ++ tailWord_493778) baseStart_493778 baseEnd_493778 := by
    simpa [prefixWord, tailWord_493778, baseEnd_493778] using wordTrace_append hprefix tailTrace_493778
  have hstable : (prefixWord ++ tailWord_493778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493778).length < 2 ^ (prefixWord ++ tailWord_493778).sum := by decide
  have hdescent : baseEnd_493778 < baseStart_493778 := by decide
  rcases family_descends (prefixWord ++ tailWord_493778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493795 : List Nat := [1, 1, 1, 8, 1, 1, 2, 4]
def baseStart_493795 : Nat := 118140960795 + 493795 * 2 ^ 59
def prefixEnd_493795 : Nat := 4983230072969 + 3 ^ 40 * 493795 * 2
def baseEnd_493795 : Nat := 150254328762667116143161

theorem tailTrace_493795 : CollatzResearch.WordTrace tailWord_493795 prefixEnd_493795 150254328762667116143161 := by
  unfold tailWord_493795
  simp only [CollatzResearch.WordTrace]
  refine ⟨18010183246072523316978839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12006788830715015544652559 18010183246072523316978839)
  ·
    refine ⟨27015274869108784975468259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18010183246072523316978839 27015274869108784975468259)
    ·
      refine ⟨40522912303663177463202389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27015274869108784975468259 40522912303663177463202389)
      ·
        refine ⟨474877878558552860896903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 40522912303663177463202389 474877878558552860896903)
        ·
          refine ⟨712316817837829291345355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474877878558552860896903 712316817837829291345355)
          ·
            refine ⟨1068475226756743937018033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712316817837829291345355 1068475226756743937018033)
            ·
              refine ⟨801356420067557952763525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068475226756743937018033 801356420067557952763525)
              ·
                refine ⟨150254328762667116143161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 801356420067557952763525 150254328762667116143161)
                ·
                  rfl

theorem cell19_493795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 4].length) (baseStart_493795 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493795 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493795 prefixEnd_493795 := by exact prefixLift 493795
  have htrace : WordTrace (prefixWord ++ tailWord_493795) baseStart_493795 baseEnd_493795 := by
    simpa [prefixWord, tailWord_493795, baseEnd_493795] using wordTrace_append hprefix tailTrace_493795
  have hstable : (prefixWord ++ tailWord_493795).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493795).length < 2 ^ (prefixWord ++ tailWord_493795).sum := by decide
  have hdescent : baseEnd_493795 < baseStart_493795 := by decide
  rcases family_descends (prefixWord ++ tailWord_493795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493797 : List Nat := [1, 3, 1, 4, 2, 2, 2, 4]
def baseStart_493797 : Nat := 118140960795 + 493797 * 2 ^ 59
def prefixEnd_493797 : Nat := 4983230072969 + 3 ^ 40 * 493797 * 2
def baseEnd_493797 : Nat := 150254937332331704098711

theorem tailTrace_493797 : CollatzResearch.WordTrace tailWord_493797 prefixEnd_493797 150254937332331704098711 := by
  unfold tailWord_493797
  simp only [CollatzResearch.WordTrace]
  refine ⟨18010256192065277658551645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12006837461376851772367763 18010256192065277658551645)
  ·
    refine ⟨6753846072024479121956867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18010256192065277658551645 6753846072024479121956867)
    ·
      refine ⟨10130769108036718682935301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6753846072024479121956867 10130769108036718682935301)
      ·
        refine ⟨1899519207756884753050369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10130769108036718682935301 1899519207756884753050369)
        ·
          refine ⟨1424639405817663564787777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1899519207756884753050369 1424639405817663564787777)
          ·
            refine ⟨1068479554363247673590833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1424639405817663564787777 1068479554363247673590833)
            ·
              refine ⟨801359665772435755193125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068479554363247673590833 801359665772435755193125)
              ·
                refine ⟨150254937332331704098711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 801359665772435755193125 150254937332331704098711)
                ·
                  rfl

theorem cell19_493797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_493797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493797 prefixEnd_493797 := by exact prefixLift 493797
  have htrace : WordTrace (prefixWord ++ tailWord_493797) baseStart_493797 baseEnd_493797 := by
    simpa [prefixWord, tailWord_493797, baseEnd_493797] using wordTrace_append hprefix tailTrace_493797
  have hstable : (prefixWord ++ tailWord_493797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493797).length < 2 ^ (prefixWord ++ tailWord_493797).sum := by decide
  have hdescent : baseEnd_493797 < baseStart_493797 := by decide
  rcases family_descends (prefixWord ++ tailWord_493797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493818 : List Nat := [3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_493818 : Nat := 118140960795 + 493818 * 2 ^ 59
def prefixEnd_493818 : Nat := 4983230072969 + 3 ^ 40 * 493818 * 2
def baseEnd_493818 : Nat := 150261327313809877631987

theorem tailTrace_493818 : CollatzResearch.WordTrace tailWord_493818 prefixEnd_493818 150261327313809877631987 := by
  unfold tailWord_493818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4502755531247299561266527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12007348083326132163377405 4502755531247299561266527)
  ·
    refine ⟨6754133296870949341899791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4502755531247299561266527 6754133296870949341899791)
    ·
      refine ⟨10131199945306424012849687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6754133296870949341899791 10131199945306424012849687)
      ·
        refine ⟨15196799917959636019274531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10131199945306424012849687 15196799917959636019274531)
        ·
          refine ⟨22795199876939454028911797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15196799917959636019274531 22795199876939454028911797)
          ·
            refine ⟨2137049988463073815210481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22795199876939454028911797 2137049988463073815210481)
            ·
              refine ⟨1602787491347305361407861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137049988463073815210481 1602787491347305361407861)
              ·
                refine ⟨150261327313809877631987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1602787491347305361407861 150261327313809877631987)
                ·
                  rfl

theorem cell19_493818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_493818 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493818 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493818 prefixEnd_493818 := by exact prefixLift 493818
  have htrace : WordTrace (prefixWord ++ tailWord_493818) baseStart_493818 baseEnd_493818 := by
    simpa [prefixWord, tailWord_493818, baseEnd_493818] using wordTrace_append hprefix tailTrace_493818
  have hstable : (prefixWord ++ tailWord_493818).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493818).length < 2 ^ (prefixWord ++ tailWord_493818).sum := by decide
  have hdescent : baseEnd_493818 < baseStart_493818 := by decide
  rcases family_descends (prefixWord ++ tailWord_493818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493869 : List Nat := [1, 5, 3, 1, 2, 1, 3, 3]
def baseStart_493869 : Nat := 118140960795 + 493869 * 2 ^ 59
def prefixEnd_493869 : Nat := 4983230072969 + 3 ^ 40 * 493869 * 2
def baseEnd_493869 : Nat := 150276845840256870498515

theorem tailTrace_493869 : CollatzResearch.WordTrace tailWord_493869 prefixEnd_493869 150276845840256870498515 := by
  unfold tailWord_493869
  simp only [CollatzResearch.WordTrace]
  refine ⟨18012882247804433955172661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12008588165202955970115107 18012882247804433955172661)
  ·
    refine ⟨1688707710731665683297437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18012882247804433955172661 1688707710731665683297437)
    ·
      refine ⟨633265391524374631236539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1688707710731665683297437 633265391524374631236539)
      ·
        refine ⟨949898087286561946854809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633265391524374631236539 949898087286561946854809)
        ·
          refine ⟨712423565464921460141107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949898087286561946854809 712423565464921460141107)
          ·
            refine ⟨1068635348197382190211661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712423565464921460141107 1068635348197382190211661)
            ·
              refine ⟨400738255574018321329373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1068635348197382190211661 400738255574018321329373)
              ·
                refine ⟨150276845840256870498515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400738255574018321329373 150276845840256870498515)
                ·
                  rfl

theorem cell19_493869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 3].length) (baseStart_493869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493869 prefixEnd_493869 := by exact prefixLift 493869
  have htrace : WordTrace (prefixWord ++ tailWord_493869) baseStart_493869 baseEnd_493869 := by
    simpa [prefixWord, tailWord_493869, baseEnd_493869] using wordTrace_append hprefix tailTrace_493869
  have hstable : (prefixWord ++ tailWord_493869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493869).length < 2 ^ (prefixWord ++ tailWord_493869).sum := by decide
  have hdescent : baseEnd_493869 < baseStart_493869 := by decide
  rcases family_descends (prefixWord ++ tailWord_493869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493928 : List Nat := [2, 1, 4, 2, 2, 3, 2, 3]
def baseStart_493928 : Nat := 118140960795 + 493928 * 2 ^ 59
def prefixEnd_493928 : Nat := 4983230072969 + 3 ^ 40 * 493928 * 2
def baseEnd_493928 : Nat := 150294798645362215187243

theorem tailTrace_493928 : CollatzResearch.WordTrace tailWord_493928 prefixEnd_493928 150294798645362215187243 := by
  unfold tailWord_493928
  simp only [CollatzResearch.WordTrace]
  refine ⟨9007517077295343515785219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12010022769727124687713625 9007517077295343515785219)
  ·
    refine ⟨13511275615943015273677829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9007517077295343515785219 13511275615943015273677829)
    ·
      refine ⟨2533364177989315363814593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13511275615943015273677829 2533364177989315363814593)
      ·
        refine ⟨1900023133491986522860945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2533364177989315363814593 1900023133491986522860945)
        ·
          refine ⟨1425017350118989892145709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1900023133491986522860945 1425017350118989892145709)
          ·
            refine ⟨534381506294621209554641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1425017350118989892145709 534381506294621209554641)
            ·
              refine ⟨400786129720965907165981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534381506294621209554641 400786129720965907165981)
              ·
                refine ⟨150294798645362215187243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400786129720965907165981 150294798645362215187243)
                ·
                  rfl

theorem cell19_493928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_493928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493928 prefixEnd_493928 := by exact prefixLift 493928
  have htrace : WordTrace (prefixWord ++ tailWord_493928) baseStart_493928 baseEnd_493928 := by
    simpa [prefixWord, tailWord_493928, baseEnd_493928] using wordTrace_append hprefix tailTrace_493928
  have hstable : (prefixWord ++ tailWord_493928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493928).length < 2 ^ (prefixWord ++ tailWord_493928).sum := by decide
  have hdescent : baseEnd_493928 < baseStart_493928 := by decide
  rcases family_descends (prefixWord ++ tailWord_493928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493930 : List Nat := [3, 1, 3, 3, 1, 2, 1, 5]
def baseStart_493930 : Nat := 118140960795 + 493930 * 2 ^ 59
def prefixEnd_493930 : Nat := 4983230072969 + 3 ^ 40 * 493930 * 2
def baseEnd_493930 : Nat := 150295407215026803142793

theorem tailTrace_493930 : CollatzResearch.WordTrace tailWord_493930 prefixEnd_493930 150295407215026803142793 := by
  unfold tailWord_493930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4503776775145860343285811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12010071400388960915428829 4503776775145860343285811)
  ·
    refine ⟨6755665162718790514928717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4503776775145860343285811 6755665162718790514928717)
    ·
      refine ⟨2533374436019546443098269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6755665162718790514928717 2533374436019546443098269)
      ·
        refine ⟨950015413507329916161851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2533374436019546443098269 950015413507329916161851)
        ·
          refine ⟨1425023120260994874242777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950015413507329916161851 1425023120260994874242777)
          ·
            refine ⟨1068767340195746155682083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1425023120260994874242777 1068767340195746155682083)
            ·
              refine ⟨1603151010293619233523125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068767340195746155682083 1603151010293619233523125)
              ·
                refine ⟨150295407215026803142793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1603151010293619233523125 150295407215026803142793)
                ·
                  rfl

theorem cell19_493930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_493930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_493930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_493930 prefixEnd_493930 := by exact prefixLift 493930
  have htrace : WordTrace (prefixWord ++ tailWord_493930) baseStart_493930 baseEnd_493930 := by
    simpa [prefixWord, tailWord_493930, baseEnd_493930] using wordTrace_append hprefix tailTrace_493930
  have hstable : (prefixWord ++ tailWord_493930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493930).length < 2 ^ (prefixWord ++ tailWord_493930).sum := by decide
  have hdescent : baseEnd_493930 < baseStart_493930 := by decide
  rcases family_descends (prefixWord ++ tailWord_493930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494004 : List Nat := [2, 5, 2, 2, 1, 7]
def baseStart_494004 : Nat := 118140960795 + 494004 * 2 ^ 59
def prefixEnd_494004 : Nat := 4983230072969 + 3 ^ 40 * 494004 * 2
def baseEnd_494004 : Nat := 16701991588068506388683

theorem tailTrace_494004 : CollatzResearch.WordTrace tailWord_494004 prefixEnd_494004 16701991588068506388683 := by
  unfold tailWord_494004
  simp only [CollatzResearch.WordTrace]
  refine ⟨9008903051157676005668533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12011870734876901340891377 9008903051157676005668533)
  ·
    refine ⟨844584661046032125531425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9008903051157676005668533 844584661046032125531425)
    ·
      refine ⟨633438495784524094148569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 844584661046032125531425 633438495784524094148569)
      ·
        refine ⟨475078871838393070611427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633438495784524094148569 475078871838393070611427)
        ·
          refine ⟨712618307757589605917141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475078871838393070611427 712618307757589605917141)
          ·
            refine ⟨16701991588068506388683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 712618307757589605917141 16701991588068506388683)
            ·
              rfl

theorem cell19_494004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 7].length) (baseStart_494004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494004 prefixEnd_494004 := by exact prefixLift 494004
  have htrace : WordTrace (prefixWord ++ tailWord_494004) baseStart_494004 baseEnd_494004 := by
    simpa [prefixWord, tailWord_494004, baseEnd_494004] using wordTrace_append hprefix tailTrace_494004
  have hstable : (prefixWord ++ tailWord_494004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494004).length < 2 ^ (prefixWord ++ tailWord_494004).sum := by decide
  have hdescent : baseEnd_494004 < baseStart_494004 := by decide
  rcases family_descends (prefixWord ++ tailWord_494004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494067 : List Nat := [1, 1, 1, 2, 2, 2, 10]
def baseStart_494067 : Nat := 118140960795 + 494067 * 2 ^ 59
def prefixEnd_494067 : Nat := 4983230072969 + 3 ^ 40 * 494067 * 2
def baseEnd_494067 : Nat := 50112364745683692699325

theorem tailTrace_494067 : CollatzResearch.WordTrace tailWord_494067 prefixEnd_494067 50112364745683692699325 := by
  unfold tailWord_494067
  simp only [CollatzResearch.WordTrace]
  refine ⟨18020103901087113770880455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12013402600724742513920303 18020103901087113770880455)
  ·
    refine ⟨27030155851630670656320683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18020103901087113770880455 27030155851630670656320683)
    ·
      refine ⟨40545233777446005984481025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27030155851630670656320683 40545233777446005984481025)
      ·
        refine ⟨30408925333084504488360769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40545233777446005984481025 30408925333084504488360769)
        ·
          refine ⟨22806693999813378366270577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30408925333084504488360769 22806693999813378366270577)
          ·
            refine ⟨17105020499860033774702933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22806693999813378366270577 17105020499860033774702933)
            ·
              refine ⟨50112364745683692699325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17105020499860033774702933 50112364745683692699325)
              ·
                rfl

theorem cell19_494067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_494067 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494067 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494067 prefixEnd_494067 := by exact prefixLift 494067
  have htrace : WordTrace (prefixWord ++ tailWord_494067) baseStart_494067 baseEnd_494067 := by
    simpa [prefixWord, tailWord_494067, baseEnd_494067] using wordTrace_append hprefix tailTrace_494067
  have hstable : (prefixWord ++ tailWord_494067).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494067).length < 2 ^ (prefixWord ++ tailWord_494067).sum := by decide
  have hdescent : baseEnd_494067 < baseStart_494067 := by decide
  rcases family_descends (prefixWord ++ tailWord_494067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494105 : List Nat := [1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_494105 : Nat := 118140960795 + 494105 * 2 ^ 59
def prefixEnd_494105 : Nat := 4983230072969 + 3 ^ 40 * 494105 * 2
def baseEnd_494105 : Nat := 150348657060678249253427

theorem tailTrace_494105 : CollatzResearch.WordTrace tailWord_494105 prefixEnd_494105 150348657060678249253427 := by
  unfold tailWord_494105
  simp only [CollatzResearch.WordTrace]
  refine ⟨18021489874949446260763769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12014326583299630840509179 18021489874949446260763769)
  ·
    refine ⟨13516117406212084695572827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18021489874949446260763769 13516117406212084695572827)
    ·
      refine ⟨20274176109318127043359241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13516117406212084695572827 20274176109318127043359241)
      ·
        refine ⟨15205632081988595282519431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20274176109318127043359241 15205632081988595282519431)
        ·
          refine ⟨22808448122982892923779147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15205632081988595282519431 22808448122982892923779147)
          ·
            refine ⟨34212672184474339385668721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22808448122982892923779147 34212672184474339385668721)
            ·
              refine ⟨25659504138355754539251541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34212672184474339385668721 25659504138355754539251541)
              ·
                refine ⟨150348657060678249253427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25659504138355754539251541 150348657060678249253427)
                ·
                  rfl

theorem cell19_494105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_494105 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494105 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494105 prefixEnd_494105 := by exact prefixLift 494105
  have htrace : WordTrace (prefixWord ++ tailWord_494105) baseStart_494105 baseEnd_494105 := by
    simpa [prefixWord, tailWord_494105, baseEnd_494105] using wordTrace_append hprefix tailTrace_494105
  have hstable : (prefixWord ++ tailWord_494105).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494105).length < 2 ^ (prefixWord ++ tailWord_494105).sum := by decide
  have hdescent : baseEnd_494105 < baseStart_494105 := by decide
  rcases family_descends (prefixWord ++ tailWord_494105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494120 : List Nat := [2, 1, 5, 2, 1, 3, 5]
def baseStart_494120 : Nat := 118140960795 + 494120 * 2 ^ 59
def prefixEnd_494120 : Nat := 4983230072969 + 3 ^ 40 * 494120 * 2
def baseEnd_494120 : Nat := 50117740444387552973351

theorem tailTrace_494120 : CollatzResearch.WordTrace tailWord_494120 prefixEnd_494120 50117740444387552973351 := by
  unfold tailWord_494120
  simp only [CollatzResearch.WordTrace]
  refine ⟨9011018484947551911279907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12014691313263402548373209 9011018484947551911279907)
  ·
    refine ⟨13516527727421327866919861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9011018484947551911279907 13516527727421327866919861)
    ·
      refine ⟨1267174474445749487523737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13516527727421327866919861 1267174474445749487523737)
      ·
        refine ⟨950380855834312115642803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1267174474445749487523737 950380855834312115642803)
        ·
          refine ⟨1425571283751468173464205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950380855834312115642803 1425571283751468173464205)
          ·
            refine ⟨534589231406800565049077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1425571283751468173464205 534589231406800565049077)
            ·
              refine ⟨50117740444387552973351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 534589231406800565049077 50117740444387552973351)
              ·
                rfl

theorem cell19_494120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_494120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494120 prefixEnd_494120 := by exact prefixLift 494120
  have htrace : WordTrace (prefixWord ++ tailWord_494120) baseStart_494120 baseEnd_494120 := by
    simpa [prefixWord, tailWord_494120, baseEnd_494120] using wordTrace_append hprefix tailTrace_494120
  have hstable : (prefixWord ++ tailWord_494120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494120).length < 2 ^ (prefixWord ++ tailWord_494120).sum := by decide
  have hdescent : baseEnd_494120 < baseStart_494120 := by decide
  rcases family_descends (prefixWord ++ tailWord_494120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494122 : List Nat := [3, 1, 4, 1, 1, 2, 7]
def baseStart_494122 : Nat := 118140960795 + 494122 * 2 ^ 59
def prefixEnd_494122 : Nat := 4983230072969 + 3 ^ 40 * 494122 * 2
def baseEnd_494122 : Nat := 50117943300942415625201

theorem tailTrace_494122 : CollatzResearch.WordTrace tailWord_494122 prefixEnd_494122 50117943300942415625201 := by
  unfold tailWord_494122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4505527478971964541033155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12014739943925238776088413 4505527478971964541033155)
  ·
    refine ⟨6758291218457946811549733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4505527478971964541033155 6758291218457946811549733)
    ·
      refine ⟨1267179603460865027165575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6758291218457946811549733 1267179603460865027165575)
      ·
        refine ⟨1900769405191297540748363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267179603460865027165575 1900769405191297540748363)
        ·
          refine ⟨2851154107786946311122545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900769405191297540748363 2851154107786946311122545)
          ·
            refine ⟨2138365580840209733341909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2851154107786946311122545 2138365580840209733341909)
            ·
              refine ⟨50117943300942415625201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2138365580840209733341909 50117943300942415625201)
              ·
                rfl

theorem cell19_494122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_494122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494122 prefixEnd_494122 := by exact prefixLift 494122
  have htrace : WordTrace (prefixWord ++ tailWord_494122) baseStart_494122 baseEnd_494122 := by
    simpa [prefixWord, tailWord_494122, baseEnd_494122] using wordTrace_append hprefix tailTrace_494122
  have hstable : (prefixWord ++ tailWord_494122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494122).length < 2 ^ (prefixWord ++ tailWord_494122).sum := by decide
  have hdescent : baseEnd_494122 < baseStart_494122 := by decide
  rcases family_descends (prefixWord ++ tailWord_494122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494141 : List Nat := [1, 4, 1, 3, 2, 1, 1, 6]
def baseStart_494141 : Nat := 118140960795 + 494141 * 2 ^ 59
def prefixEnd_494141 : Nat := 4983230072969 + 3 ^ 40 * 494141 * 2
def baseEnd_494141 : Nat := 150359611314640832453329

theorem tailTrace_494141 : CollatzResearch.WordTrace tailWord_494141 prefixEnd_494141 150359611314640832453329 := by
  unfold tailWord_494141
  simp only [CollatzResearch.WordTrace]
  refine ⟨18022802902819024409074277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12015201935212682939382851 18022802902819024409074277)
  ·
    refine ⟨3379275544278567076701427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18022802902819024409074277 3379275544278567076701427)
    ·
      refine ⟨5068913316417850615052141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3379275544278567076701427 5068913316417850615052141)
      ·
        refine ⟨1900842493656693980644553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5068913316417850615052141 1900842493656693980644553)
        ·
          refine ⟨1425631870242520485483415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1900842493656693980644553 1425631870242520485483415)
          ·
            refine ⟨2138447805363780728225123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425631870242520485483415 2138447805363780728225123)
            ·
              refine ⟨3207671708045671092337685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138447805363780728225123 3207671708045671092337685)
              ·
                refine ⟨150359611314640832453329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3207671708045671092337685 150359611314640832453329)
                ·
                  rfl

theorem cell19_494141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_494141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494141 prefixEnd_494141 := by exact prefixLift 494141
  have htrace : WordTrace (prefixWord ++ tailWord_494141) baseStart_494141 baseEnd_494141 := by
    simpa [prefixWord, tailWord_494141, baseEnd_494141] using wordTrace_append hprefix tailTrace_494141
  have hstable : (prefixWord ++ tailWord_494141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494141).length < 2 ^ (prefixWord ++ tailWord_494141).sum := by decide
  have hdescent : baseEnd_494141 < baseStart_494141 := by decide
  rcases family_descends (prefixWord ++ tailWord_494141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494181 : List Nat := [1, 3, 1, 3, 11]
def baseStart_494181 : Nat := 118140960795 + 494181 * 2 ^ 59
def prefixEnd_494181 : Nat := 4983230072969 + 3 ^ 40 * 494181 * 2
def baseEnd_494181 : Nat := 5569325285478984872753

theorem tailTrace_494181 : CollatzResearch.WordTrace tailWord_494181 prefixEnd_494181 5569325285478984872753 := by
  unfold tailWord_494181
  simp only [CollatzResearch.WordTrace]
  refine ⟨18024261822674111240530397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12016174548449407493686931 18024261822674111240530397)
  ·
    refine ⟨6759098183502791715198899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18024261822674111240530397 6759098183502791715198899)
    ·
      refine ⟨10138647275254187572798349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6759098183502791715198899 10138647275254187572798349)
      ·
        refine ⟨3801992728220320339799381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10138647275254187572798349 3801992728220320339799381)
        ·
          refine ⟨5569325285478984872753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3801992728220320339799381 5569325285478984872753)
          ·
            rfl

theorem cell19_494181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 11].length) (baseStart_494181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494181 prefixEnd_494181 := by exact prefixLift 494181
  have htrace : WordTrace (prefixWord ++ tailWord_494181) baseStart_494181 baseEnd_494181 := by
    simpa [prefixWord, tailWord_494181, baseEnd_494181] using wordTrace_append hprefix tailTrace_494181
  have hstable : (prefixWord ++ tailWord_494181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494181).length < 2 ^ (prefixWord ++ tailWord_494181).sum := by decide
  have hdescent : baseEnd_494181 < baseStart_494181 := by decide
  rcases family_descends (prefixWord ++ tailWord_494181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494194 : List Nat := [3, 2, 1, 2, 5, 1, 1, 4]
def baseStart_494194 : Nat := 118140960795 + 494194 * 2 ^ 59
def prefixEnd_494194 : Nat := 4983230072969 + 3 ^ 40 * 494194 * 2
def baseEnd_494194 : Nat := 150375738410752413275407

theorem tailTrace_494194 : CollatzResearch.WordTrace tailWord_494194 prefixEnd_494194 150375738410752413275407 := by
  unfold tailWord_494194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506183992906753615188409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12016490647751342973835757 4506183992906753615188409)
  ·
    refine ⟨3379637994680065211391307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4506183992906753615188409 3379637994680065211391307)
    ·
      refine ⟨5069456992020097817086961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3379637994680065211391307 5069456992020097817086961)
      ·
        refine ⟨3802092744015073362815221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5069456992020097817086961 3802092744015073362815221)
        ·
          refine ⟨356446194751413127763927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3802092744015073362815221 356446194751413127763927)
          ·
            refine ⟨534669292127119691645891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356446194751413127763927 534669292127119691645891)
            ·
              refine ⟨802003938190679537468837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534669292127119691645891 802003938190679537468837)
              ·
                refine ⟨150375738410752413275407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 802003938190679537468837 150375738410752413275407)
                ·
                  rfl

theorem cell19_494194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_494194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494194 prefixEnd_494194 := by exact prefixLift 494194
  have htrace : WordTrace (prefixWord ++ tailWord_494194) baseStart_494194 baseEnd_494194 := by
    simpa [prefixWord, tailWord_494194, baseEnd_494194] using wordTrace_append hprefix tailTrace_494194
  have hstable : (prefixWord ++ tailWord_494194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494194).length < 2 ^ (prefixWord ++ tailWord_494194).sum := by decide
  have hdescent : baseEnd_494194 < baseStart_494194 := by decide
  rcases family_descends (prefixWord ++ tailWord_494194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494234 : List Nat := [3, 1, 1, 6, 1, 1, 6]
def baseStart_494234 : Nat := 118140960795 + 494234 * 2 ^ 59
def prefixEnd_494234 : Nat := 4983230072969 + 3 ^ 40 * 494234 * 2
def baseEnd_494234 : Nat := 50129303268014724128803

theorem tailTrace_494234 : CollatzResearch.WordTrace tailWord_494234 prefixEnd_494234 50129303268014724128803 := by
  unfold tailWord_494234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506548722870525323052439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12017463260988067528139837 4506548722870525323052439)
  ·
    refine ⟨6759823084305787984578659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4506548722870525323052439 6759823084305787984578659)
    ·
      refine ⟨10139734626458681976867989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6759823084305787984578659 10139734626458681976867989)
      ·
        refine ⟨475300060615250717665687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10139734626458681976867989 475300060615250717665687)
        ·
          refine ⟨712950090922876076498531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475300060615250717665687 712950090922876076498531)
          ·
            refine ⟨1069425136384314114747797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712950090922876076498531 1069425136384314114747797)
            ·
              refine ⟨50129303268014724128803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1069425136384314114747797 50129303268014724128803)
              ·
                rfl

theorem cell19_494234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 6].length) (baseStart_494234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494234 prefixEnd_494234 := by exact prefixLift 494234
  have htrace : WordTrace (prefixWord ++ tailWord_494234) baseStart_494234 baseEnd_494234 := by
    simpa [prefixWord, tailWord_494234, baseEnd_494234] using wordTrace_append hprefix tailTrace_494234
  have hstable : (prefixWord ++ tailWord_494234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494234).length < 2 ^ (prefixWord ++ tailWord_494234).sum := by decide
  have hdescent : baseEnd_494234 < baseStart_494234 := by decide
  rcases family_descends (prefixWord ++ tailWord_494234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494236 : List Nat := [2, 2, 3, 2, 2, 2, 6]
def baseStart_494236 : Nat := 118140960795 + 494236 * 2 ^ 59
def prefixEnd_494236 : Nat := 4983230072969 + 3 ^ 40 * 494236 * 2
def baseEnd_494236 : Nat := 50129506124569586780653

theorem tailTrace_494236 : CollatzResearch.WordTrace tailWord_494236 prefixEnd_494236 50129506124569586780653 := by
  unfold tailWord_494236
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013133918737427816891281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12017511891649903755855041 9013133918737427816891281)
  ·
    refine ⟨6759850439053070862668461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9013133918737427816891281 6759850439053070862668461)
    ·
      refine ⟨2534943914644901573500673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6759850439053070862668461 2534943914644901573500673)
      ·
        refine ⟨1901207935983676180125505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2534943914644901573500673 1901207935983676180125505)
        ·
          refine ⟨1425905951987757135094129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1901207935983676180125505 1425905951987757135094129)
          ·
            refine ⟨1069429463990817851320597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1425905951987757135094129 1069429463990817851320597)
            ·
              refine ⟨50129506124569586780653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1069429463990817851320597 50129506124569586780653)
              ·
                rfl

theorem cell19_494236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_494236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494236 prefixEnd_494236 := by exact prefixLift 494236
  have htrace : WordTrace (prefixWord ++ tailWord_494236) baseStart_494236 baseEnd_494236 := by
    simpa [prefixWord, tailWord_494236, baseEnd_494236] using wordTrace_append hprefix tailTrace_494236
  have hstable : (prefixWord ++ tailWord_494236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494236).length < 2 ^ (prefixWord ++ tailWord_494236).sum := by decide
  have hdescent : baseEnd_494236 < baseStart_494236 := by decide
  rcases family_descends (prefixWord ++ tailWord_494236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494272 : List Nat := [2, 1, 1, 2, 4, 4, 2, 3]
def baseStart_494272 : Nat := 118140960795 + 494272 * 2 ^ 59
def prefixEnd_494272 : Nat := 4983230072969 + 3 ^ 40 * 494272 * 2
def baseEnd_494272 : Nat := 150399472627671343541861

theorem tailTrace_494272 : CollatzResearch.WordTrace tailWord_494272 prefixEnd_494272 150399472627671343541861 := by
  unfold tailWord_494272
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013790432672216891046535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12018387243562955854728713 9013790432672216891046535)
  ·
    refine ⟨13520685649008325336569803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9013790432672216891046535 13520685649008325336569803)
    ·
      refine ⟨20281028473512488004854705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13520685649008325336569803 20281028473512488004854705)
      ·
        refine ⟨15210771355134366003641029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20281028473512488004854705 15210771355134366003641029)
        ·
          refine ⟨2852019629087693625682693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15210771355134366003641029 2852019629087693625682693)
          ·
            refine ⟨534753680453942554815505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2852019629087693625682693 534753680453942554815505)
            ·
              refine ⟨401065260340456916111629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534753680453942554815505 401065260340456916111629)
              ·
                refine ⟨150399472627671343541861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401065260340456916111629 150399472627671343541861)
                ·
                  rfl

theorem cell19_494272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_494272 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494272 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494272 prefixEnd_494272 := by exact prefixLift 494272
  have htrace : WordTrace (prefixWord ++ tailWord_494272) baseStart_494272 baseEnd_494272 := by
    simpa [prefixWord, tailWord_494272, baseEnd_494272] using wordTrace_append hprefix tailTrace_494272
  have hstable : (prefixWord ++ tailWord_494272).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494272).length < 2 ^ (prefixWord ++ tailWord_494272).sum := by decide
  have hdescent : baseEnd_494272 < baseStart_494272 := by decide
  rcases family_descends (prefixWord ++ tailWord_494272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494295 : List Nat := [1, 1, 3, 2, 1, 4, 7]
def baseStart_494295 : Nat := 118140960795 + 494295 * 2 ^ 59
def prefixEnd_494295 : Nat := 4983230072969 + 3 ^ 40 * 494295 * 2
def baseEnd_494295 : Nat := 50135490392938035010229

theorem tailTrace_494295 : CollatzResearch.WordTrace tailWord_494295 prefixEnd_494295 50135490392938035010229 := by
  unfold tailWord_494295
  simp only [CollatzResearch.WordTrace]
  refine ⟨18028419744261108710180339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12018946496174072473453559 18028419744261108710180339)
  ·
    refine ⟨27042629616391663065270509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18028419744261108710180339 27042629616391663065270509)
    ·
      refine ⟨10140986106146873649476441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27042629616391663065270509 10140986106146873649476441)
      ·
        refine ⟨7605739579610155237107331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10140986106146873649476441 7605739579610155237107331)
        ·
          refine ⟨11408609369415232855660997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7605739579610155237107331 11408609369415232855660997)
          ·
            refine ⟨2139114256765356160436437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11408609369415232855660997 2139114256765356160436437)
            ·
              refine ⟨50135490392938035010229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2139114256765356160436437 50135490392938035010229)
              ·
                rfl

theorem cell19_494295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_494295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494295 prefixEnd_494295 := by exact prefixLift 494295
  have htrace : WordTrace (prefixWord ++ tailWord_494295) baseStart_494295 baseEnd_494295 := by
    simpa [prefixWord, tailWord_494295, baseEnd_494295] using wordTrace_append hprefix tailTrace_494295
  have hstable : (prefixWord ++ tailWord_494295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494295).length < 2 ^ (prefixWord ++ tailWord_494295).sum := by decide
  have hdescent : baseEnd_494295 < baseStart_494295 := by decide
  rcases family_descends (prefixWord ++ tailWord_494295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494333 : List Nat := [1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_494333 : Nat := 118140960795 + 494333 * 2 ^ 59
def prefixEnd_494333 : Nat := 4983230072969 + 3 ^ 40 * 494333 * 2
def baseEnd_494333 : Nat := 150418034002441276186139

theorem tailTrace_494333 : CollatzResearch.WordTrace tailWord_494333 prefixEnd_494333 150418034002441276186139 := by
  unfold tailWord_494333
  simp only [CollatzResearch.WordTrace]
  refine ⟨18029805718123441200063653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12019870478748960800042435 18029805718123441200063653)
  ·
    refine ⟨3380588572148145225011935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18029805718123441200063653 3380588572148145225011935)
    ·
      refine ⟨5070882858222217837517903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3380588572148145225011935 5070882858222217837517903)
      ·
        refine ⟨7606324287333326756276855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5070882858222217837517903 7606324287333326756276855)
        ·
          refine ⟨11409486430999990134415283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7606324287333326756276855 11409486430999990134415283)
          ·
            refine ⟨17114229646499985201622925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11409486430999990134415283 17114229646499985201622925)
            ·
              refine ⟨6417836117437494450608597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17114229646499985201622925 6417836117437494450608597)
              ·
                refine ⟨150418034002441276186139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6417836117437494450608597 150418034002441276186139)
                ·
                  rfl

theorem cell19_494333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_494333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494333 prefixEnd_494333 := by exact prefixLift 494333
  have htrace : WordTrace (prefixWord ++ tailWord_494333) baseStart_494333 baseEnd_494333 := by
    simpa [prefixWord, tailWord_494333, baseEnd_494333] using wordTrace_append hprefix tailTrace_494333
  have hstable : (prefixWord ++ tailWord_494333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494333).length < 2 ^ (prefixWord ++ tailWord_494333).sum := by decide
  have hdescent : baseEnd_494333 < baseStart_494333 := by decide
  rcases family_descends (prefixWord ++ tailWord_494333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494365 : List Nat := [1, 4, 2, 4, 1, 2, 1, 4]
def baseStart_494365 : Nat := 118140960795 + 494365 * 2 ^ 59
def prefixEnd_494365 : Nat := 4983230072969 + 3 ^ 40 * 494365 * 2
def baseEnd_494365 : Nat := 150427771117074683474941

theorem tailTrace_494365 : CollatzResearch.WordTrace tailWord_494365 prefixEnd_494365 150427771117074683474941 := by
  unfold tailWord_494365
  simp only [CollatzResearch.WordTrace]
  refine ⟨18030972854007510665228549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12020648569338340443485699 18030972854007510665228549)
  ·
    refine ⟨3380807410126408249730353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18030972854007510665228549 3380807410126408249730353)
    ·
      refine ⟨2535605557594806187297765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3380807410126408249730353 2535605557594806187297765)
      ·
        refine ⟨475426042049026160118331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2535605557594806187297765 475426042049026160118331)
        ·
          refine ⟨713139063073539240177497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475426042049026160118331 713139063073539240177497)
          ·
            refine ⟨534854297305154430133123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713139063073539240177497 534854297305154430133123)
            ·
              refine ⟨802281445957731645199685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534854297305154430133123 802281445957731645199685)
              ·
                refine ⟨150427771117074683474941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 802281445957731645199685 150427771117074683474941)
                ·
                  rfl

theorem cell19_494365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 4].length) (baseStart_494365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494365 prefixEnd_494365 := by exact prefixLift 494365
  have htrace : WordTrace (prefixWord ++ tailWord_494365) baseStart_494365 baseEnd_494365 := by
    simpa [prefixWord, tailWord_494365, baseEnd_494365] using wordTrace_append hprefix tailTrace_494365
  have hstable : (prefixWord ++ tailWord_494365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494365).length < 2 ^ (prefixWord ++ tailWord_494365).sum := by decide
  have hdescent : baseEnd_494365 < baseStart_494365 := by decide
  rcases family_descends (prefixWord ++ tailWord_494365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494409 : List Nat := [1, 2, 1, 1, 2, 6, 6]
def baseStart_494409 : Nat := 118140960795 + 494409 * 2 ^ 59
def prefixEnd_494409 : Nat := 4983230072969 + 3 ^ 40 * 494409 * 2
def baseEnd_494409 : Nat := 50147053216565206165681

theorem tailTrace_494409 : CollatzResearch.WordTrace tailWord_494409 prefixEnd_494409 50147053216565206165681 := by
  unfold tailWord_494409
  simp only [CollatzResearch.WordTrace]
  refine ⟨18032577665848106179830281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12021718443898737453220187 18032577665848106179830281)
  ·
    refine ⟨13524433249386079634872711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18032577665848106179830281 13524433249386079634872711)
    ·
      refine ⟨20286649874079119452309067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13524433249386079634872711 20286649874079119452309067)
      ·
        refine ⟨30429974811118679178463601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20286649874079119452309067 30429974811118679178463601)
        ·
          refine ⟨22822481108339009383847701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30429974811118679178463601 22822481108339009383847701)
          ·
            refine ⟨1069803801953391064867861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22822481108339009383847701 1069803801953391064867861)
            ·
              refine ⟨50147053216565206165681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1069803801953391064867861 50147053216565206165681)
              ·
                rfl

theorem cell19_494409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_494409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494409 prefixEnd_494409 := by exact prefixLift 494409
  have htrace : WordTrace (prefixWord ++ tailWord_494409) baseStart_494409 baseEnd_494409 := by
    simpa [prefixWord, tailWord_494409, baseEnd_494409] using wordTrace_append hprefix tailTrace_494409
  have hstable : (prefixWord ++ tailWord_494409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494409).length < 2 ^ (prefixWord ++ tailWord_494409).sum := by decide
  have hdescent : baseEnd_494409 < baseStart_494409 := by decide
  rcases family_descends (prefixWord ++ tailWord_494409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494485 : List Nat := [1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_494485 : Nat := 118140960795 + 494485 * 2 ^ 59
def prefixEnd_494485 : Nat := 4983230072969 + 3 ^ 40 * 494485 * 2
def baseEnd_494485 : Nat := 150464285296949960807947

theorem tailTrace_494485 : CollatzResearch.WordTrace tailWord_494485 prefixEnd_494485 150464285296949960807947 := by
  unfold tailWord_494485
  simp only [CollatzResearch.WordTrace]
  refine ⟨18035349613572771159596909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12023566409048514106397939 18035349613572771159596909)
  ·
    refine ⟨6763256105089789184848841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18035349613572771159596909 6763256105089789184848841)
    ·
      refine ⟨5072442078817341888636631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6763256105089789184848841 5072442078817341888636631)
      ·
        refine ⟨7608663118226012832954947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072442078817341888636631 7608663118226012832954947)
        ·
          refine ⟨11412994677339019249432421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7608663118226012832954947 11412994677339019249432421)
          ·
            refine ⟨2139936502001066109268579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11412994677339019249432421 2139936502001066109268579)
            ·
              refine ⟨3209904753001599163902869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139936502001066109268579 3209904753001599163902869)
              ·
                refine ⟨150464285296949960807947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3209904753001599163902869 150464285296949960807947)
                ·
                  rfl

theorem cell19_494485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_494485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494485 prefixEnd_494485 := by exact prefixLift 494485
  have htrace : WordTrace (prefixWord ++ tailWord_494485) baseStart_494485 baseEnd_494485 := by
    simpa [prefixWord, tailWord_494485, baseEnd_494485] using wordTrace_append hprefix tailTrace_494485
  have hstable : (prefixWord ++ tailWord_494485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494485).length < 2 ^ (prefixWord ++ tailWord_494485).sum := by decide
  have hdescent : baseEnd_494485 < baseStart_494485 := by decide
  rcases family_descends (prefixWord ++ tailWord_494485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494557 : List Nat := [1, 4, 3, 1, 2, 2, 3, 3]
def baseStart_494557 : Nat := 118140960795 + 494557 * 2 ^ 59
def prefixEnd_494557 : Nat := 4983230072969 + 3 ^ 40 * 494557 * 2
def baseEnd_494557 : Nat := 150486193804875127207751

theorem tailTrace_494557 : CollatzResearch.WordTrace tailWord_494557 prefixEnd_494557 150486193804875127207751 := by
  unfold tailWord_494557
  simp only [CollatzResearch.WordTrace]
  refine ⟨18037975669311927456217925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12025317112874618304145283 18037975669311927456217925)
  ·
    refine ⟨3382120437995986398040861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18037975669311927456217925 3382120437995986398040861)
    ·
      refine ⟨1268295164248494899265323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3382120437995986398040861 1268295164248494899265323)
      ·
        refine ⟨1902442746372742348897985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268295164248494899265323 1902442746372742348897985)
        ·
          refine ⟨1426832059779556761673489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1902442746372742348897985 1426832059779556761673489)
          ·
            refine ⟨1070124044834667571255117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1426832059779556761673489 1070124044834667571255117)
            ·
              refine ⟨401296516813000339220669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1070124044834667571255117 401296516813000339220669)
              ·
                refine ⟨150486193804875127207751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401296516813000339220669 150486193804875127207751)
                ·
                  rfl

theorem cell19_494557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 3].length) (baseStart_494557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494557 prefixEnd_494557 := by exact prefixLift 494557
  have htrace : WordTrace (prefixWord ++ tailWord_494557) baseStart_494557 baseEnd_494557 := by
    simpa [prefixWord, tailWord_494557, baseEnd_494557] using wordTrace_append hprefix tailTrace_494557
  have hstable : (prefixWord ++ tailWord_494557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494557).length < 2 ^ (prefixWord ++ tailWord_494557).sum := by decide
  have hdescent : baseEnd_494557 < baseStart_494557 := by decide
  rcases family_descends (prefixWord ++ tailWord_494557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494599 : List Nat := [1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_494599 : Nat := 118140960795 + 494599 * 2 ^ 59
def prefixEnd_494599 : Nat := 4983230072969 + 3 ^ 40 * 494599 * 2
def baseEnd_494599 : Nat := 150498973767831474274303

theorem tailTrace_494599 : CollatzResearch.WordTrace tailWord_494599 prefixEnd_494599 150498973767831474274303 := by
  unfold tailWord_494599
  simp only [CollatzResearch.WordTrace]
  refine ⟨18039507535159768629246851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12026338356773179086164567 18039507535159768629246851)
  ·
    refine ⟨27059261302739652943870277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18039507535159768629246851 27059261302739652943870277)
    ·
      refine ⟨5073611494263684926975677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27059261302739652943870277 5073611494263684926975677)
      ·
        refine ⟨1902604310348881847615879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5073611494263684926975677 1902604310348881847615879)
        ·
          refine ⟨2853906465523322771423819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902604310348881847615879 2853906465523322771423819)
          ·
            refine ⟨4280859698284984157135729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853906465523322771423819 4280859698284984157135729)
            ·
              refine ⟨3210644773713738117851797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4280859698284984157135729 3210644773713738117851797)
              ·
                refine ⟨150498973767831474274303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3210644773713738117851797 150498973767831474274303)
                ·
                  rfl

theorem cell19_494599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_494599 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494599 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494599 prefixEnd_494599 := by exact prefixLift 494599
  have htrace : WordTrace (prefixWord ++ tailWord_494599) baseStart_494599 baseEnd_494599 := by
    simpa [prefixWord, tailWord_494599, baseEnd_494599] using wordTrace_append hprefix tailTrace_494599
  have hstable : (prefixWord ++ tailWord_494599).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494599).length < 2 ^ (prefixWord ++ tailWord_494599).sum := by decide
  have hdescent : baseEnd_494599 < baseStart_494599 := by decide
  rcases family_descends (prefixWord ++ tailWord_494599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494616 : List Nat := [2, 1, 2, 3, 2, 2, 4, 3]
def baseStart_494616 : Nat := 118140960795 + 494616 * 2 ^ 59
def prefixEnd_494616 : Nat := 4983230072969 + 3 ^ 40 * 494616 * 2
def baseEnd_494616 : Nat := 150504146609980471896479

theorem tailTrace_494616 : CollatzResearch.WordTrace tailWord_494616 prefixEnd_494616 150504146609980471896479 := by
  unfold tailWord_494616
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020063788049090266307851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12026751717398787021743801 9020063788049090266307851)
  ·
    refine ⟨13530095682073635399461777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9020063788049090266307851 13530095682073635399461777)
    ·
      refine ⟨10147571761555226549596333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13530095682073635399461777 10147571761555226549596333)
      ·
        refine ⟨3805339410583209956098625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10147571761555226549596333 3805339410583209956098625)
        ·
          refine ⟨2854004557937407467073969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3805339410583209956098625 2854004557937407467073969)
          ·
            refine ⟨2140503418453055600305477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2854004557937407467073969 2140503418453055600305477)
            ·
              refine ⟨401344390959947925057277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2140503418453055600305477 401344390959947925057277)
              ·
                refine ⟨150504146609980471896479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401344390959947925057277 150504146609980471896479)
                ·
                  rfl

theorem cell19_494616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_494616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494616 prefixEnd_494616 := by exact prefixLift 494616
  have htrace : WordTrace (prefixWord ++ tailWord_494616) baseStart_494616 baseEnd_494616 := by
    simpa [prefixWord, tailWord_494616, baseEnd_494616] using wordTrace_append hprefix tailTrace_494616
  have hstable : (prefixWord ++ tailWord_494616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494616).length < 2 ^ (prefixWord ++ tailWord_494616).sum := by decide
  have hdescent : baseEnd_494616 < baseStart_494616 := by decide
  rcases family_descends (prefixWord ++ tailWord_494616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494618 : List Nat := [3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_494618 : Nat := 118140960795 + 494618 * 2 ^ 59
def prefixEnd_494618 : Nat := 4983230072969 + 3 ^ 40 * 494618 * 2
def baseEnd_494618 : Nat := 150504755179645059852029

theorem tailTrace_494618 : CollatzResearch.WordTrace tailWord_494618 prefixEnd_494618 150504755179645059852029 := by
  unfold tailWord_494618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510050130522733718547127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12026800348060623249459005 4510050130522733718547127)
  ·
    refine ⟨6765075195784100577820691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4510050130522733718547127 6765075195784100577820691)
    ·
      refine ⟨10147612793676150866731037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6765075195784100577820691 10147612793676150866731037)
      ·
        refine ⟨3805354797628556575024139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10147612793676150866731037 3805354797628556575024139)
        ·
          refine ⟨5708032196442834862536209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3805354797628556575024139 5708032196442834862536209)
          ·
            refine ⟨4281024147332126146902157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5708032196442834862536209 4281024147332126146902157)
            ·
              refine ⟨1605384055249547305088309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4281024147332126146902157 1605384055249547305088309)
              ·
                refine ⟨150504755179645059852029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1605384055249547305088309 150504755179645059852029)
                ·
                  rfl

theorem cell19_494618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_494618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494618 prefixEnd_494618 := by exact prefixLift 494618
  have htrace : WordTrace (prefixWord ++ tailWord_494618) baseStart_494618 baseEnd_494618 := by
    simpa [prefixWord, tailWord_494618, baseEnd_494618] using wordTrace_append hprefix tailTrace_494618
  have hstable : (prefixWord ++ tailWord_494618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494618).length < 2 ^ (prefixWord ++ tailWord_494618).sum := by decide
  have hdescent : baseEnd_494618 < baseStart_494618 := by decide
  rcases family_descends (prefixWord ++ tailWord_494618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494654 : List Nat := [4, 2, 1, 3, 1, 1, 1, 6]
def baseStart_494654 : Nat := 118140960795 + 494654 * 2 ^ 59
def prefixEnd_494654 : Nat := 4983230072969 + 3 ^ 40 * 494654 * 2
def baseEnd_494654 : Nat := 150515709433607643051931

theorem tailTrace_494654 : CollatzResearch.WordTrace tailWord_494654 prefixEnd_494654 150515709433607643051931 := by
  unfold tailWord_494654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2255189193745064127812377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12027675699973675348332677 2255189193745064127812377)
  ·
    refine ⟨1691391895308798095859283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2255189193745064127812377 1691391895308798095859283)
    ·
      refine ⟨2537087842963197143788925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691391895308798095859283 2537087842963197143788925)
      ·
        refine ⟨951407941111198928920847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2537087842963197143788925 951407941111198928920847)
        ·
          refine ⟨1427111911666798393381271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951407941111198928920847 1427111911666798393381271)
          ·
            refine ⟨2140667867500197590071907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427111911666798393381271 2140667867500197590071907)
            ·
              refine ⟨3211001801250296385107861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140667867500197590071907 3211001801250296385107861)
              ·
                refine ⟨150515709433607643051931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3211001801250296385107861 150515709433607643051931)
                ·
                  rfl

theorem cell19_494654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_494654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494654 prefixEnd_494654 := by exact prefixLift 494654
  have htrace : WordTrace (prefixWord ++ tailWord_494654) baseStart_494654 baseEnd_494654 := by
    simpa [prefixWord, tailWord_494654, baseEnd_494654] using wordTrace_append hprefix tailTrace_494654
  have hstable : (prefixWord ++ tailWord_494654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494654).length < 2 ^ (prefixWord ++ tailWord_494654).sum := by decide
  have hdescent : baseEnd_494654 < baseStart_494654 := by decide
  rcases family_descends (prefixWord ++ tailWord_494654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494656 : List Nat := [2, 1, 1, 2, 2, 3, 4, 4]
def baseStart_494656 : Nat := 118140960795 + 494656 * 2 ^ 59
def prefixEnd_494656 : Nat := 4983230072969 + 3 ^ 40 * 494656 * 2
def baseEnd_494656 : Nat := 150516318003272231007481

theorem tailTrace_494656 : CollatzResearch.WordTrace tailWord_494656 prefixEnd_494656 150516318003272231007481 := by
  unfold tailWord_494656
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020793247976633682035911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12027724330635511576047881 9020793247976633682035911)
  ·
    refine ⟨13531189871964950523053867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9020793247976633682035911 13531189871964950523053867)
    ·
      refine ⟨20296784807947425784580801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13531189871964950523053867 20296784807947425784580801)
      ·
        refine ⟨15222588605960569338435601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20296784807947425784580801 15222588605960569338435601)
        ·
          refine ⟨11416941454470427003826701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15222588605960569338435601 11416941454470427003826701)
          ·
            refine ⟨4281353045426410126435013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11416941454470427003826701 4281353045426410126435013)
            ·
              refine ⟨802753696017451898706565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4281353045426410126435013 802753696017451898706565)
              ·
                refine ⟨150516318003272231007481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 802753696017451898706565 150516318003272231007481)
                ·
                  rfl

theorem cell19_494656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_494656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494656 prefixEnd_494656 := by exact prefixLift 494656
  have htrace : WordTrace (prefixWord ++ tailWord_494656) baseStart_494656 baseEnd_494656 := by
    simpa [prefixWord, tailWord_494656, baseEnd_494656] using wordTrace_append hprefix tailTrace_494656
  have hstable : (prefixWord ++ tailWord_494656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494656).length < 2 ^ (prefixWord ++ tailWord_494656).sum := by decide
  have hdescent : baseEnd_494656 < baseStart_494656 := by decide
  rcases family_descends (prefixWord ++ tailWord_494656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494728 : List Nat := [2, 1, 3, 4, 2, 1, 3, 3]
def baseStart_494728 : Nat := 118140960795 + 494728 * 2 ^ 59
def prefixEnd_494728 : Nat := 4983230072969 + 3 ^ 40 * 494728 * 2
def baseEnd_494728 : Nat := 150538226511197397407285

theorem tailTrace_494728 : CollatzResearch.WordTrace tailWord_494728 prefixEnd_494728 150538226511197397407285 := by
  unfold tailWord_494728
  simp only [CollatzResearch.WordTrace]
  refine ⟨9022106275846211830346419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12029475034461615773795225 9022106275846211830346419)
  ·
    refine ⟨13533159413769317745519629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9022106275846211830346419 13533159413769317745519629)
    ·
      refine ⟨5074934780163494154569861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13533159413769317745519629 5074934780163494154569861)
      ·
        refine ⟨951550271280655153981849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5074934780163494154569861 951550271280655153981849)
        ·
          refine ⟨713662703460491365486387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951550271280655153981849 713662703460491365486387)
          ·
            refine ⟨1070494055190737048229581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713662703460491365486387 1070494055190737048229581)
            ·
              refine ⟨401435270696526393086093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1070494055190737048229581 401435270696526393086093)
              ·
                refine ⟨150538226511197397407285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401435270696526393086093 150538226511197397407285)
                ·
                  rfl

theorem cell19_494728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_494728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494728 prefixEnd_494728 := by exact prefixLift 494728
  have htrace : WordTrace (prefixWord ++ tailWord_494728) baseStart_494728 baseEnd_494728 := by
    simpa [prefixWord, tailWord_494728, baseEnd_494728] using wordTrace_append hprefix tailTrace_494728
  have hstable : (prefixWord ++ tailWord_494728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494728).length < 2 ^ (prefixWord ++ tailWord_494728).sum := by decide
  have hdescent : baseEnd_494728 < baseStart_494728 := by decide
  rcases family_descends (prefixWord ++ tailWord_494728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494730 : List Nat := [3, 1, 2, 3, 1, 1, 5, 3]
def baseStart_494730 : Nat := 118140960795 + 494730 * 2 ^ 59
def prefixEnd_494730 : Nat := 4983230072969 + 3 ^ 40 * 494730 * 2
def baseEnd_494730 : Nat := 150538835080861985362835

theorem tailTrace_494730 : CollatzResearch.WordTrace tailWord_494730 prefixEnd_494730 150538835080861985362835 := by
  unfold tailWord_494730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4511071374421294500566411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12029523665123452001510429 4511071374421294500566411)
  ·
    refine ⟨6766607061631941750849617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4511071374421294500566411 6766607061631941750849617)
    ·
      refine ⟨5074955296223956313137213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6766607061631941750849617 5074955296223956313137213)
      ·
        refine ⟨1903108236083983617426455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5074955296223956313137213 1903108236083983617426455)
        ·
          refine ⟨2854662354125975426139683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903108236083983617426455 2854662354125975426139683)
          ·
            refine ⟨4281993531188963139209525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854662354125975426139683 4281993531188963139209525)
            ·
              refine ⟨401436893548965294300893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4281993531188963139209525 401436893548965294300893)
              ·
                refine ⟨150538835080861985362835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401436893548965294300893 150538835080861985362835)
                ·
                  rfl

theorem cell19_494730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_494730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494730 prefixEnd_494730 := by exact prefixLift 494730
  have htrace : WordTrace (prefixWord ++ tailWord_494730) baseStart_494730 baseEnd_494730 := by
    simpa [prefixWord, tailWord_494730, baseEnd_494730] using wordTrace_append hprefix tailTrace_494730
  have hstable : (prefixWord ++ tailWord_494730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494730).length < 2 ^ (prefixWord ++ tailWord_494730).sum := by decide
  have hdescent : baseEnd_494730 < baseStart_494730 := by decide
  rcases family_descends (prefixWord ++ tailWord_494730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494785 : List Nat := [1, 2, 6, 1, 1, 1, 4, 3]
def baseStart_494785 : Nat := 118140960795 + 494785 * 2 ^ 59
def prefixEnd_494785 : Nat := 4983230072969 + 3 ^ 40 * 494785 * 2
def baseEnd_494785 : Nat := 150555570746638154140463

theorem tailTrace_494785 : CollatzResearch.WordTrace tailWord_494785 prefixEnd_494785 150555570746638154140463 := by
  unfold tailWord_494785
  simp only [CollatzResearch.WordTrace]
  refine ⟨18046291512485922395517809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12030861008323948263678539 18046291512485922395517809)
  ·
    refine ⟨13534718634364441796638357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18046291512485922395517809 13534718634364441796638357)
    ·
      refine ⟨634439935985833209217423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13534718634364441796638357 634439935985833209217423)
      ·
        refine ⟨951659903978749813826135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634439935985833209217423 951659903978749813826135)
        ·
          refine ⟨1427489855968124720739203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951659903978749813826135 1427489855968124720739203)
          ·
            refine ⟨2141234783952187081108805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427489855968124720739203 2141234783952187081108805)
            ·
              refine ⟨401481521991035077707901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2141234783952187081108805 401481521991035077707901)
              ·
                refine ⟨150555570746638154140463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401481521991035077707901 150555570746638154140463)
                ·
                  rfl

theorem cell19_494785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 3].length) (baseStart_494785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494785 prefixEnd_494785 := by exact prefixLift 494785
  have htrace : WordTrace (prefixWord ++ tailWord_494785) baseStart_494785 baseEnd_494785 := by
    simpa [prefixWord, tailWord_494785, baseEnd_494785] using wordTrace_append hprefix tailTrace_494785
  have hstable : (prefixWord ++ tailWord_494785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494785).length < 2 ^ (prefixWord ++ tailWord_494785).sum := by decide
  have hdescent : baseEnd_494785 < baseStart_494785 := by decide
  rcases family_descends (prefixWord ++ tailWord_494785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494804 : List Nat := [2, 4, 1, 4, 1, 2, 5]
def baseStart_494804 : Nat := 118140960795 + 494804 * 2 ^ 59
def prefixEnd_494804 : Nat := 4983230072969 + 3 ^ 40 * 494804 * 2
def baseEnd_494804 : Nat := 50187117386150579906063

theorem tailTrace_494804 : CollatzResearch.WordTrace tailWord_494804 prefixEnd_494804 50187117386150579906063 := by
  unfold tailWord_494804
  simp only [CollatzResearch.WordTrace]
  refine ⟨9023492249708544320229733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12031322999611392426972977 9023492249708544320229733)
  ·
    refine ⟨1691904796820352060043075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9023492249708544320229733 1691904796820352060043075)
    ·
      refine ⟨2537857195230528090064613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691904796820352060043075 2537857195230528090064613)
      ·
        refine ⟨475848224105724016887115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2537857195230528090064613 475848224105724016887115)
        ·
          refine ⟨713772336158586025330673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475848224105724016887115 713772336158586025330673)
          ·
            refine ⟨535329252118939518998005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713772336158586025330673 535329252118939518998005)
            ·
              refine ⟨50187117386150579906063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 535329252118939518998005 50187117386150579906063)
              ·
                rfl

theorem cell19_494804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 5].length) (baseStart_494804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494804 prefixEnd_494804 := by exact prefixLift 494804
  have htrace : WordTrace (prefixWord ++ tailWord_494804) baseStart_494804 baseEnd_494804 := by
    simpa [prefixWord, tailWord_494804, baseEnd_494804] using wordTrace_append hprefix tailTrace_494804
  have hstable : (prefixWord ++ tailWord_494804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494804).length < 2 ^ (prefixWord ++ tailWord_494804).sum := by decide
  have hdescent : baseEnd_494804 < baseStart_494804 := by decide
  rcases family_descends (prefixWord ++ tailWord_494804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494827 : List Nat := [1, 1, 1, 1, 2, 7, 2, 4]
def baseStart_494827 : Nat := 118140960795 + 494827 * 2 ^ 59
def prefixEnd_494827 : Nat := 4983230072969 + 3 ^ 40 * 494827 * 2
def baseEnd_494827 : Nat := 150568350709594501207015

theorem tailTrace_494827 : CollatzResearch.WordTrace tailWord_494827 prefixEnd_494827 150568350709594501207015 := by
  unfold tailWord_494827
  simp only [CollatzResearch.WordTrace]
  refine ⟨18047823378333763568546735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12031882252222509045697823 18047823378333763568546735)
  ·
    refine ⟨27071735067500645352820103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18047823378333763568546735 27071735067500645352820103)
    ·
      refine ⟨40607602601250968029230155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27071735067500645352820103 40607602601250968029230155)
      ·
        refine ⟨60911403901876452043845233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40607602601250968029230155 60911403901876452043845233)
        ·
          refine ⟨45683552926407339032883925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60911403901876452043845233 45683552926407339032883925)
          ·
            refine ⟨1070708271712672008583217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45683552926407339032883925 1070708271712672008583217)
            ·
              refine ⟨803031203784504006437413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070708271712672008583217 803031203784504006437413)
              ·
                refine ⟨150568350709594501207015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803031203784504006437413 150568350709594501207015)
                ·
                  rfl

theorem cell19_494827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_494827 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494827 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494827 prefixEnd_494827 := by exact prefixLift 494827
  have htrace : WordTrace (prefixWord ++ tailWord_494827) baseStart_494827 baseEnd_494827 := by
    simpa [prefixWord, tailWord_494827, baseEnd_494827] using wordTrace_append hprefix tailTrace_494827
  have hstable : (prefixWord ++ tailWord_494827).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494827).length < 2 ^ (prefixWord ++ tailWord_494827).sum := by decide
  have hdescent : baseEnd_494827 < baseStart_494827 := by decide
  rcases family_descends (prefixWord ++ tailWord_494827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494878 : List Nat := [4, 3, 2, 1, 2, 2, 1, 4]
def baseStart_494878 : Nat := 118140960795 + 494878 * 2 ^ 59
def prefixEnd_494878 : Nat := 4983230072969 + 3 ^ 40 * 494878 * 2
def baseEnd_494878 : Nat := 150583869236041494073543

theorem tailTrace_494878 : CollatzResearch.WordTrace tailWord_494878 prefixEnd_494878 150583869236041494073543 := by
  unfold tailWord_494878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256210437643624909831661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12033122334099332852435525 2256210437643624909831661)
  ·
    refine ⟨846078914116359341186873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2256210437643624909831661 846078914116359341186873)
    ·
      refine ⟨634559185587269505890155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 846078914116359341186873 634559185587269505890155)
      ·
        refine ⟨951838778380904258835233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634559185587269505890155 951838778380904258835233)
        ·
          refine ⟨713879083785678194126425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951838778380904258835233 713879083785678194126425)
          ·
            refine ⟨535409312839258645594819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713879083785678194126425 535409312839258645594819)
            ·
              refine ⟨803113969258887968392229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535409312839258645594819 803113969258887968392229)
              ·
                refine ⟨150583869236041494073543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803113969258887968392229 150583869236041494073543)
                ·
                  rfl

theorem cell19_494878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_494878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494878 prefixEnd_494878 := by exact prefixLift 494878
  have htrace : WordTrace (prefixWord ++ tailWord_494878) baseStart_494878 baseEnd_494878 := by
    simpa [prefixWord, tailWord_494878, baseEnd_494878] using wordTrace_append hprefix tailTrace_494878
  have hstable : (prefixWord ++ tailWord_494878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494878).length < 2 ^ (prefixWord ++ tailWord_494878).sum := by decide
  have hdescent : baseEnd_494878 < baseStart_494878 := by decide
  rcases family_descends (prefixWord ++ tailWord_494878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494880 : List Nat := [2, 1, 1, 5, 4, 1, 1, 4]
def baseStart_494880 : Nat := 118140960795 + 494880 * 2 ^ 59
def prefixEnd_494880 : Nat := 4983230072969 + 3 ^ 40 * 494880 * 2
def baseEnd_494880 : Nat := 150584477805706082029093

theorem tailTrace_494880 : CollatzResearch.WordTrace tailWord_494880 prefixEnd_494880 150584477805706082029093 := by
  unfold tailWord_494880
  simp only [CollatzResearch.WordTrace]
  refine ⟨9024878223570876810113047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12033170964761169080150729 9024878223570876810113047)
  ·
    refine ⟨13537317335356315215169571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9024878223570876810113047 13537317335356315215169571)
    ·
      refine ⟨20305976003034472822754357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13537317335356315215169571 20305976003034472822754357)
      ·
        refine ⟨1903685250284481827133221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20305976003034472822754357 1903685250284481827133221)
        ·
          refine ⟨356940984428340342587479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1903685250284481827133221 356940984428340342587479)
          ·
            refine ⟨535411476642510513881219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356940984428340342587479 535411476642510513881219)
            ·
              refine ⟨803117214963765770821829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535411476642510513881219 803117214963765770821829)
              ·
                refine ⟨150584477805706082029093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803117214963765770821829 150584477805706082029093)
                ·
                  rfl

theorem cell19_494880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_494880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494880 prefixEnd_494880 := by exact prefixLift 494880
  have htrace : WordTrace (prefixWord ++ tailWord_494880) baseStart_494880 baseEnd_494880 := by
    simpa [prefixWord, tailWord_494880, baseEnd_494880] using wordTrace_append hprefix tailTrace_494880
  have hstable : (prefixWord ++ tailWord_494880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494880).length < 2 ^ (prefixWord ++ tailWord_494880).sum := by decide
  have hdescent : baseEnd_494880 < baseStart_494880 := by decide
  rcases family_descends (prefixWord ++ tailWord_494880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494901 : List Nat := [1, 3, 3, 1, 2, 3, 3, 3]
def baseStart_494901 : Nat := 118140960795 + 494901 * 2 ^ 59
def prefixEnd_494901 : Nat := 4983230072969 + 3 ^ 40 * 494901 * 2
def baseEnd_494901 : Nat := 150590867787184255562369

theorem tailTrace_494901 : CollatzResearch.WordTrace tailWord_494901 prefixEnd_494901 150590867787184255562369 := by
  unfold tailWord_494901
  simp only [CollatzResearch.WordTrace]
  refine ⟨18050522380065674206740557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12033681586710449471160371 18050522380065674206740557)
  ·
    refine ⟨6768945892524627827527709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18050522380065674206740557 6768945892524627827527709)
    ·
      refine ⟨2538354709696735435322891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6768945892524627827527709 2538354709696735435322891)
      ·
        refine ⟨3807532064545103152984337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538354709696735435322891 3807532064545103152984337)
        ·
          refine ⟨2855649048408827364738253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3807532064545103152984337 2855649048408827364738253)
          ·
            refine ⟨1070868393153310261776845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2855649048408827364738253 1070868393153310261776845)
            ·
              refine ⟨401575647432491348166317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1070868393153310261776845 401575647432491348166317)
              ·
                refine ⟨150590867787184255562369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401575647432491348166317 150590867787184255562369)
                ·
                  rfl

theorem cell19_494901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 3].length) (baseStart_494901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494901 prefixEnd_494901 := by exact prefixLift 494901
  have htrace : WordTrace (prefixWord ++ tailWord_494901) baseStart_494901 baseEnd_494901 := by
    simpa [prefixWord, tailWord_494901, baseEnd_494901] using wordTrace_append hprefix tailTrace_494901
  have hstable : (prefixWord ++ tailWord_494901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494901).length < 2 ^ (prefixWord ++ tailWord_494901).sum := by decide
  have hdescent : baseEnd_494901 < baseStart_494901 := by decide
  rcases family_descends (prefixWord ++ tailWord_494901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494943 : List Nat := [1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_494943 : Nat := 118140960795 + 494943 * 2 ^ 59
def prefixEnd_494943 : Nat := 4983230072969 + 3 ^ 40 * 494943 * 2
def baseEnd_494943 : Nat := 150603647750140602628921

theorem tailTrace_494943 : CollatzResearch.WordTrace tailWord_494943 prefixEnd_494943 150603647750140602628921 := by
  unfold tailWord_494943
  simp only [CollatzResearch.WordTrace]
  refine ⟨18052054245913515379769483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12034702830609010253179655 18052054245913515379769483)
  ·
    refine ⟨27078081368870273069654225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18052054245913515379769483 27078081368870273069654225)
    ·
      refine ⟨20308561026652704802240669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27078081368870273069654225 20308561026652704802240669)
      ·
        refine ⟨7615710384994764300840251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20308561026652704802240669 7615710384994764300840251)
        ·
          refine ⟨11423565577492146451260377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7615710384994764300840251 11423565577492146451260377)
          ·
            refine ⟨8567674183119109838445283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11423565577492146451260377 8567674183119109838445283)
            ·
              refine ⟨12851511274678664757667925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8567674183119109838445283 12851511274678664757667925)
              ·
                refine ⟨150603647750140602628921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12851511274678664757667925 150603647750140602628921)
                ·
                  rfl

theorem cell19_494943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_494943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494943 prefixEnd_494943 := by exact prefixLift 494943
  have htrace : WordTrace (prefixWord ++ tailWord_494943) baseStart_494943 baseEnd_494943 := by
    simpa [prefixWord, tailWord_494943, baseEnd_494943] using wordTrace_append hprefix tailTrace_494943
  have hstable : (prefixWord ++ tailWord_494943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494943).length < 2 ^ (prefixWord ++ tailWord_494943).sum := by decide
  have hdescent : baseEnd_494943 < baseStart_494943 := by decide
  rcases family_descends (prefixWord ++ tailWord_494943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494954 : List Nat := [3, 1, 3, 3, 3, 1, 2, 3]
def baseStart_494954 : Nat := 118140960795 + 494954 * 2 ^ 59
def prefixEnd_494954 : Nat := 4983230072969 + 3 ^ 40 * 494954 * 2
def baseEnd_494954 : Nat := 150606994883295836384447

theorem tailTrace_494954 : CollatzResearch.WordTrace tailWord_494954 prefixEnd_494954 150606994883295836384447 := by
  unfold tailWord_494954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513113862218416064604979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12034970299249109505613277 4513113862218416064604979)
  ·
    refine ⟨6769670793327624096907469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4513113862218416064604979 6769670793327624096907469)
    ·
      refine ⟨2538626547497859036340301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6769670793327624096907469 2538626547497859036340301)
      ·
        refine ⟨951984955311697138627613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2538626547497859036340301 951984955311697138627613)
        ·
          refine ⟨356994358241886426985355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 951984955311697138627613 356994358241886426985355)
          ·
            refine ⟨535491537362829640478033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356994358241886426985355 535491537362829640478033)
            ·
              refine ⟨401618653022122230358525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535491537362829640478033 401618653022122230358525)
              ·
                refine ⟨150606994883295836384447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401618653022122230358525 150606994883295836384447)
                ·
                  rfl

theorem cell19_494954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_494954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494954 prefixEnd_494954 := by exact prefixLift 494954
  have htrace : WordTrace (prefixWord ++ tailWord_494954) baseStart_494954 baseEnd_494954 := by
    simpa [prefixWord, tailWord_494954, baseEnd_494954] using wordTrace_append hprefix tailTrace_494954
  have hstable : (prefixWord ++ tailWord_494954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494954).length < 2 ^ (prefixWord ++ tailWord_494954).sum := by decide
  have hdescent : baseEnd_494954 < baseStart_494954 := by decide
  rcases family_descends (prefixWord ++ tailWord_494954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494977 : List Nat := [1, 2, 4, 3, 2, 2, 5]
def baseStart_494977 : Nat := 118140960795 + 494977 * 2 ^ 59
def prefixEnd_494977 : Nat := 4983230072969 + 3 ^ 40 * 494977 * 2
def baseEnd_494977 : Nat := 50204664478146199291091

theorem tailTrace_494977 : CollatzResearch.WordTrace tailWord_494977 prefixEnd_494977 50204664478146199291091 := by
  unfold tailWord_494977
  simp only [CollatzResearch.WordTrace]
  refine ⟨18053294327790339186507185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12035529551860226124338123 18053294327790339186507185)
  ·
    refine ⟨13539970745842754389880389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18053294327790339186507185 13539970745842754389880389)
    ·
      refine ⟨2538744514845516448102573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13539970745842754389880389 2538744514845516448102573)
      ·
        refine ⟨952029193067068668038465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2538744514845516448102573 952029193067068668038465)
        ·
          refine ⟨714021894800301501028849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952029193067068668038465 714021894800301501028849)
          ·
            refine ⟨535516421100226125771637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714021894800301501028849 535516421100226125771637)
            ·
              refine ⟨50204664478146199291091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 535516421100226125771637 50204664478146199291091)
              ·
                rfl

theorem cell19_494977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_494977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494977 prefixEnd_494977 := by exact prefixLift 494977
  have htrace : WordTrace (prefixWord ++ tailWord_494977) baseStart_494977 baseEnd_494977 := by
    simpa [prefixWord, tailWord_494977, baseEnd_494977] using wordTrace_append hprefix tailTrace_494977
  have hstable : (prefixWord ++ tailWord_494977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494977).length < 2 ^ (prefixWord ++ tailWord_494977).sum := by decide
  have hdescent : baseEnd_494977 < baseStart_494977 := by decide
  rcases family_descends (prefixWord ++ tailWord_494977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494979 : List Nat := [1, 1, 1, 3, 5, 3, 5]
def baseStart_494979 : Nat := 118140960795 + 494979 * 2 ^ 59
def prefixEnd_494979 : Nat := 4983230072969 + 3 ^ 40 * 494979 * 2
def baseEnd_494979 : Nat := 50204867334701061942941

theorem tailTrace_494979 : CollatzResearch.WordTrace tailWord_494979 prefixEnd_494979 50204867334701061942941 := by
  unfold tailWord_494979
  simp only [CollatzResearch.WordTrace]
  refine ⟨18053367273783093528079991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12035578182522062352053327 18053367273783093528079991)
  ·
    refine ⟨27080050910674640292119987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18053367273783093528079991 27080050910674640292119987)
    ·
      refine ⟨40620076366011960438179981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27080050910674640292119987 40620076366011960438179981)
      ·
        refine ⟨15232528637254485164317493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40620076366011960438179981 15232528637254485164317493)
        ·
          refine ⟨1428049559742607984154765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15232528637254485164317493 1428049559742607984154765)
          ·
            refine ⟨535518584903477994058037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1428049559742607984154765 535518584903477994058037)
            ·
              refine ⟨50204867334701061942941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 535518584903477994058037 50204867334701061942941)
              ·
                rfl

theorem cell19_494979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_494979 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494979 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494979 prefixEnd_494979 := by exact prefixLift 494979
  have htrace : WordTrace (prefixWord ++ tailWord_494979) baseStart_494979 baseEnd_494979 := by
    simpa [prefixWord, tailWord_494979, baseEnd_494979] using wordTrace_append hprefix tailTrace_494979
  have hstable : (prefixWord ++ tailWord_494979).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494979).length < 2 ^ (prefixWord ++ tailWord_494979).sum := by decide
  have hdescent : baseEnd_494979 < baseStart_494979 := by decide
  rcases family_descends (prefixWord ++ tailWord_494979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494981 : List Nat := [1, 3, 1, 1, 3, 1, 9]
def baseStart_494981 : Nat := 118140960795 + 494981 * 2 ^ 59
def prefixEnd_494981 : Nat := 4983230072969 + 3 ^ 40 * 494981 * 2
def baseEnd_494981 : Nat := 50205070191255924594791

theorem tailTrace_494981 : CollatzResearch.WordTrace tailWord_494981 prefixEnd_494981 50205070191255924594791 := by
  unfold tailWord_494981
  simp only [CollatzResearch.WordTrace]
  refine ⟨18053440219775847869652797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12035626813183898579768531 18053440219775847869652797)
  ·
    refine ⟨6770040082415942951119799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18053440219775847869652797 6770040082415942951119799)
    ·
      refine ⟨10155060123623914426679699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6770040082415942951119799 10155060123623914426679699)
      ·
        refine ⟨15232590185435871640019549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10155060123623914426679699 15232590185435871640019549)
        ·
          refine ⟨5712221319538451865007331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15232590185435871640019549 5712221319538451865007331)
          ·
            refine ⟨8568331979307677797510997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712221319538451865007331 8568331979307677797510997)
            ·
              refine ⟨50205070191255924594791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8568331979307677797510997 50205070191255924594791)
              ·
                rfl

theorem cell19_494981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_494981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494981 prefixEnd_494981 := by exact prefixLift 494981
  have htrace : WordTrace (prefixWord ++ tailWord_494981) baseStart_494981 baseEnd_494981 := by
    simpa [prefixWord, tailWord_494981, baseEnd_494981] using wordTrace_append hprefix tailTrace_494981
  have hstable : (prefixWord ++ tailWord_494981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494981).length < 2 ^ (prefixWord ++ tailWord_494981).sum := by decide
  have hdescent : baseEnd_494981 < baseStart_494981 := by decide
  rcases family_descends (prefixWord ++ tailWord_494981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494994 : List Nat := [3, 2, 3, 3, 1, 1, 2, 4]
def baseStart_494994 : Nat := 118140960795 + 494994 * 2 ^ 59
def prefixEnd_494994 : Nat := 4983230072969 + 3 ^ 40 * 494994 * 2
def baseEnd_494994 : Nat := 150619166276587595495449

theorem tailTrace_494994 : CollatzResearch.WordTrace tailWord_494994 prefixEnd_494994 150619166276587595495449 := by
  unfold tailWord_494994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513478592182187772469009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12035942912485834059917357 4513478592182187772469009)
  ·
    refine ⟨3385108944136640829351757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4513478592182187772469009 3385108944136640829351757)
    ·
      refine ⟨1269415854051240311006909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3385108944136640829351757 1269415854051240311006909)
      ·
        refine ⟨476030945269215116627591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1269415854051240311006909 476030945269215116627591)
        ·
          refine ⟨714046417903822674941387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476030945269215116627591 714046417903822674941387)
          ·
            refine ⟨1071069626855734012412081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714046417903822674941387 1071069626855734012412081)
            ·
              refine ⟨803302220141800509309061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071069626855734012412081 803302220141800509309061)
              ·
                refine ⟨150619166276587595495449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803302220141800509309061 150619166276587595495449)
                ·
                  rfl

theorem cell19_494994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_494994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494994 prefixEnd_494994 := by exact prefixLift 494994
  have htrace : WordTrace (prefixWord ++ tailWord_494994) baseStart_494994 baseEnd_494994 := by
    simpa [prefixWord, tailWord_494994, baseEnd_494994] using wordTrace_append hprefix tailTrace_494994
  have hstable : (prefixWord ++ tailWord_494994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494994).length < 2 ^ (prefixWord ++ tailWord_494994).sum := by decide
  have hdescent : baseEnd_494994 < baseStart_494994 := by decide
  rcases family_descends (prefixWord ++ tailWord_494994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494996 : List Nat := [2, 4, 2, 1, 2, 2, 2, 4]
def baseStart_494996 : Nat := 118140960795 + 494996 * 2 ^ 59
def prefixEnd_494996 : Nat := 4983230072969 + 3 ^ 40 * 494996 * 2
def baseEnd_494996 : Nat := 150619774846252183450999

theorem tailTrace_494996 : CollatzResearch.WordTrace tailWord_494996 prefixEnd_494996 150619774846252183450999 := by
  unfold tailWord_494996
  simp only [CollatzResearch.WordTrace]
  refine ⟨9026993657360752715724421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12035991543147670287632561 9026993657360752715724421)
  ·
    refine ⟨1692561310755141134198329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9026993657360752715724421 1692561310755141134198329)
    ·
      refine ⟨1269420983066355850648747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1692561310755141134198329 1269420983066355850648747)
      ·
        refine ⟨1904131474599533775973121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269420983066355850648747 1904131474599533775973121)
        ·
          refine ⟨1428098605949650331979841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1904131474599533775973121 1428098605949650331979841)
          ·
            refine ⟨1071073954462237748984881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1428098605949650331979841 1071073954462237748984881)
            ·
              refine ⟨803305465846678311738661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071073954462237748984881 803305465846678311738661)
              ·
                refine ⟨150619774846252183450999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803305465846678311738661 150619774846252183450999)
                ·
                  rfl

theorem cell19_494996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_494996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_494996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_494996 prefixEnd_494996 := by exact prefixLift 494996
  have htrace : WordTrace (prefixWord ++ tailWord_494996) baseStart_494996 baseEnd_494996 := by
    simpa [prefixWord, tailWord_494996, baseEnd_494996] using wordTrace_append hprefix tailTrace_494996
  have hstable : (prefixWord ++ tailWord_494996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494996).length < 2 ^ (prefixWord ++ tailWord_494996).sum := by decide
  have hdescent : baseEnd_494996 < baseStart_494996 := by decide
  rcases family_descends (prefixWord ++ tailWord_494996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495036 : List Nat := [2, 2, 2, 4, 2, 7]
def baseStart_495036 : Nat := 118140960795 + 495036 * 2 ^ 59
def prefixEnd_495036 : Nat := 4983230072969 + 3 ^ 40 * 495036 * 2
def baseEnd_495036 : Nat := 16736882915504882506889

theorem tailTrace_495036 : CollatzResearch.WordTrace tailWord_495036 prefixEnd_495036 16736882915504882506889 := by
  unfold tailWord_495036
  simp only [CollatzResearch.WordTrace]
  refine ⟨9027723117288296131452481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12036964156384394841936641 9027723117288296131452481)
  ·
    refine ⟨6770792337966222098589361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9027723117288296131452481 6770792337966222098589361)
    ·
      refine ⟨5078094253474666573942021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6770792337966222098589361 5078094253474666573942021)
      ·
        refine ⟨952142672526499982614129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5078094253474666573942021 952142672526499982614129)
        ·
          refine ⟨714107004394874986960597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952142672526499982614129 714107004394874986960597)
          ·
            refine ⟨16736882915504882506889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 714107004394874986960597 16736882915504882506889)
            ·
              rfl

theorem cell19_495036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 7].length) (baseStart_495036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495036 prefixEnd_495036 := by exact prefixLift 495036
  have htrace : WordTrace (prefixWord ++ tailWord_495036) baseStart_495036 baseEnd_495036 := by
    simpa [prefixWord, tailWord_495036, baseEnd_495036] using wordTrace_append hprefix tailTrace_495036
  have hstable : (prefixWord ++ tailWord_495036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495036).length < 2 ^ (prefixWord ++ tailWord_495036).sum := by decide
  have hdescent : baseEnd_495036 < baseStart_495036 := by decide
  rcases family_descends (prefixWord ++ tailWord_495036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495076 : List Nat := [2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_495076 : Nat := 118140960795 + 495076 * 2 ^ 59
def prefixEnd_495076 : Nat := 4983230072969 + 3 ^ 40 * 495076 * 2
def baseEnd_495076 : Nat := 150644117632835701673003

theorem tailTrace_495076 : CollatzResearch.WordTrace tailWord_495076 prefixEnd_495076 150644117632835701673003 := by
  unfold tailWord_495076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9028452577215839547180541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12037936769621119396240721 9028452577215839547180541)
  ·
    refine ⟨3385669716455939830192703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9028452577215839547180541 3385669716455939830192703)
    ·
      refine ⟨5078504574683909745289055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3385669716455939830192703 5078504574683909745289055)
      ·
        refine ⟨7617756862025864617933583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078504574683909745289055 7617756862025864617933583)
        ·
          refine ⟨11426635293038796926900375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617756862025864617933583 11426635293038796926900375)
          ·
            refine ⟨17139952939558195390350563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11426635293038796926900375 17139952939558195390350563)
            ·
              refine ⟨25709929409337293085525845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17139952939558195390350563 25709929409337293085525845)
              ·
                refine ⟨150644117632835701673003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25709929409337293085525845 150644117632835701673003)
                ·
                  rfl

theorem cell19_495076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_495076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495076 prefixEnd_495076 := by exact prefixLift 495076
  have htrace : WordTrace (prefixWord ++ tailWord_495076) baseStart_495076 baseEnd_495076 := by
    simpa [prefixWord, tailWord_495076, baseEnd_495076] using wordTrace_append hprefix tailTrace_495076
  have hstable : (prefixWord ++ tailWord_495076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495076).length < 2 ^ (prefixWord ++ tailWord_495076).sum := by decide
  have hdescent : baseEnd_495076 < baseStart_495076 := by decide
  rcases family_descends (prefixWord ++ tailWord_495076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495150 : List Nat := [4, 1, 3, 1, 2, 1, 7]
def baseStart_495150 : Nat := 118140960795 + 495150 * 2 ^ 59
def prefixEnd_495150 : Nat := 4983230072969 + 3 ^ 40 * 495150 * 2
def baseEnd_495150 : Nat := 50222211570141818676119

theorem tailTrace_495150 : CollatzResearch.WordTrace tailWord_495150 prefixEnd_495150 50222211570141818676119 := by
  unfold tailWord_495150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2257450519520448716569363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12039736104109059821703269 2257450519520448716569363)
  ·
    refine ⟨3386175779280673074854045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2257450519520448716569363 3386175779280673074854045)
    ·
      refine ⟨1269815917230252403070267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3386175779280673074854045 1269815917230252403070267)
      ·
        refine ⟨1904723875845378604605401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269815917230252403070267 1904723875845378604605401)
        ·
          refine ⟨1428542906884033953454051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1904723875845378604605401 1428542906884033953454051)
          ·
            refine ⟨2142814360326050930181077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428542906884033953454051 2142814360326050930181077)
            ·
              refine ⟨50222211570141818676119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2142814360326050930181077 50222211570141818676119)
              ·
                rfl

theorem cell19_495150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_495150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495150 prefixEnd_495150 := by exact prefixLift 495150
  have htrace : WordTrace (prefixWord ++ tailWord_495150) baseStart_495150 baseEnd_495150 := by
    simpa [prefixWord, tailWord_495150, baseEnd_495150] using wordTrace_append hprefix tailTrace_495150
  have hstable : (prefixWord ++ tailWord_495150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495150).length < 2 ^ (prefixWord ++ tailWord_495150).sum := by decide
  have hdescent : baseEnd_495150 < baseStart_495150 := by decide
  rcases family_descends (prefixWord ++ tailWord_495150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495169 : List Nat := [1, 2, 5, 1, 1, 1, 4, 4]
def baseStart_495169 : Nat := 118140960795 + 495169 * 2 ^ 59
def prefixEnd_495169 : Nat := 4983230072969 + 3 ^ 40 * 495169 * 2
def baseEnd_495169 : Nat := 150672416122239041606083

theorem tailTrace_495169 : CollatzResearch.WordTrace tailWord_495169 prefixEnd_495169 150672416122239041606083 := by
  unfold tailWord_495169
  simp only [CollatzResearch.WordTrace]
  refine ⟨18060297143094755977496561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12040198095396503984997707 18060297143094755977496561)
  ·
    refine ⟨13545222857321066983122421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18060297143094755977496561 13545222857321066983122421)
    ·
      refine ⟨1269864642873850029667727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13545222857321066983122421 1269864642873850029667727)
      ·
        refine ⟨1904796964310775044501591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269864642873850029667727 1904796964310775044501591)
        ·
          refine ⟨2857195446466162566752387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904796964310775044501591 2857195446466162566752387)
          ·
            refine ⟨4285793169699243850128581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857195446466162566752387 4285793169699243850128581)
            ·
              refine ⟨803586219318608221899109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4285793169699243850128581 803586219318608221899109)
              ·
                refine ⟨150672416122239041606083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803586219318608221899109 150672416122239041606083)
                ·
                  rfl

theorem cell19_495169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_495169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495169 prefixEnd_495169 := by exact prefixLift 495169
  have htrace : WordTrace (prefixWord ++ tailWord_495169) baseStart_495169 baseEnd_495169 := by
    simpa [prefixWord, tailWord_495169, baseEnd_495169] using wordTrace_append hprefix tailTrace_495169
  have hstable : (prefixWord ++ tailWord_495169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495169).length < 2 ^ (prefixWord ++ tailWord_495169).sum := by decide
  have hdescent : baseEnd_495169 < baseStart_495169 := by decide
  rcases family_descends (prefixWord ++ tailWord_495169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495304 : List Nat := [2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_495304 : Nat := 118140960795 + 495304 * 2 ^ 59
def prefixEnd_495304 : Nat := 4983230072969 + 3 ^ 40 * 495304 * 2
def baseEnd_495304 : Nat := 150713494574598728605715

theorem tailTrace_495304 : CollatzResearch.WordTrace tailWord_495304 prefixEnd_495304 150713494574598728605715 := by
  unfold tailWord_495304
  simp only [CollatzResearch.WordTrace]
  refine ⟨9032610498802837016830483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12043480665070449355773977 9032610498802837016830483)
  ·
    refine ⟨13548915748204255525245725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9032610498802837016830483 13548915748204255525245725)
    ·
      refine ⟨5080843405576595821967147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13548915748204255525245725 5080843405576595821967147)
      ·
        refine ⟨7621265108364893732950721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5080843405576595821967147 7621265108364893732950721)
        ·
          refine ⟨5715948831273670299713041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7621265108364893732950721 5715948831273670299713041)
          ·
            refine ⟨4286961623455252724784781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5715948831273670299713041 4286961623455252724784781)
            ·
              refine ⟨1607610608795719771794293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4286961623455252724784781 1607610608795719771794293)
              ·
                refine ⟨150713494574598728605715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1607610608795719771794293 150713494574598728605715)
                ·
                  rfl

theorem cell19_495304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_495304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495304 prefixEnd_495304 := by exact prefixLift 495304
  have htrace : WordTrace (prefixWord ++ tailWord_495304) baseStart_495304 baseEnd_495304 := by
    simpa [prefixWord, tailWord_495304, baseEnd_495304] using wordTrace_append hprefix tailTrace_495304
  have hstable : (prefixWord ++ tailWord_495304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495304).length < 2 ^ (prefixWord ++ tailWord_495304).sum := by decide
  have hdescent : baseEnd_495304 < baseStart_495304 := by decide
  rcases family_descends (prefixWord ++ tailWord_495304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495361 : List Nat := [1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_495361 : Nat := 118140960795 + 495361 * 2 ^ 59
def prefixEnd_495361 : Nat := 4983230072969 + 3 ^ 40 * 495361 * 2
def baseEnd_495361 : Nat := 150730838810039485338893

theorem tailTrace_495361 : CollatzResearch.WordTrace tailWord_495361 prefixEnd_495361 150730838810039485338893 := by
  unfold tailWord_495361
  simp only [CollatzResearch.WordTrace]
  refine ⟨18067299958399172768485937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12044866638932781845657291 18067299958399172768485937)
  ·
    refine ⟨13550474968799379576364453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18067299958399172768485937 13550474968799379576364453)
    ·
      refine ⟨2540714056649883670568335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13550474968799379576364453 2540714056649883670568335)
      ·
        refine ⟨3811071084974825505852503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540714056649883670568335 3811071084974825505852503)
        ·
          refine ⟨5716606627462238258778755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3811071084974825505852503 5716606627462238258778755)
          ·
            refine ⟨8574909941193357388168133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5716606627462238258778755 8574909941193357388168133)
            ·
              refine ⟨1607795613973754510281525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8574909941193357388168133 1607795613973754510281525)
              ·
                refine ⟨150730838810039485338893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1607795613973754510281525 150730838810039485338893)
                ·
                  rfl

theorem cell19_495361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_495361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495361 prefixEnd_495361 := by exact prefixLift 495361
  have htrace : WordTrace (prefixWord ++ tailWord_495361) baseStart_495361 baseEnd_495361 := by
    simpa [prefixWord, tailWord_495361, baseEnd_495361] using wordTrace_append hprefix tailTrace_495361
  have hstable : (prefixWord ++ tailWord_495361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495361).length < 2 ^ (prefixWord ++ tailWord_495361).sum := by decide
  have hdescent : baseEnd_495361 < baseStart_495361 := by decide
  rcases family_descends (prefixWord ++ tailWord_495361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495378 : List Nat := [3, 2, 4, 1, 1, 8]
def baseStart_495378 : Nat := 118140960795 + 495378 * 2 ^ 59
def prefixEnd_495378 : Nat := 4983230072969 + 3 ^ 40 * 495378 * 2
def baseEnd_495378 : Nat := 16748445739132053662341

theorem tailTrace_495378 : CollatzResearch.WordTrace tailWord_495378 prefixEnd_495378 16748445739132053662341 := by
  unfold tailWord_495378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4516979999834396167963697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12045279999558389781236525 4516979999834396167963697)
  ·
    refine ⟨3387734999875797125972773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4516979999834396167963697 3387734999875797125972773)
    ·
      refine ⟨635200312476711961119895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3387734999875797125972773 635200312476711961119895)
      ·
        refine ⟨952800468715067941679843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635200312476711961119895 952800468715067941679843)
        ·
          refine ⟨1429200703072601912519765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952800468715067941679843 1429200703072601912519765)
          ·
            refine ⟨16748445739132053662341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1429200703072601912519765 16748445739132053662341)
            ·
              rfl

theorem cell19_495378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 8].length) (baseStart_495378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495378 prefixEnd_495378 := by exact prefixLift 495378
  have htrace : WordTrace (prefixWord ++ tailWord_495378) baseStart_495378 baseEnd_495378 := by
    simpa [prefixWord, tailWord_495378, baseEnd_495378] using wordTrace_append hprefix tailTrace_495378
  have hstable : (prefixWord ++ tailWord_495378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495378).length < 2 ^ (prefixWord ++ tailWord_495378).sum := by decide
  have hdescent : baseEnd_495378 < baseStart_495378 := by decide
  rcases family_descends (prefixWord ++ tailWord_495378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495397 : List Nat := [1, 3, 1, 2, 3, 4, 1, 4]
def baseStart_495397 : Nat := 118140960795 + 495397 * 2 ^ 59
def prefixEnd_495397 : Nat := 4983230072969 + 3 ^ 40 * 495397 * 2
def baseEnd_495397 : Nat := 150741793064002068538795

theorem tailTrace_495397 : CollatzResearch.WordTrace tailWord_495397 prefixEnd_495397 150741793064002068538795 := by
  unfold tailWord_495397
  simp only [CollatzResearch.WordTrace]
  refine ⟨18068612986268750916796445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12045741990845833944530963 18068612986268750916796445)
  ·
    refine ⟨6775729869850781593798667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18068612986268750916796445 6775729869850781593798667)
    ·
      refine ⟨10163594804776172390698001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6775729869850781593798667 10163594804776172390698001)
      ·
        refine ⟨7622696103582129293023501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10163594804776172390698001 7622696103582129293023501)
        ·
          refine ⟨2858511038843298484883813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7622696103582129293023501 2858511038843298484883813)
          ·
            refine ⟨535970819783118465915715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2858511038843298484883813 535970819783118465915715)
            ·
              refine ⟨803956229674677698873573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535970819783118465915715 803956229674677698873573)
              ·
                refine ⟨150741793064002068538795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803956229674677698873573 150741793064002068538795)
                ·
                  rfl

theorem cell19_495397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_495397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495397 prefixEnd_495397 := by exact prefixLift 495397
  have htrace : WordTrace (prefixWord ++ tailWord_495397) baseStart_495397 baseEnd_495397 := by
    simpa [prefixWord, tailWord_495397, baseEnd_495397] using wordTrace_append hprefix tailTrace_495397
  have hstable : (prefixWord ++ tailWord_495397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495397).length < 2 ^ (prefixWord ++ tailWord_495397).sum := by decide
  have hdescent : baseEnd_495397 < baseStart_495397 := by decide
  rcases family_descends (prefixWord ++ tailWord_495397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495416 : List Nat := [2, 1, 2, 1, 3, 4, 3, 3]
def baseStart_495416 : Nat := 118140960795 + 495416 * 2 ^ 59
def prefixEnd_495416 : Nat := 4983230072969 + 3 ^ 40 * 495416 * 2
def baseEnd_495416 : Nat := 150747574475815654116521

theorem tailTrace_495416 : CollatzResearch.WordTrace tailWord_495416 prefixEnd_495416 150747574475815654116521 := by
  unfold tailWord_495416
  simp only [CollatzResearch.WordTrace]
  refine ⟨9034652986599958580869051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12046203982133278107825401 9034652986599958580869051)
  ·
    refine ⟨13551979479899937871303577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9034652986599958580869051 13551979479899937871303577)
    ·
      refine ⟨10163984609924953403477683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13551979479899937871303577 10163984609924953403477683)
      ·
        refine ⟨15245976914887430105216525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10163984609924953403477683 15245976914887430105216525)
        ·
          refine ⟨5717241343082786289456197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15245976914887430105216525 5717241343082786289456197)
          ·
            refine ⟨1071982751828022429273037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5717241343082786289456197 1071982751828022429273037)
            ·
              refine ⟨401993531935508410977389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1071982751828022429273037 401993531935508410977389)
              ·
                refine ⟨150747574475815654116521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401993531935508410977389 150747574475815654116521)
                ·
                  rfl

theorem cell19_495416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_495416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495416 prefixEnd_495416 := by exact prefixLift 495416
  have htrace : WordTrace (prefixWord ++ tailWord_495416) baseStart_495416 baseEnd_495416 := by
    simpa [prefixWord, tailWord_495416, baseEnd_495416] using wordTrace_append hprefix tailTrace_495416
  have hstable : (prefixWord ++ tailWord_495416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495416).length < 2 ^ (prefixWord ++ tailWord_495416).sum := by decide
  have hdescent : baseEnd_495416 < baseStart_495416 := by decide
  rcases family_descends (prefixWord ++ tailWord_495416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495553 : List Nat := [1, 2, 16]
def baseStart_495553 : Nat := 118140960795 + 495553 * 2 ^ 59
def prefixEnd_495553 : Nat := 4983230072969 + 3 ^ 40 * 495553 * 2
def baseEnd_495553 : Nat := 620531940320328926221

theorem tailTrace_495553 : CollatzResearch.WordTrace tailWord_495553 prefixEnd_495553 620531940320328926221 := by
  unfold tailWord_495553
  simp only [CollatzResearch.WordTrace]
  refine ⟨18074302773703589559475313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12049535182469059706316875 18074302773703589559475313)
  ·
    refine ⟨13555727080277692169606485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18074302773703589559475313 13555727080277692169606485)
    ·
      refine ⟨620531940320328926221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 13555727080277692169606485 620531940320328926221)
      ·
        rfl

theorem cell19_495553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 16].length) (baseStart_495553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495553 prefixEnd_495553 := by exact prefixLift 495553
  have htrace : WordTrace (prefixWord ++ tailWord_495553) baseStart_495553 baseEnd_495553 := by
    simpa [prefixWord, tailWord_495553, baseEnd_495553] using wordTrace_append hprefix tailTrace_495553
  have hstable : (prefixWord ++ tailWord_495553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495553).length < 2 ^ (prefixWord ++ tailWord_495553).sum := by decide
  have hdescent : baseEnd_495553 < baseStart_495553 := by decide
  rcases family_descends (prefixWord ++ tailWord_495553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495587 : List Nat := [1, 1, 1, 6, 1, 3, 3, 3]
def baseStart_495587 : Nat := 118140960795 + 495587 * 2 ^ 59
def prefixEnd_495587 : Nat := 4983230072969 + 3 ^ 40 * 495587 * 2
def baseEnd_495587 : Nat := 150799607182137924316055

theorem tailTrace_495587 : CollatzResearch.WordTrace tailWord_495587 prefixEnd_495587 150799607182137924316055 := by
  unfold tailWord_495587
  simp only [CollatzResearch.WordTrace]
  refine ⟨18075542855580413366213015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12050361903720275577475343 18075542855580413366213015)
  ·
    refine ⟨27113314283370620049319523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18075542855580413366213015 27113314283370620049319523)
    ·
      refine ⟨40669971425055930073979285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27113314283370620049319523 40669971425055930073979285)
      ·
        refine ⟨1906404910549496722217779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40669971425055930073979285 1906404910549496722217779)
        ·
          refine ⟨2859607365824245083326669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1906404910549496722217779 2859607365824245083326669)
          ·
            refine ⟨1072352762184091906247501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2859607365824245083326669 1072352762184091906247501)
            ·
              refine ⟨402132285819034464842813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1072352762184091906247501 402132285819034464842813)
              ·
                refine ⟨150799607182137924316055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402132285819034464842813 150799607182137924316055)
                ·
                  rfl

theorem cell19_495587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 3].length) (baseStart_495587 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495587 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495587 prefixEnd_495587 := by exact prefixLift 495587
  have htrace : WordTrace (prefixWord ++ tailWord_495587) baseStart_495587 baseEnd_495587 := by
    simpa [prefixWord, tailWord_495587, baseEnd_495587] using wordTrace_append hprefix tailTrace_495587
  have hstable : (prefixWord ++ tailWord_495587).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495587).length < 2 ^ (prefixWord ++ tailWord_495587).sum := by decide
  have hdescent : baseEnd_495587 < baseStart_495587 := by decide
  rcases family_descends (prefixWord ++ tailWord_495587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495606 : List Nat := [5, 1, 1, 1, 4, 1, 6]
def baseStart_495606 : Nat := 118140960795 + 495606 * 2 ^ 59
def prefixEnd_495606 : Nat := 4983230072969 + 3 ^ 40 * 495606 * 2
def baseEnd_495606 : Nat := 50268462864650503297927

theorem tailTrace_495606 : CollatzResearch.WordTrace tailWord_495606 prefixEnd_495606 50268462864650503297927 := by
  unfold tailWord_495606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1129764740156973725697167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12050823895007719740769781 1129764740156973725697167)
  ·
    refine ⟨1694647110235460588545751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1129764740156973725697167 1694647110235460588545751)
    ·
      refine ⟨2541970665353190882818627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1694647110235460588545751 2541970665353190882818627)
      ·
        refine ⟨3812955998029786324227941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2541970665353190882818627 3812955998029786324227941)
        ·
          refine ⟨714929249630584935792739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3812955998029786324227941 714929249630584935792739)
          ·
            refine ⟨1072393874445877403689109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714929249630584935792739 1072393874445877403689109)
            ·
              refine ⟨50268462864650503297927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1072393874445877403689109 50268462864650503297927)
              ·
                rfl

theorem cell19_495606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_495606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495606 prefixEnd_495606 := by exact prefixLift 495606
  have htrace : WordTrace (prefixWord ++ tailWord_495606) baseStart_495606 baseEnd_495606 := by
    simpa [prefixWord, tailWord_495606, baseEnd_495606] using wordTrace_append hprefix tailTrace_495606
  have hstable : (prefixWord ++ tailWord_495606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495606).length < 2 ^ (prefixWord ++ tailWord_495606).sum := by decide
  have hdescent : baseEnd_495606 < baseStart_495606 := by decide
  rcases family_descends (prefixWord ++ tailWord_495606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495644 : List Nat := [2, 2, 3, 1, 3, 1, 4, 3]
def baseStart_495644 : Nat := 118140960795 + 495644 * 2 ^ 59
def prefixEnd_495644 : Nat := 4983230072969 + 3 ^ 40 * 495644 * 2
def baseEnd_495644 : Nat := 150816951417578681049233

theorem tailTrace_495644 : CollatzResearch.WordTrace tailWord_495644 prefixEnd_495644 150816951417578681049233 := by
  unfold tailWord_495644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9038810908186956050518993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12051747877582608067358657 9038810908186956050518993)
  ·
    refine ⟨6779108181140217037889245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9038810908186956050518993 6779108181140217037889245)
    ·
      refine ⟨2542165567927581389208467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6779108181140217037889245 2542165567927581389208467)
      ·
        refine ⟨3813248351891372083812701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2542165567927581389208467 3813248351891372083812701)
        ·
          refine ⟨1429968131959264531429763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3813248351891372083812701 1429968131959264531429763)
          ·
            refine ⟨2144952197938896797144645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429968131959264531429763 2144952197938896797144645)
            ·
              refine ⟨402178537113543149464621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2144952197938896797144645 402178537113543149464621)
              ·
                refine ⟨150816951417578681049233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402178537113543149464621 150816951417578681049233)
                ·
                  rfl

theorem cell19_495644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_495644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495644 prefixEnd_495644 := by exact prefixLift 495644
  have htrace : WordTrace (prefixWord ++ tailWord_495644) baseStart_495644 baseEnd_495644 := by
    simpa [prefixWord, tailWord_495644, baseEnd_495644] using wordTrace_append hprefix tailTrace_495644
  have hstable : (prefixWord ++ tailWord_495644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495644).length < 2 ^ (prefixWord ++ tailWord_495644).sum := by decide
  have hdescent : baseEnd_495644 < baseStart_495644 := by decide
  rcases family_descends (prefixWord ++ tailWord_495644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495665 : List Nat := [1, 2, 2, 3, 1, 5, 5]
def baseStart_495665 : Nat := 118140960795 + 495665 * 2 ^ 59
def prefixEnd_495665 : Nat := 4983230072969 + 3 ^ 40 * 495665 * 2
def baseEnd_495665 : Nat := 50274447133018951527503

theorem tailTrace_495665 : CollatzResearch.WordTrace tailWord_495665 prefixEnd_495665 50274447133018951527503 := by
  unfold tailWord_495665
  simp only [CollatzResearch.WordTrace]
  refine ⟨18078387749297832687552449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12052258499531888458368299 18078387749297832687552449)
  ·
    refine ⟨13558790811973374515664337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18078387749297832687552449 13558790811973374515664337)
    ·
      refine ⟨10169093108980030886748253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13558790811973374515664337 10169093108980030886748253)
      ·
        refine ⟨3813409915867511582530595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10169093108980030886748253 3813409915867511582530595)
        ·
          refine ⟨5720114873801267373795893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813409915867511582530595 5720114873801267373795893)
          ·
            refine ⟨536260769418868816293365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5720114873801267373795893 536260769418868816293365)
            ·
              refine ⟨50274447133018951527503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 536260769418868816293365 50274447133018951527503)
              ·
                rfl

theorem cell19_495665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_495665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495665 prefixEnd_495665 := by exact prefixLift 495665
  have htrace : WordTrace (prefixWord ++ tailWord_495665) baseStart_495665 baseEnd_495665 := by
    simpa [prefixWord, tailWord_495665, baseEnd_495665] using wordTrace_append hprefix tailTrace_495665
  have hstable : (prefixWord ++ tailWord_495665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495665).length < 2 ^ (prefixWord ++ tailWord_495665).sum := by decide
  have hdescent : baseEnd_495665 < baseStart_495665 := by decide
  rcases family_descends (prefixWord ++ tailWord_495665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495667 : List Nat := [1, 1, 1, 2, 4, 1, 9]
def baseStart_495667 : Nat := 118140960795 + 495667 * 2 ^ 59
def prefixEnd_495667 : Nat := 4983230072969 + 3 ^ 40 * 495667 * 2
def baseEnd_495667 : Nat := 50274649989573814179353

theorem tailTrace_495667 : CollatzResearch.WordTrace tailWord_495667 prefixEnd_495667 50274649989573814179353 := by
  unfold tailWord_495667
  simp only [CollatzResearch.WordTrace]
  refine ⟨18078460695290587029125255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12052307130193724686083503 18078460695290587029125255)
  ·
    refine ⟨27117691042935880543687883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18078460695290587029125255 27117691042935880543687883)
    ·
      refine ⟨40676536564403820815531825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27117691042935880543687883 40676536564403820815531825)
      ·
        refine ⟨30507402423302865611648869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40676536564403820815531825 30507402423302865611648869)
        ·
          refine ⟨5720137954369287302184163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30507402423302865611648869 5720137954369287302184163)
          ·
            refine ⟨8580206931553930953276245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5720137954369287302184163 8580206931553930953276245)
            ·
              refine ⟨50274649989573814179353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8580206931553930953276245 50274649989573814179353)
              ·
                rfl

theorem cell19_495667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_495667 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495667 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495667 prefixEnd_495667 := by exact prefixLift 495667
  have htrace : WordTrace (prefixWord ++ tailWord_495667) baseStart_495667 baseEnd_495667 := by
    simpa [prefixWord, tailWord_495667, baseEnd_495667] using wordTrace_append hprefix tailTrace_495667
  have hstable : (prefixWord ++ tailWord_495667).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495667).length < 2 ^ (prefixWord ++ tailWord_495667).sum := by decide
  have hdescent : baseEnd_495667 < baseStart_495667 := by decide
  rcases family_descends (prefixWord ++ tailWord_495667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495705 : List Nat := [1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_495705 : Nat := 118140960795 + 495705 * 2 ^ 59
def prefixEnd_495705 : Nat := 4983230072969 + 3 ^ 40 * 495705 * 2
def baseEnd_495705 : Nat := 150835512792348613693511

theorem tailTrace_495705 : CollatzResearch.WordTrace tailWord_495705 prefixEnd_495705 150835512792348613693511 := by
  unfold tailWord_495705
  simp only [CollatzResearch.WordTrace]
  refine ⟨18079846669152919519008569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12053231112768613012672379 18079846669152919519008569)
  ·
    refine ⟨13559885001864689639256427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18079846669152919519008569 13559885001864689639256427)
    ·
      refine ⟨20339827502797034458884641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13559885001864689639256427 20339827502797034458884641)
      ·
        refine ⟨15254870627097775844163481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20339827502797034458884641 15254870627097775844163481)
        ·
          refine ⟨11441152970323331883122611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15254870627097775844163481 11441152970323331883122611)
          ·
            refine ⟨17161729455484997824683917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11441152970323331883122611 17161729455484997824683917)
            ·
              refine ⟨6435648545806874184256469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17161729455484997824683917 6435648545806874184256469)
              ·
                refine ⟨150835512792348613693511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6435648545806874184256469 150835512792348613693511)
                ·
                  rfl

theorem cell19_495705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_495705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495705 prefixEnd_495705 := by exact prefixLift 495705
  have htrace : WordTrace (prefixWord ++ tailWord_495705) baseStart_495705 baseEnd_495705 := by
    simpa [prefixWord, tailWord_495705, baseEnd_495705] using wordTrace_append hprefix tailTrace_495705
  have hstable : (prefixWord ++ tailWord_495705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495705).length < 2 ^ (prefixWord ++ tailWord_495705).sum := by decide
  have hdescent : baseEnd_495705 < baseStart_495705 := by decide
  rcases family_descends (prefixWord ++ tailWord_495705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495722 : List Nat := [3, 1, 3, 2, 3, 7]
def baseStart_495722 : Nat := 118140960795 + 495722 * 2 ^ 59
def prefixEnd_495722 : Nat := 4983230072969 + 3 ^ 40 * 495722 * 2
def baseEnd_495722 : Nat := 16760076181610845701743

theorem tailTrace_495722 : CollatzResearch.WordTrace tailWord_495722 prefixEnd_495722 16760076181610845701743 := by
  unfold tailWord_495722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4520116677522832855594355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12053644473394220948251613 4520116677522832855594355)
  ·
    refine ⟨6780175016284249283391533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4520116677522832855594355 6780175016284249283391533)
    ·
      refine ⟨2542565631106593481271825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6780175016284249283391533 2542565631106593481271825)
      ·
        refine ⟨1906924223329945110953869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2542565631106593481271825 1906924223329945110953869)
        ·
          refine ⟨715096583748729416607701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1906924223329945110953869 715096583748729416607701)
          ·
            refine ⟨16760076181610845701743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 715096583748729416607701 16760076181610845701743)
            ·
              rfl

theorem cell19_495722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 7].length) (baseStart_495722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495722 prefixEnd_495722 := by exact prefixLift 495722
  have htrace : WordTrace (prefixWord ++ tailWord_495722) baseStart_495722 baseEnd_495722 := by
    simpa [prefixWord, tailWord_495722, baseEnd_495722] using wordTrace_append hprefix tailTrace_495722
  have hstable : (prefixWord ++ tailWord_495722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495722).length < 2 ^ (prefixWord ++ tailWord_495722).sum := by decide
  have hdescent : baseEnd_495722 < baseStart_495722 := by decide
  rcases family_descends (prefixWord ++ tailWord_495722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495724 : List Nat := [2, 2, 1, 1, 3, 10]
def baseStart_495724 : Nat := 118140960795 + 495724 * 2 ^ 59
def prefixEnd_495724 : Nat := 4983230072969 + 3 ^ 40 * 495724 * 2
def baseEnd_495724 : Nat := 16760143800462466585693

theorem tailTrace_495724 : CollatzResearch.WordTrace tailWord_495724 prefixEnd_495724 16760143800462466585693 := by
  unfold tailWord_495724
  simp only [CollatzResearch.WordTrace]
  refine ⟨9040269828042042881975113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12053693104056057175966817 9040269828042042881975113)
  ·
    refine ⟨6780202371031532161481335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9040269828042042881975113 6780202371031532161481335)
    ·
      refine ⟨10170303556547298242222003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6780202371031532161481335 10170303556547298242222003)
      ·
        refine ⟨15255455334820947363333005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10170303556547298242222003 15255455334820947363333005)
        ·
          refine ⟨5720795750557855261249877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15255455334820947363333005 5720795750557855261249877)
          ·
            refine ⟨16760143800462466585693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5720795750557855261249877 16760143800462466585693)
            ·
              rfl

theorem cell19_495724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 10].length) (baseStart_495724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495724 prefixEnd_495724 := by exact prefixLift 495724
  have htrace : WordTrace (prefixWord ++ tailWord_495724) baseStart_495724 baseEnd_495724 := by
    simpa [prefixWord, tailWord_495724, baseEnd_495724] using wordTrace_append hprefix tailTrace_495724
  have hstable : (prefixWord ++ tailWord_495724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495724).length < 2 ^ (prefixWord ++ tailWord_495724).sum := by decide
  have hdescent : baseEnd_495724 < baseStart_495724 := by decide
  rcases family_descends (prefixWord ++ tailWord_495724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495741 : List Nat := [1, 4, 1, 1, 3, 2, 3, 4]
def baseStart_495741 : Nat := 118140960795 + 495741 * 2 ^ 59
def prefixEnd_495741 : Nat := 4983230072969 + 3 ^ 40 * 495741 * 2
def baseEnd_495741 : Nat := 150846467046311196893413

theorem tailTrace_495741 : CollatzResearch.WordTrace tailWord_495741 prefixEnd_495741 150846467046311196893413 := by
  unfold tailWord_495741
  simp only [CollatzResearch.WordTrace]
  refine ⟨18081159697022497667319077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12054106464681665111546051 18081159697022497667319077)
  ·
    refine ⟨3390217443191718312622327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18081159697022497667319077 3390217443191718312622327)
    ·
      refine ⟨5085326164787577468933491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3390217443191718312622327 5085326164787577468933491)
      ·
        refine ⟨7627989247181366203400237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5085326164787577468933491 7627989247181366203400237)
        ·
          refine ⟨2860495967693012326275089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7627989247181366203400237 2860495967693012326275089)
          ·
            refine ⟨2145371975769759244706317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2860495967693012326275089 2145371975769759244706317)
            ·
              refine ⟨804514490913659716764869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2145371975769759244706317 804514490913659716764869)
              ·
                refine ⟨150846467046311196893413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 804514490913659716764869 150846467046311196893413)
                ·
                  rfl

theorem cell19_495741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_495741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495741 prefixEnd_495741 := by exact prefixLift 495741
  have htrace : WordTrace (prefixWord ++ tailWord_495741) baseStart_495741 baseEnd_495741 := by
    simpa [prefixWord, tailWord_495741, baseEnd_495741] using wordTrace_append hprefix tailTrace_495741
  have hstable : (prefixWord ++ tailWord_495741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495741).length < 2 ^ (prefixWord ++ tailWord_495741).sum := by decide
  have hdescent : baseEnd_495741 < baseStart_495741 := by decide
  rcases family_descends (prefixWord ++ tailWord_495741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495760 : List Nat := [2, 1, 1, 1, 1, 1, 9, 3]
def baseStart_495760 : Nat := 118140960795 + 495760 * 2 ^ 59
def prefixEnd_495760 : Nat := 4983230072969 + 3 ^ 40 * 495760 * 2
def baseEnd_495760 : Nat := 150852248458124782471139

theorem tailTrace_495760 : CollatzResearch.WordTrace tailWord_495760 prefixEnd_495760 150852248458124782471139 := by
  unfold tailWord_495760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9040926341976831956130367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12054568455969109274840489 9040926341976831956130367)
  ·
    refine ⟨13561389512965247934195551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9040926341976831956130367 13561389512965247934195551)
    ·
      refine ⟨20342084269447871901293327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13561389512965247934195551 20342084269447871901293327)
      ·
        refine ⟨30513126404171807851939991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20342084269447871901293327 30513126404171807851939991)
        ·
          refine ⟨45769689606257711777909987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30513126404171807851939991 45769689606257711777909987)
          ·
            refine ⟨68654534409386567666864981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45769689606257711777909987 68654534409386567666864981)
            ·
              refine ⟨402272662554999419923037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 68654534409386567666864981 402272662554999419923037)
              ·
                refine ⟨150852248458124782471139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402272662554999419923037 150852248458124782471139)
                ·
                  rfl

theorem cell19_495760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_495760 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495760 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495760 prefixEnd_495760 := by exact prefixLift 495760
  have htrace : WordTrace (prefixWord ++ tailWord_495760) baseStart_495760 baseEnd_495760 := by
    simpa [prefixWord, tailWord_495760, baseEnd_495760] using wordTrace_append hprefix tailTrace_495760
  have hstable : (prefixWord ++ tailWord_495760).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495760).length < 2 ^ (prefixWord ++ tailWord_495760).sum := by decide
  have hdescent : baseEnd_495760 < baseStart_495760 := by decide
  rcases family_descends (prefixWord ++ tailWord_495760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495781 : List Nat := [1, 3, 1, 2, 1, 3, 8]
def baseStart_495781 : Nat := 118140960795 + 495781 * 2 ^ 59
def prefixEnd_495781 : Nat := 4983230072969 + 3 ^ 40 * 495781 * 2
def baseEnd_495781 : Nat := 50286212813200985334805

theorem tailTrace_495781 : CollatzResearch.WordTrace tailWord_495781 prefixEnd_495781 50286212813200985334805 := by
  unfold tailWord_495781
  simp only [CollatzResearch.WordTrace]
  refine ⟨18082618616877584498775197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12055079077918389665850131 18082618616877584498775197)
  ·
    refine ⟨6780981981329094187040699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18082618616877584498775197 6780981981329094187040699)
    ·
      refine ⟨10171472971993641280561049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6780981981329094187040699 10171472971993641280561049)
      ·
        refine ⟨7628604728995230960420787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10171472971993641280561049 7628604728995230960420787)
        ·
          refine ⟨11442907093492846440631181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7628604728995230960420787 11442907093492846440631181)
          ·
            refine ⟨4291090160059817415236693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11442907093492846440631181 4291090160059817415236693)
            ·
              refine ⟨50286212813200985334805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4291090160059817415236693 50286212813200985334805)
              ·
                rfl

theorem cell19_495781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_495781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495781 prefixEnd_495781 := by exact prefixLift 495781
  have htrace : WordTrace (prefixWord ++ tailWord_495781) baseStart_495781 baseEnd_495781 := by
    simpa [prefixWord, tailWord_495781, baseEnd_495781] using wordTrace_append hprefix tailTrace_495781
  have hstable : (prefixWord ++ tailWord_495781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495781).length < 2 ^ (prefixWord ++ tailWord_495781).sum := by decide
  have hdescent : baseEnd_495781 < baseStart_495781 := by decide
  rcases family_descends (prefixWord ++ tailWord_495781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495800 : List Nat := [2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_495800 : Nat := 118140960795 + 495800 * 2 ^ 59
def prefixEnd_495800 : Nat := 4983230072969 + 3 ^ 40 * 495800 * 2
def baseEnd_495800 : Nat := 150864419851416541582141

theorem tailTrace_495800 : CollatzResearch.WordTrace tailWord_495800 prefixEnd_495800 150864419851416541582141 := by
  unfold tailWord_495800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9041655801904375371858427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12055541069205833829144569 9041655801904375371858427)
  ·
    refine ⟨13562483702856563057787641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9041655801904375371858427 13562483702856563057787641)
    ·
      refine ⟨10171862777142422293340731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13562483702856563057787641 10171862777142422293340731)
      ·
        refine ⟨15257794165713633440011097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10171862777142422293340731 15257794165713633440011097)
        ·
          refine ⟨11443345624285225080008323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15257794165713633440011097 11443345624285225080008323)
          ·
            refine ⟨17165018436427837620012485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11443345624285225080008323 17165018436427837620012485)
            ·
              refine ⟨3218440956830219553752341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17165018436427837620012485 3218440956830219553752341)
              ·
                refine ⟨150864419851416541582141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3218440956830219553752341 150864419851416541582141)
                ·
                  rfl

theorem cell19_495800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_495800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495800 prefixEnd_495800 := by exact prefixLift 495800
  have htrace : WordTrace (prefixWord ++ tailWord_495800) baseStart_495800 baseEnd_495800 := by
    simpa [prefixWord, tailWord_495800, baseEnd_495800] using wordTrace_append hprefix tailTrace_495800
  have hstable : (prefixWord ++ tailWord_495800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495800).length < 2 ^ (prefixWord ++ tailWord_495800).sum := by decide
  have hdescent : baseEnd_495800 < baseStart_495800 := by decide
  rcases family_descends (prefixWord ++ tailWord_495800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495819 : List Nat := [1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_495819 : Nat := 118140960795 + 495819 * 2 ^ 59
def prefixEnd_495819 : Nat := 4983230072969 + 3 ^ 40 * 495819 * 2
def baseEnd_495819 : Nat := 150870201263230127159867

theorem tailTrace_495819 : CollatzResearch.WordTrace tailWord_495819 prefixEnd_495819 150870201263230127159867 := by
  unfold tailWord_495819
  simp only [CollatzResearch.WordTrace]
  refine ⟨18084004590739916988658511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12056003060493277992439007 18084004590739916988658511)
  ·
    refine ⟨27126006886109875482987767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18084004590739916988658511 27126006886109875482987767)
    ·
      refine ⟨40689010329164813224481651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27126006886109875482987767 40689010329164813224481651)
      ·
        refine ⟨61033515493747219836722477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40689010329164813224481651 61033515493747219836722477)
        ·
          refine ⟨22887568310155207438770929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61033515493747219836722477 22887568310155207438770929)
          ·
            refine ⟨17165676232616405579078197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22887568310155207438770929 17165676232616405579078197)
            ·
              refine ⟨1609282146807788023038581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17165676232616405579078197 1609282146807788023038581)
              ·
                refine ⟨150870201263230127159867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1609282146807788023038581 150870201263230127159867)
                ·
                  rfl

theorem cell19_495819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_495819 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495819 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495819 prefixEnd_495819 := by exact prefixLift 495819
  have htrace : WordTrace (prefixWord ++ tailWord_495819) baseStart_495819 baseEnd_495819 := by
    simpa [prefixWord, tailWord_495819, baseEnd_495819] using wordTrace_append hprefix tailTrace_495819
  have hstable : (prefixWord ++ tailWord_495819).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495819).length < 2 ^ (prefixWord ++ tailWord_495819).sum := by decide
  have hdescent : baseEnd_495819 < baseStart_495819 := by decide
  rcases family_descends (prefixWord ++ tailWord_495819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495853 : List Nat := [1, 5, 1, 2, 3, 1, 2, 4]
def baseStart_495853 : Nat := 118140960795 + 495853 * 2 ^ 59
def prefixEnd_495853 : Nat := 4983230072969 + 3 ^ 40 * 495853 * 2
def baseEnd_495853 : Nat := 150880546947528122404219

theorem tailTrace_495853 : CollatzResearch.WordTrace tailWord_495853 prefixEnd_495853 150880546947528122404219 := by
  unfold tailWord_495853
  simp only [CollatzResearch.WordTrace]
  refine ⟨18085244672616740795396213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12056829781744493863597475 18085244672616740795396213)
  ·
    refine ⟨1695491688057819449568395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18085244672616740795396213 1695491688057819449568395)
    ·
      refine ⟨2543237532086729174352593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1695491688057819449568395 2543237532086729174352593)
      ·
        refine ⟨1907428149065046880764445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2543237532086729174352593 1907428149065046880764445)
        ·
          refine ⟨715285555899392580286667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1907428149065046880764445 715285555899392580286667)
          ·
            refine ⟨1072928333849088870430001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715285555899392580286667 1072928333849088870430001)
            ·
              refine ⟨804696250386816652822501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072928333849088870430001 804696250386816652822501)
              ·
                refine ⟨150880546947528122404219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 804696250386816652822501 150880546947528122404219)
                ·
                  rfl

theorem cell19_495853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_495853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495853 prefixEnd_495853 := by exact prefixLift 495853
  have htrace : WordTrace (prefixWord ++ tailWord_495853) baseStart_495853 baseEnd_495853 := by
    simpa [prefixWord, tailWord_495853, baseEnd_495853] using wordTrace_append hprefix tailTrace_495853
  have hstable : (prefixWord ++ tailWord_495853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495853).length < 2 ^ (prefixWord ++ tailWord_495853).sum := by decide
  have hdescent : baseEnd_495853 < baseStart_495853 := by decide
  rcases family_descends (prefixWord ++ tailWord_495853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495855 : List Nat := [1, 1, 2, 1, 6, 2, 2, 4]
def baseStart_495855 : Nat := 118140960795 + 495855 * 2 ^ 59
def prefixEnd_495855 : Nat := 4983230072969 + 3 ^ 40 * 495855 * 2
def baseEnd_495855 : Nat := 150881155517192710359769

theorem tailTrace_495855 : CollatzResearch.WordTrace tailWord_495855 prefixEnd_495855 150881155517192710359769 := by
  unfold tailWord_495855
  simp only [CollatzResearch.WordTrace]
  refine ⟨18085317618609495136969019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12056878412406330091312679 18085317618609495136969019)
  ·
    refine ⟨27127976427914242705453529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18085317618609495136969019 27127976427914242705453529)
    ·
      refine ⟨20345982320935682029090147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27127976427914242705453529 20345982320935682029090147)
      ·
        refine ⟨30518973481403523043635221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20345982320935682029090147 30518973481403523043635221)
        ·
          refine ⟨1430576881940790142670401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30518973481403523043635221 1430576881940790142670401)
          ·
            refine ⟨1072932661455592607002801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1430576881940790142670401 1072932661455592607002801)
            ·
              refine ⟨804699496091694455252101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072932661455592607002801 804699496091694455252101)
              ·
                refine ⟨150881155517192710359769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 804699496091694455252101 150881155517192710359769)
                ·
                  rfl

theorem cell19_495855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_495855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495855 prefixEnd_495855 := by exact prefixLift 495855
  have htrace : WordTrace (prefixWord ++ tailWord_495855) baseStart_495855 baseEnd_495855 := by
    simpa [prefixWord, tailWord_495855, baseEnd_495855] using wordTrace_append hprefix tailTrace_495855
  have hstable : (prefixWord ++ tailWord_495855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495855).length < 2 ^ (prefixWord ++ tailWord_495855).sum := by decide
  have hdescent : baseEnd_495855 < baseStart_495855 := by decide
  rcases family_descends (prefixWord ++ tailWord_495855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495857 : List Nat := [1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_495857 : Nat := 118140960795 + 495857 * 2 ^ 59
def prefixEnd_495857 : Nat := 4983230072969 + 3 ^ 40 * 495857 * 2
def baseEnd_495857 : Nat := 150881764086857298315319

theorem tailTrace_495857 : CollatzResearch.WordTrace tailWord_495857 prefixEnd_495857 150881764086857298315319 := by
  unfold tailWord_495857
  simp only [CollatzResearch.WordTrace]
  refine ⟨18085390564602249478541825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12056927043068166319027883 18085390564602249478541825)
  ·
    refine ⟨13564042923451687108906369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18085390564602249478541825 13564042923451687108906369)
    ·
      refine ⟨10173032192588765331679777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13564042923451687108906369 10173032192588765331679777)
      ·
        refine ⟨7629774144441573998759833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10173032192588765331679777 7629774144441573998759833)
        ·
          refine ⟨5722330608331180499069875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7629774144441573998759833 5722330608331180499069875)
          ·
            refine ⟨8583495912496770748604813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5722330608331180499069875 8583495912496770748604813)
            ·
              refine ⟨3218810967186289030726805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8583495912496770748604813 3218810967186289030726805)
              ·
                refine ⟨150881764086857298315319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3218810967186289030726805 150881764086857298315319)
                ·
                  rfl

theorem cell19_495857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_495857 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495857 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495857 prefixEnd_495857 := by exact prefixLift 495857
  have htrace : WordTrace (prefixWord ++ tailWord_495857) baseStart_495857 baseEnd_495857 := by
    simpa [prefixWord, tailWord_495857, baseEnd_495857] using wordTrace_append hprefix tailTrace_495857
  have hstable : (prefixWord ++ tailWord_495857).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495857).length < 2 ^ (prefixWord ++ tailWord_495857).sum := by decide
  have hdescent : baseEnd_495857 < baseStart_495857 := by decide
  rcases family_descends (prefixWord ++ tailWord_495857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495895 : List Nat := [1, 1, 3, 4, 1, 9]
def baseStart_495895 : Nat := 118140960795 + 495895 * 2 ^ 59
def prefixEnd_495895 : Nat := 4983230072969 + 3 ^ 40 * 495895 * 2
def baseEnd_495895 : Nat := 16765925212276052163419

theorem tailTrace_495895 : CollatzResearch.WordTrace tailWord_495895 prefixEnd_495895 16765925212276052163419 := by
  unfold tailWord_495895
  simp only [CollatzResearch.WordTrace]
  refine ⟨18086776538464581968425139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12057851025643054645616759 18086776538464581968425139)
  ·
    refine ⟨27130164807696872952637709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18086776538464581968425139 27130164807696872952637709)
    ·
      refine ⟨10173811802886327357239141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27130164807696872952637709 10173811802886327357239141)
      ·
        refine ⟨1907589713041186379482339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10173811802886327357239141 1907589713041186379482339)
        ·
          refine ⟨2861384569561779569223509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907589713041186379482339 2861384569561779569223509)
          ·
            refine ⟨16765925212276052163419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2861384569561779569223509 16765925212276052163419)
            ·
              rfl

theorem cell19_495895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 9].length) (baseStart_495895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495895 prefixEnd_495895 := by exact prefixLift 495895
  have htrace : WordTrace (prefixWord ++ tailWord_495895) baseStart_495895 baseEnd_495895 := by
    simpa [prefixWord, tailWord_495895, baseEnd_495895] using wordTrace_append hprefix tailTrace_495895
  have hstable : (prefixWord ++ tailWord_495895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495895).length < 2 ^ (prefixWord ++ tailWord_495895).sum := by decide
  have hdescent : baseEnd_495895 < baseStart_495895 := by decide
  rcases family_descends (prefixWord ++ tailWord_495895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495929 : List Nat := [1, 2, 1, 6, 1, 2, 3, 3]
def baseStart_495929 : Nat := 118140960795 + 495929 * 2 ^ 59
def prefixEnd_495929 : Nat := 4983230072969 + 3 ^ 40 * 495929 * 2
def baseEnd_495929 : Nat := 150903672594782464715123

theorem tailTrace_495929 : CollatzResearch.WordTrace tailWord_495929 prefixEnd_495929 150903672594782464715123 := by
  unfold tailWord_495929
  simp only [CollatzResearch.WordTrace]
  refine ⟨18088016620341405775162841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12058677746894270516775227 18088016620341405775162841)
  ·
    refine ⟨13566012465256054331372131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18088016620341405775162841 13566012465256054331372131)
    ·
      refine ⟨20349018697884081497058197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13566012465256054331372131 20349018697884081497058197)
      ·
        refine ⟨953860251463316320174603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20349018697884081497058197 953860251463316320174603)
        ·
          refine ⟨1430790377194974480261905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953860251463316320174603 1430790377194974480261905)
          ·
            refine ⟨1073092782896230860196429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1430790377194974480261905 1073092782896230860196429)
            ·
              refine ⟨402409793586086572573661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1073092782896230860196429 402409793586086572573661)
              ·
                refine ⟨150903672594782464715123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402409793586086572573661 150903672594782464715123)
                ·
                  rfl

theorem cell19_495929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 3].length) (baseStart_495929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495929 prefixEnd_495929 := by exact prefixLift 495929
  have htrace : WordTrace (prefixWord ++ tailWord_495929) baseStart_495929 baseEnd_495929 := by
    simpa [prefixWord, tailWord_495929, baseEnd_495929] using wordTrace_append hprefix tailTrace_495929
  have hstable : (prefixWord ++ tailWord_495929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495929).length < 2 ^ (prefixWord ++ tailWord_495929).sum := by decide
  have hdescent : baseEnd_495929 < baseStart_495929 := by decide
  rcases family_descends (prefixWord ++ tailWord_495929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495952 : List Nat := [2, 1, 1, 1, 1, 7, 6]
def baseStart_495952 : Nat := 118140960795 + 495952 * 2 ^ 59
def prefixEnd_495952 : Nat := 4983230072969 + 3 ^ 40 * 495952 * 2
def baseEnd_495952 : Nat := 50303557048641742067983

theorem tailTrace_495952 : CollatzResearch.WordTrace tailWord_495952 prefixEnd_495952 50303557048641742067983 := by
  unfold tailWord_495952
  simp only [CollatzResearch.WordTrace]
  refine ⟨9044427749629040351625055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12059236999505387135500073 9044427749629040351625055)
  ·
    refine ⟨13566641624443560527437583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9044427749629040351625055 13566641624443560527437583)
    ·
      refine ⟨20349962436665340791156375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13566641624443560527437583 20349962436665340791156375)
      ·
        refine ⟨30524943654998011186734563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20349962436665340791156375 30524943654998011186734563)
        ·
          refine ⟨45787415482497016780101845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30524943654998011186734563 45787415482497016780101845)
          ·
            refine ⟨1073142550371023830783637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45787415482497016780101845 1073142550371023830783637)
            ·
              refine ⟨50303557048641742067983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1073142550371023830783637 50303557048641742067983)
              ·
                rfl

theorem cell19_495952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_495952 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495952 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495952 prefixEnd_495952 := by exact prefixLift 495952
  have htrace : WordTrace (prefixWord ++ tailWord_495952) baseStart_495952 baseEnd_495952 := by
    simpa [prefixWord, tailWord_495952, baseEnd_495952] using wordTrace_append hprefix tailTrace_495952
  have hstable : (prefixWord ++ tailWord_495952).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495952).length < 2 ^ (prefixWord ++ tailWord_495952).sum := by decide
  have hdescent : baseEnd_495952 < baseStart_495952 := by decide
  rcases family_descends (prefixWord ++ tailWord_495952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495971 : List Nat := [1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_495971 : Nat := 118140960795 + 495971 * 2 ^ 59
def prefixEnd_495971 : Nat := 4983230072969 + 3 ^ 40 * 495971 * 2
def baseEnd_495971 : Nat := 150916452557738811781675

theorem tailTrace_495971 : CollatzResearch.WordTrace tailWord_495971 prefixEnd_495971 150916452557738811781675 := by
  unfold tailWord_495971
  simp only [CollatzResearch.WordTrace]
  refine ⟨18089548486189246948191767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12059698990792831298794511 18089548486189246948191767)
  ·
    refine ⟨27134322729283870422287651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18089548486189246948191767 27134322729283870422287651)
    ·
      refine ⟨40701484093925805633431477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27134322729283870422287651 40701484093925805633431477)
      ·
        refine ⟨3815764133805544278134201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40701484093925805633431477 3815764133805544278134201)
        ·
          refine ⟨2861823100354158208600651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3815764133805544278134201 2861823100354158208600651)
          ·
            refine ⟨4292734650531237312900977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861823100354158208600651 4292734650531237312900977)
            ·
              refine ⟨3219550987898427984675733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4292734650531237312900977 3219550987898427984675733)
              ·
                refine ⟨150916452557738811781675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3219550987898427984675733 150916452557738811781675)
                ·
                  rfl

theorem cell19_495971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_495971 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495971 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495971 prefixEnd_495971 := by exact prefixLift 495971
  have htrace : WordTrace (prefixWord ++ tailWord_495971) baseStart_495971 baseEnd_495971 := by
    simpa [prefixWord, tailWord_495971, baseEnd_495971] using wordTrace_append hprefix tailTrace_495971
  have hstable : (prefixWord ++ tailWord_495971).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495971).length < 2 ^ (prefixWord ++ tailWord_495971).sum := by decide
  have hdescent : baseEnd_495971 < baseStart_495971 := by decide
  rcases family_descends (prefixWord ++ tailWord_495971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495986 : List Nat := [3, 2, 1, 2, 1, 5, 2, 3]
def baseStart_495986 : Nat := 118140960795 + 495986 * 2 ^ 59
def prefixEnd_495986 : Nat := 4983230072969 + 3 ^ 40 * 495986 * 2
def baseEnd_495986 : Nat := 150921016830223221448301

theorem tailTrace_495986 : CollatzResearch.WordTrace tailWord_495986 prefixEnd_495986 150921016830223221448301 := by
  unfold tailWord_495986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522523895283726127496953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12060063720756603006658541 4522523895283726127496953)
  ·
    refine ⟨3391892921462794595622715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4522523895283726127496953 3391892921462794595622715)
    ·
      refine ⟨5087839382194191893434073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3391892921462794595622715 5087839382194191893434073)
      ·
        refine ⟨3815879536645643920075555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5087839382194191893434073 3815879536645643920075555)
        ·
          refine ⟨5723819304968465880113333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815879536645643920075555 5723819304968465880113333)
          ·
            refine ⟨536608059840793676260625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5723819304968465880113333 536608059840793676260625)
            ·
              refine ⟨402456044880595257195469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536608059840793676260625 402456044880595257195469)
              ·
                refine ⟨150921016830223221448301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402456044880595257195469 150921016830223221448301)
                ·
                  rfl

theorem cell19_495986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_495986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_495986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_495986 prefixEnd_495986 := by exact prefixLift 495986
  have htrace : WordTrace (prefixWord ++ tailWord_495986) baseStart_495986 baseEnd_495986 := by
    simpa [prefixWord, tailWord_495986, baseEnd_495986] using wordTrace_append hprefix tailTrace_495986
  have hstable : (prefixWord ++ tailWord_495986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495986).length < 2 ^ (prefixWord ++ tailWord_495986).sum := by decide
  have hdescent : baseEnd_495986 < baseStart_495986 := by decide
  rcases family_descends (prefixWord ++ tailWord_495986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496009 : List Nat := [1, 2, 1, 1, 6, 1, 7]
def baseStart_496009 : Nat := 118140960795 + 496009 * 2 ^ 59
def prefixEnd_496009 : Nat := 4983230072969 + 3 ^ 40 * 496009 * 2
def baseEnd_496009 : Nat := 50309338460455327645709

theorem tailTrace_496009 : CollatzResearch.WordTrace tailWord_496009 prefixEnd_496009 50309338460455327645709 := by
  unfold tailWord_496009
  simp only [CollatzResearch.WordTrace]
  refine ⟨18090934460051579438075081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12060622973367719625383387 18090934460051579438075081)
  ·
    refine ⟨13568200845038684578556311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18090934460051579438075081 13568200845038684578556311)
    ·
      refine ⟨20352301267558026867834467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13568200845038684578556311 20352301267558026867834467)
      ·
        refine ⟨30528451901337040301751701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20352301267558026867834467 30528451901337040301751701)
        ·
          refine ⟨1431021182875173764144611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30528451901337040301751701 1431021182875173764144611)
          ·
            refine ⟨2146531774312760646216917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431021182875173764144611 2146531774312760646216917)
            ·
              refine ⟨50309338460455327645709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2146531774312760646216917 50309338460455327645709)
              ·
                rfl

theorem cell19_496009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_496009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496009 prefixEnd_496009 := by exact prefixLift 496009
  have htrace : WordTrace (prefixWord ++ tailWord_496009) baseStart_496009 baseEnd_496009 := by
    simpa [prefixWord, tailWord_496009, baseEnd_496009] using wordTrace_append hprefix tailTrace_496009
  have hstable : (prefixWord ++ tailWord_496009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496009).length < 2 ^ (prefixWord ++ tailWord_496009).sum := by decide
  have hdescent : baseEnd_496009 < baseStart_496009 := by decide
  rcases family_descends (prefixWord ++ tailWord_496009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496026 : List Nat := [3, 1, 1, 4, 1, 3, 2, 4]
def baseStart_496026 : Nat := 118140960795 + 496026 * 2 ^ 59
def prefixEnd_496026 : Nat := 4983230072969 + 3 ^ 40 * 496026 * 2
def baseEnd_496026 : Nat := 150933188223514980559303

theorem tailTrace_496026 : CollatzResearch.WordTrace tailWord_496026 prefixEnd_496026 150933188223514980559303 := by
  unfold tailWord_496026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522888625247497835360983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12061036333993327560962621 4522888625247497835360983)
  ·
    refine ⟨6784332937871246753041475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4522888625247497835360983 6784332937871246753041475)
    ·
      refine ⟨10176499406806870129562213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6784332937871246753041475 10176499406806870129562213)
      ·
        refine ⟨1908093638776288149292915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10176499406806870129562213 1908093638776288149292915)
        ·
          refine ⟨2862140458164432223939373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908093638776288149292915 2862140458164432223939373)
          ·
            refine ⟨1073302671811662083977265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2862140458164432223939373 1073302671811662083977265)
            ·
              refine ⟨804977003858746562982949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073302671811662083977265 804977003858746562982949)
              ·
                refine ⟨150933188223514980559303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 804977003858746562982949 150933188223514980559303)
                ·
                  rfl

theorem cell19_496026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_496026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496026 prefixEnd_496026 := by exact prefixLift 496026
  have htrace : WordTrace (prefixWord ++ tailWord_496026) baseStart_496026 baseEnd_496026 := by
    simpa [prefixWord, tailWord_496026, baseEnd_496026] using wordTrace_append hprefix tailTrace_496026
  have hstable : (prefixWord ++ tailWord_496026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496026).length < 2 ^ (prefixWord ++ tailWord_496026).sum := by decide
  have hdescent : baseEnd_496026 < baseStart_496026 := by decide
  rcases family_descends (prefixWord ++ tailWord_496026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496157 : List Nat := [1, 4, 2, 2, 1, 4, 2, 3]
def baseStart_496157 : Nat := 118140960795 + 496157 * 2 ^ 59
def prefixEnd_496157 : Nat := 4983230072969 + 3 ^ 40 * 496157 * 2
def baseEnd_496157 : Nat := 150973049536545491647835

theorem tailTrace_496157 : CollatzResearch.WordTrace tailWord_496157 prefixEnd_496157 150973049536545491647835 := by
  unfold tailWord_496157
  simp only [CollatzResearch.WordTrace]
  refine ⟨18096332463515400714462725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12064221642343600476308483 18096332463515400714462725)
  ·
    refine ⟨3393062336909137633961761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18096332463515400714462725 3393062336909137633961761)
    ·
      refine ⟨2544796752681853225471321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3393062336909137633961761 2544796752681853225471321)
      ·
        refine ⟨1908597564511389919103491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2544796752681853225471321 1908597564511389919103491)
        ·
          refine ⟨2862896346767084878655237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908597564511389919103491 2862896346767084878655237)
          ·
            refine ⟨536793065018828414747857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2862896346767084878655237 536793065018828414747857)
            ·
              refine ⟨402594798764121311060893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536793065018828414747857 402594798764121311060893)
              ·
                refine ⟨150973049536545491647835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402594798764121311060893 150973049536545491647835)
                ·
                  rfl

theorem cell19_496157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 3].length) (baseStart_496157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496157 prefixEnd_496157 := by exact prefixLift 496157
  have htrace : WordTrace (prefixWord ++ tailWord_496157) baseStart_496157 baseEnd_496157 := by
    simpa [prefixWord, tailWord_496157, baseEnd_496157] using wordTrace_append hprefix tailTrace_496157
  have hstable : (prefixWord ++ tailWord_496157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496157).length < 2 ^ (prefixWord ++ tailWord_496157).sum := by decide
  have hdescent : baseEnd_496157 < baseStart_496157 := by decide
  rcases family_descends (prefixWord ++ tailWord_496157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496161 : List Nat := [1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_496161 : Nat := 118140960795 + 496161 * 2 ^ 59
def prefixEnd_496161 : Nat := 4983230072969 + 3 ^ 40 * 496161 * 2
def baseEnd_496161 : Nat := 150974266675874667558935

theorem tailTrace_496161 : CollatzResearch.WordTrace tailWord_496161 prefixEnd_496161 150974266675874667558935 := by
  unfold tailWord_496161
  simp only [CollatzResearch.WordTrace]
  refine ⟨18096478355500909397608337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12064318903667272931738891 18096478355500909397608337)
  ·
    refine ⟨13572358766625682048206253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18096478355500909397608337 13572358766625682048206253)
    ·
      refine ⟨5089634537484630768077345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13572358766625682048206253 5089634537484630768077345)
      ·
        refine ⟨3817225903113473076058009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5089634537484630768077345 3817225903113473076058009)
        ·
          refine ⟨2862919427335104807043507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3817225903113473076058009 2862919427335104807043507)
          ·
            refine ⟨4294379141002657210565261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862919427335104807043507 4294379141002657210565261)
            ·
              refine ⟨1610392177875996453961973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4294379141002657210565261 1610392177875996453961973)
              ·
                refine ⟨150974266675874667558935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1610392177875996453961973 150974266675874667558935)
                ·
                  rfl

theorem cell19_496161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_496161 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496161 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496161 prefixEnd_496161 := by exact prefixLift 496161
  have htrace : WordTrace (prefixWord ++ tailWord_496161) baseStart_496161 baseEnd_496161 := by
    simpa [prefixWord, tailWord_496161, baseEnd_496161] using wordTrace_append hprefix tailTrace_496161
  have hstable : (prefixWord ++ tailWord_496161).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496161).length < 2 ^ (prefixWord ++ tailWord_496161).sum := by decide
  have hdescent : baseEnd_496161 < baseStart_496161 := by decide
  rcases family_descends (prefixWord ++ tailWord_496161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496199 : List Nat := [1, 1, 4, 1, 4, 1, 1, 6]
def baseStart_496199 : Nat := 118140960795 + 496199 * 2 ^ 59
def prefixEnd_496199 : Nat := 4983230072969 + 3 ^ 40 * 496199 * 2
def baseEnd_496199 : Nat := 150985829499501838714387

theorem tailTrace_496199 : CollatzResearch.WordTrace tailWord_496199 prefixEnd_496199 150985829499501838714387 := by
  unfold tailWord_496199
  simp only [CollatzResearch.WordTrace]
  refine ⟨18097864329363241887491651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12065242886242161258327767 18097864329363241887491651)
  ·
    refine ⟨27146796494044862831237477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18097864329363241887491651 27146796494044862831237477)
    ·
      refine ⟨5090024342633411780857027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27146796494044862831237477 5090024342633411780857027)
      ·
        refine ⟨7635036513950117671285541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5090024342633411780857027 7635036513950117671285541)
        ·
          refine ⟨1431569346365647063366039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7635036513950117671285541 1431569346365647063366039)
          ·
            refine ⟨2147354019548470595049059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431569346365647063366039 2147354019548470595049059)
            ·
              refine ⟨3221031029322705892573589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147354019548470595049059 3221031029322705892573589)
              ·
                refine ⟨150985829499501838714387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3221031029322705892573589 150985829499501838714387)
                ·
                  rfl

theorem cell19_496199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_496199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496199 prefixEnd_496199 := by exact prefixLift 496199
  have htrace : WordTrace (prefixWord ++ tailWord_496199) baseStart_496199 baseEnd_496199 := by
    simpa [prefixWord, tailWord_496199, baseEnd_496199] using wordTrace_append hprefix tailTrace_496199
  have hstable : (prefixWord ++ tailWord_496199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496199).length < 2 ^ (prefixWord ++ tailWord_496199).sum := by decide
  have hdescent : baseEnd_496199 < baseStart_496199 := by decide
  rcases family_descends (prefixWord ++ tailWord_496199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496237 : List Nat := [1, 5, 1, 1, 3, 8]
def baseStart_496237 : Nat := 118140960795 + 496237 * 2 ^ 59
def prefixEnd_496237 : Nat := 4983230072969 + 3 ^ 40 * 496237 * 2
def baseEnd_496237 : Nat := 16777488035903223318871

theorem tailTrace_496237 : CollatzResearch.WordTrace tailWord_496237 prefixEnd_496237 16777488035903223318871 := by
  unfold tailWord_496237
  simp only [CollatzResearch.WordTrace]
  refine ⟨18099250303225574377374965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12066166868817049584916643 18099250303225574377374965)
  ·
    refine ⟨1696804715927397597878903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18099250303225574377374965 1696804715927397597878903)
    ·
      refine ⟨2545207073891096396818355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696804715927397597878903 2545207073891096396818355)
      ·
        refine ⟨3817810610836644595227533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545207073891096396818355 3817810610836644595227533)
        ·
          refine ⟨1431678979063741723210325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3817810610836644595227533 1431678979063741723210325)
          ·
            refine ⟨16777488035903223318871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1431678979063741723210325 16777488035903223318871)
            ·
              rfl

theorem cell19_496237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 8].length) (baseStart_496237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496237 prefixEnd_496237 := by exact prefixLift 496237
  have htrace : WordTrace (prefixWord ++ tailWord_496237) baseStart_496237 baseEnd_496237 := by
    simpa [prefixWord, tailWord_496237, baseEnd_496237] using wordTrace_append hprefix tailTrace_496237
  have hstable : (prefixWord ++ tailWord_496237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496237).length < 2 ^ (prefixWord ++ tailWord_496237).sum := by decide
  have hdescent : baseEnd_496237 < baseStart_496237 := by decide
  rcases family_descends (prefixWord ++ tailWord_496237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496256 : List Nat := [2, 1, 1, 2, 1, 5, 3, 4]
def baseStart_496256 : Nat := 118140960795 + 496256 * 2 ^ 59
def prefixEnd_496256 : Nat := 4983230072969 + 3 ^ 40 * 496256 * 2
def baseEnd_496256 : Nat := 151003173734942595447565

theorem tailTrace_496256 : CollatzResearch.WordTrace tailWord_496256 prefixEnd_496256 151003173734942595447565 := by
  unfold tailWord_496256
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049971645078370311158311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12066628860104493748211081 9049971645078370311158311)
  ·
    refine ⟨13574957467617555466737467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9049971645078370311158311 13574957467617555466737467)
    ·
      refine ⟨20362436201426333200106201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13574957467617555466737467 20362436201426333200106201)
      ·
        refine ⟨15271827151069749900079651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20362436201426333200106201 15271827151069749900079651)
        ·
          refine ⟨22907740726604624850119477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15271827151069749900079651 22907740726604624850119477)
          ·
            refine ⟨2147600693119183579698701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22907740726604624850119477 2147600693119183579698701)
            ·
              refine ⟨805350259919693842387013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2147600693119183579698701 805350259919693842387013)
              ·
                refine ⟨151003173734942595447565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 805350259919693842387013 151003173734942595447565)
                ·
                  rfl

theorem cell19_496256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_496256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496256 prefixEnd_496256 := by exact prefixLift 496256
  have htrace : WordTrace (prefixWord ++ tailWord_496256) baseStart_496256 baseEnd_496256 := by
    simpa [prefixWord, tailWord_496256, baseEnd_496256] using wordTrace_append hprefix tailTrace_496256
  have hstable : (prefixWord ++ tailWord_496256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496256).length < 2 ^ (prefixWord ++ tailWord_496256).sum := by decide
  have hdescent : baseEnd_496256 < baseStart_496256 := by decide
  rcases family_descends (prefixWord ++ tailWord_496256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496326 : List Nat := [6, 1, 2, 1, 2, 1, 1, 5]
def baseStart_496326 : Nat := 118140960795 + 496326 * 2 ^ 59
def prefixEnd_496326 : Nat := 4983230072969 + 3 ^ 40 * 496326 * 2
def baseEnd_496326 : Nat := 151024473673203173891819

theorem tailTrace_496326 : CollatzResearch.WordTrace tailWord_496326 prefixEnd_496326 151024473673203173891819 := by
  unfold tailWord_496326
  simp only [CollatzResearch.WordTrace]
  refine ⟨565703012496973205542651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12068330933268761718243221 565703012496973205542651)
  ·
    refine ⟨848554518745459808313977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 565703012496973205542651 848554518745459808313977)
    ·
      refine ⟨636415889059094856235483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 848554518745459808313977 636415889059094856235483)
      ·
        refine ⟨954623833588642284353225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636415889059094856235483 954623833588642284353225)
        ·
          refine ⟨715967875191481713264919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954623833588642284353225 715967875191481713264919)
          ·
            refine ⟨1073951812787222569897379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715967875191481713264919 1073951812787222569897379)
            ·
              refine ⟨1610927719180833854846069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073951812787222569897379 1610927719180833854846069)
              ·
                refine ⟨151024473673203173891819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1610927719180833854846069 151024473673203173891819)
                ·
                  rfl

theorem cell19_496326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_496326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496326 prefixEnd_496326 := by exact prefixLift 496326
  have htrace : WordTrace (prefixWord ++ tailWord_496326) baseStart_496326 baseEnd_496326 := by
    simpa [prefixWord, tailWord_496326, baseEnd_496326] using wordTrace_append hprefix tailTrace_496326
  have hstable : (prefixWord ++ tailWord_496326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496326).length < 2 ^ (prefixWord ++ tailWord_496326).sum := by decide
  have hdescent : baseEnd_496326 < baseStart_496326 := by decide
  rcases family_descends (prefixWord ++ tailWord_496326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496330 : List Nat := [3, 1, 2, 1, 4, 1, 4, 3]
def baseStart_496330 : Nat := 118140960795 + 496330 * 2 ^ 59
def prefixEnd_496330 : Nat := 4983230072969 + 3 ^ 40 * 496330 * 2
def baseEnd_496330 : Nat := 151025690812532349802919

theorem tailTrace_496330 : CollatzResearch.WordTrace tailWord_496330 prefixEnd_496330 151025690812532349802919 := by
  unfold tailWord_496330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4525660572972162815127611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12068428194592434173673629 4525660572972162815127611)
  ·
    refine ⟨6788490859458244222691417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4525660572972162815127611 6788490859458244222691417)
    ·
      refine ⟨5091368144593683167018563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6788490859458244222691417 5091368144593683167018563)
      ·
        refine ⟨7637052216890524750527845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5091368144593683167018563 7637052216890524750527845)
        ·
          refine ⟨1431947290666973390723971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7637052216890524750527845 1431947290666973390723971)
          ·
            refine ⟨2147920936000460086085957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431947290666973390723971 2147920936000460086085957)
            ·
              refine ⟨402735175500086266141117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2147920936000460086085957 402735175500086266141117)
              ·
                refine ⟨151025690812532349802919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402735175500086266141117 151025690812532349802919)
                ·
                  rfl

theorem cell19_496330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_496330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496330 prefixEnd_496330 := by exact prefixLift 496330
  have htrace : WordTrace (prefixWord ++ tailWord_496330) baseStart_496330 baseEnd_496330 := by
    simpa [prefixWord, tailWord_496330, baseEnd_496330] using wordTrace_append hprefix tailTrace_496330
  have hstable : (prefixWord ++ tailWord_496330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496330).length < 2 ^ (prefixWord ++ tailWord_496330).sum := by decide
  have hdescent : baseEnd_496330 < baseStart_496330 := by decide
  rcases family_descends (prefixWord ++ tailWord_496330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496351 : List Nat := [1, 1, 2, 3, 2, 5, 5]
def baseStart_496351 : Nat := 118140960795 + 496351 * 2 ^ 59
def prefixEnd_496351 : Nat := 4983230072969 + 3 ^ 40 * 496351 * 2
def baseEnd_496351 : Nat := 50344026931336841112065

theorem tailTrace_496351 : CollatzResearch.WordTrace tailWord_496351 prefixEnd_496351 50344026931336841112065 := by
  unfold tailWord_496351
  simp only [CollatzResearch.WordTrace]
  refine ⟨18103408224812571847024907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12068938816541714564683271 18103408224812571847024907)
  ·
    refine ⟨27155112337218857770537361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18103408224812571847024907 27155112337218857770537361)
    ·
      refine ⟨20366334252914143327903021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27155112337218857770537361 20366334252914143327903021)
      ·
        refine ⟨7637375344842803747963633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20366334252914143327903021 7637375344842803747963633)
        ·
          refine ⟨5728031508632102810972725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7637375344842803747963633 5728031508632102810972725)
          ·
            refine ⟨537002953934259638528693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5728031508632102810972725 537002953934259638528693)
            ·
              refine ⟨50344026931336841112065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 537002953934259638528693 50344026931336841112065)
              ·
                rfl

theorem cell19_496351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_496351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496351 prefixEnd_496351 := by exact prefixLift 496351
  have htrace : WordTrace (prefixWord ++ tailWord_496351) baseStart_496351 baseEnd_496351 := by
    simpa [prefixWord, tailWord_496351, baseEnd_496351] using wordTrace_append hprefix tailTrace_496351
  have hstable : (prefixWord ++ tailWord_496351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496351).length < 2 ^ (prefixWord ++ tailWord_496351).sum := by decide
  have hdescent : baseEnd_496351 < baseStart_496351 := by decide
  rcases family_descends (prefixWord ++ tailWord_496351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496370 : List Nat := [3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_496370 : Nat := 118140960795 + 496370 * 2 ^ 59
def prefixEnd_496370 : Nat := 4983230072969 + 3 ^ 40 * 496370 * 2
def baseEnd_496370 : Nat := 151037862205824108913921

theorem tailTrace_496370 : CollatzResearch.WordTrace tailWord_496370 prefixEnd_496370 151037862205824108913921 := by
  unfold tailWord_496370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4526025302935934522991641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12069400807829158727977709 4526025302935934522991641)
  ·
    refine ⟨3394518977201950892243731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4526025302935934522991641 3394518977201950892243731)
    ·
      refine ⟨5091778465802926338365597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3394518977201950892243731 5091778465802926338365597)
      ·
        refine ⟨1909416924676097376887099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5091778465802926338365597 1909416924676097376887099)
        ·
          refine ⟨2864125387014146065330649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909416924676097376887099 2864125387014146065330649)
          ·
            refine ⟨2148094040260609548997987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864125387014146065330649 2148094040260609548997987)
            ·
              refine ⟨3222141060390914323496981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148094040260609548997987 3222141060390914323496981)
              ·
                refine ⟨151037862205824108913921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3222141060390914323496981 151037862205824108913921)
                ·
                  rfl

theorem cell19_496370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_496370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496370 prefixEnd_496370 := by exact prefixLift 496370
  have htrace : WordTrace (prefixWord ++ tailWord_496370) baseStart_496370 baseEnd_496370 := by
    simpa [prefixWord, tailWord_496370, baseEnd_496370] using wordTrace_append hprefix tailTrace_496370
  have hstable : (prefixWord ++ tailWord_496370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496370).length < 2 ^ (prefixWord ++ tailWord_496370).sum := by decide
  have hdescent : baseEnd_496370 < baseStart_496370 := by decide
  rcases family_descends (prefixWord ++ tailWord_496370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496448 : List Nat := [2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_496448 : Nat := 118140960795 + 496448 * 2 ^ 59
def prefixEnd_496448 : Nat := 4983230072969 + 3 ^ 40 * 496448 * 2
def baseEnd_496448 : Nat := 151061596422743039180375

theorem tailTrace_496448 : CollatzResearch.WordTrace tailWord_496448 prefixEnd_496448 151061596422743039180375 := by
  unfold tailWord_496448
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053473052730578706652999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12071297403640771608870665 9053473052730578706652999)
  ·
    refine ⟨13580209579095868059979499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9053473052730578706652999 13580209579095868059979499)
    ·
      refine ⟨20370314368643802089969249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13580209579095868059979499 20370314368643802089969249)
      ·
        refine ⟨15277735776482851567476937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20370314368643802089969249 15277735776482851567476937)
        ·
          refine ⟨11458301832362138675607703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15277735776482851567476937 11458301832362138675607703)
          ·
            refine ⟨17187452748543208013411555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11458301832362138675607703 17187452748543208013411555)
            ·
              refine ⟨25781179122814812020117333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17187452748543208013411555 25781179122814812020117333)
              ·
                refine ⟨151061596422743039180375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25781179122814812020117333 151061596422743039180375)
                ·
                  rfl

theorem cell19_496448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_496448 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496448 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496448 prefixEnd_496448 := by exact prefixLift 496448
  have htrace : WordTrace (prefixWord ++ tailWord_496448) baseStart_496448 baseEnd_496448 := by
    simpa [prefixWord, tailWord_496448, baseEnd_496448] using wordTrace_append hprefix tailTrace_496448
  have hstable : (prefixWord ++ tailWord_496448).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496448).length < 2 ^ (prefixWord ++ tailWord_496448).sum := by decide
  have hdescent : baseEnd_496448 < baseStart_496448 := by decide
  rcases family_descends (prefixWord ++ tailWord_496448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496465 : List Nat := [1, 2, 2, 1, 6, 1, 6]
def baseStart_496465 : Nat := 118140960795 + 496465 * 2 ^ 59
def prefixEnd_496465 : Nat := 4983230072969 + 3 ^ 40 * 496465 * 2
def baseEnd_496465 : Nat := 50355589754964012267517

theorem tailTrace_496465 : CollatzResearch.WordTrace tailWord_496465 prefixEnd_496465 50355589754964012267517 := by
  unfold tailWord_496465
  simp only [CollatzResearch.WordTrace]
  refine ⟨18107566146399569316674849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12071710764266379544449899 18107566146399569316674849)
  ·
    refine ⟨13580674609799676987506137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18107566146399569316674849 13580674609799676987506137)
    ·
      refine ⟨10185505957349757740629603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13580674609799676987506137 10185505957349757740629603)
      ·
        refine ⟨15278258936024636610944405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10185505957349757740629603 15278258936024636610944405)
        ·
          refine ⟨716168387626154841138019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15278258936024636610944405 716168387626154841138019)
          ·
            refine ⟨1074252581439232261707029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716168387626154841138019 1074252581439232261707029)
            ·
              refine ⟨50355589754964012267517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1074252581439232261707029 50355589754964012267517)
              ·
                rfl

theorem cell19_496465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_496465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496465 prefixEnd_496465 := by exact prefixLift 496465
  have htrace : WordTrace (prefixWord ++ tailWord_496465) baseStart_496465 baseEnd_496465 := by
    simpa [prefixWord, tailWord_496465, baseEnd_496465] using wordTrace_append hprefix tailTrace_496465
  have hstable : (prefixWord ++ tailWord_496465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496465).length < 2 ^ (prefixWord ++ tailWord_496465).sum := by decide
  have hdescent : baseEnd_496465 < baseStart_496465 := by decide
  rcases family_descends (prefixWord ++ tailWord_496465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496501 : List Nat := [1, 3, 4, 1, 1, 2, 4, 3]
def baseStart_496501 : Nat := 118140960795 + 496501 * 2 ^ 59
def prefixEnd_496501 : Nat := 4983230072969 + 3 ^ 40 * 496501 * 2
def baseEnd_496501 : Nat := 151077723518854620002453

theorem tailTrace_496501 : CollatzResearch.WordTrace tailWord_496501 prefixEnd_496501 151077723518854620002453 := by
  unfold tailWord_496501
  simp only [CollatzResearch.WordTrace]
  refine ⟨18108879174269147464985357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12072586116179431643323571 18108879174269147464985357)
  ·
    refine ⟨6790829690350930299369509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18108879174269147464985357 6790829690350930299369509)
    ·
      refine ⟨1273280566940799431131783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6790829690350930299369509 1273280566940799431131783)
      ·
        refine ⟨1909920850411199146697675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273280566940799431131783 1909920850411199146697675)
        ·
          refine ⟨2864881275616798720046513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909920850411199146697675 2864881275616798720046513)
          ·
            refine ⟨2148660956712599040034885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864881275616798720046513 2148660956712599040034885)
            ·
              refine ⟨402873929383612320006541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2148660956712599040034885 402873929383612320006541)
              ·
                refine ⟨151077723518854620002453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402873929383612320006541 151077723518854620002453)
                ·
                  rfl

theorem cell19_496501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 3].length) (baseStart_496501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496501 prefixEnd_496501 := by exact prefixLift 496501
  have htrace : WordTrace (prefixWord ++ tailWord_496501) baseStart_496501 baseEnd_496501 := by
    simpa [prefixWord, tailWord_496501, baseEnd_496501] using wordTrace_append hprefix tailTrace_496501
  have hstable : (prefixWord ++ tailWord_496501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496501).length < 2 ^ (prefixWord ++ tailWord_496501).sum := by decide
  have hdescent : baseEnd_496501 < baseStart_496501 := by decide
  rcases family_descends (prefixWord ++ tailWord_496501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496522 : List Nat := [3, 1, 2, 4, 1, 1, 7]
def baseStart_496522 : Nat := 118140960795 + 496522 * 2 ^ 59
def prefixEnd_496522 : Nat := 4983230072969 + 3 ^ 40 * 496522 * 2
def baseEnd_496522 : Nat := 50361371166777597845243

theorem tailTrace_496522 : CollatzResearch.WordTrace tailWord_496522 prefixEnd_496522 50361371166777597845243 := by
  unfold tailWord_496522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4527411276798267012874955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12073096738128712034333213 4527411276798267012874955)
  ·
    refine ⟨6791116915197400519312433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4527411276798267012874955 6791116915197400519312433)
    ·
      refine ⟨5093337686398050389484325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6791116915197400519312433 5093337686398050389484325)
      ·
        refine ⟨955000816199634448028311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5093337686398050389484325 955000816199634448028311)
        ·
          refine ⟨1432501224299451672042467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955000816199634448028311 1432501224299451672042467)
          ·
            refine ⟨2148751836449177508063701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432501224299451672042467 2148751836449177508063701)
            ·
              refine ⟨50361371166777597845243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2148751836449177508063701 50361371166777597845243)
              ·
                rfl

theorem cell19_496522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_496522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496522 prefixEnd_496522 := by exact prefixLift 496522
  have htrace : WordTrace (prefixWord ++ tailWord_496522) baseStart_496522 baseEnd_496522 := by
    simpa [prefixWord, tailWord_496522, baseEnd_496522] using wordTrace_append hprefix tailTrace_496522
  have hstable : (prefixWord ++ tailWord_496522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496522).length < 2 ^ (prefixWord ++ tailWord_496522).sum := by decide
  have hdescent : baseEnd_496522 < baseStart_496522 := by decide
  rcases family_descends (prefixWord ++ tailWord_496522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496524 : List Nat := [2, 2, 1, 2, 1, 2, 9]
def baseStart_496524 : Nat := 118140960795 + 496524 * 2 ^ 59
def prefixEnd_496524 : Nat := 4983230072969 + 3 ^ 40 * 496524 * 2
def baseEnd_496524 : Nat := 50361574023332460497093

theorem tailTrace_496524 : CollatzResearch.WordTrace tailWord_496524 prefixEnd_496524 50361574023332460497093 := by
  unfold tailWord_496524
  simp only [CollatzResearch.WordTrace]
  refine ⟨9054859026592911196536313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12073145368790548262048417 9054859026592911196536313)
  ·
    refine ⟨6791144269944683397402235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9054859026592911196536313 6791144269944683397402235)
    ·
      refine ⟨10186716404917025096103353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6791144269944683397402235 10186716404917025096103353)
      ·
        refine ⟨7640037303687768822077515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10186716404917025096103353 7640037303687768822077515)
        ·
          refine ⟨11460055955531653233116273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7640037303687768822077515 11460055955531653233116273)
          ·
            refine ⟨8595041966648739924837205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11460055955531653233116273 8595041966648739924837205)
            ·
              refine ⟨50361574023332460497093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8595041966648739924837205 50361574023332460497093)
              ·
                rfl

theorem cell19_496524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_496524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496524 prefixEnd_496524 := by exact prefixLift 496524
  have htrace : WordTrace (prefixWord ++ tailWord_496524) baseStart_496524 baseEnd_496524 := by
    simpa [prefixWord, tailWord_496524, baseEnd_496524] using wordTrace_append hprefix tailTrace_496524
  have hstable : (prefixWord ++ tailWord_496524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496524).length < 2 ^ (prefixWord ++ tailWord_496524).sum := by decide
  have hdescent : baseEnd_496524 < baseStart_496524 := by decide
  rcases family_descends (prefixWord ++ tailWord_496524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496541 : List Nat := [1, 4, 2, 1, 2, 1, 4, 4]
def baseStart_496541 : Nat := 118140960795 + 496541 * 2 ^ 59
def prefixEnd_496541 : Nat := 4983230072969 + 3 ^ 40 * 496541 * 2
def baseEnd_496541 : Nat := 151089894912146379113455

theorem tailTrace_496541 : CollatzResearch.WordTrace tailWord_496541 prefixEnd_496541 151089894912146379113455 := by
  unfold tailWord_496541
  simp only [CollatzResearch.WordTrace]
  refine ⟨18110338094124234296441477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12073558729416156197627651 18110338094124234296441477)
  ·
    refine ⟨3395688392648293930582777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18110338094124234296441477 3395688392648293930582777)
    ·
      refine ⟨2546766294486220447937083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3395688392648293930582777 2546766294486220447937083)
      ·
        refine ⟨3820149441729330671905625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2546766294486220447937083 3820149441729330671905625)
        ·
          refine ⟨2865112081296998003929219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3820149441729330671905625 2865112081296998003929219)
          ·
            refine ⟨4297668121945497005893829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865112081296998003929219 4297668121945497005893829)
            ·
              refine ⟨805812772864780688605093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4297668121945497005893829 805812772864780688605093)
              ·
                refine ⟨151089894912146379113455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 805812772864780688605093 151089894912146379113455)
                ·
                  rfl

theorem cell19_496541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_496541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496541 prefixEnd_496541 := by exact prefixLift 496541
  have htrace : WordTrace (prefixWord ++ tailWord_496541) baseStart_496541 baseEnd_496541 := by
    simpa [prefixWord, tailWord_496541, baseEnd_496541] using wordTrace_append hprefix tailTrace_496541
  have hstable : (prefixWord ++ tailWord_496541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496541).length < 2 ^ (prefixWord ++ tailWord_496541).sum := by decide
  have hdescent : baseEnd_496541 < baseStart_496541 := by decide
  rcases family_descends (prefixWord ++ tailWord_496541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496596 : List Nat := [2, 4, 1, 2, 1, 4, 1, 4]
def baseStart_496596 : Nat := 118140960795 + 496596 * 2 ^ 59
def prefixEnd_496596 : Nat := 4983230072969 + 3 ^ 40 * 496596 * 2
def baseEnd_496596 : Nat := 151106630577922547891083

theorem tailTrace_496596 : CollatzResearch.WordTrace tailWord_496596 prefixEnd_496596 151106630577922547891083 := by
  unfold tailWord_496596
  simp only [CollatzResearch.WordTrace]
  refine ⟨9056172054462489344846821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12074896072616652459795761 9056172054462489344846821)
  ·
    refine ⟨1698032260211716752158779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9056172054462489344846821 1698032260211716752158779)
    ·
      refine ⟨2547048390317575128238169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1698032260211716752158779 2547048390317575128238169)
      ·
        refine ⟨1910286292738181346178627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2547048390317575128238169 1910286292738181346178627)
        ·
          refine ⟨2865429439107272019267941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910286292738181346178627 2865429439107272019267941)
          ·
            refine ⟨537268019832613503612739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2865429439107272019267941 537268019832613503612739)
            ·
              refine ⟨805902029748920255419109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537268019832613503612739 805902029748920255419109)
              ·
                refine ⟨151106630577922547891083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 805902029748920255419109 151106630577922547891083)
                ·
                  rfl

theorem cell19_496596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_496596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496596 prefixEnd_496596 := by exact prefixLift 496596
  have htrace : WordTrace (prefixWord ++ tailWord_496596) baseStart_496596 baseEnd_496596 := by
    simpa [prefixWord, tailWord_496596, baseEnd_496596] using wordTrace_append hprefix tailTrace_496596
  have hstable : (prefixWord ++ tailWord_496596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496596).length < 2 ^ (prefixWord ++ tailWord_496596).sum := by decide
  have hdescent : baseEnd_496596 < baseStart_496596 := by decide
  rcases family_descends (prefixWord ++ tailWord_496596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496613 : List Nat := [1, 3, 1, 6, 1, 1, 3, 3]
def baseStart_496613 : Nat := 118140960795 + 496613 * 2 ^ 59
def prefixEnd_496613 : Nat := 4983230072969 + 3 ^ 40 * 496613 * 2
def baseEnd_496613 : Nat := 151111803420071545513259

theorem tailTrace_496613 : CollatzResearch.WordTrace tailWord_496613 prefixEnd_496613 151111803420071545513259 := by
  unfold tailWord_496613
  simp only [CollatzResearch.WordTrace]
  refine ⟨18112964149863390593062493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12075309433242260395374995 18112964149863390593062493)
  ·
    refine ⟨6792361556198771472398435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18112964149863390593062493 6792361556198771472398435)
    ·
      refine ⟨10188542334298157208597653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6792361556198771472398435 10188542334298157208597653)
      ·
        refine ⟨477587921920226119153015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10188542334298157208597653 477587921920226119153015)
        ·
          refine ⟨716381882880339178729523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477587921920226119153015 716381882880339178729523)
          ·
            refine ⟨1074572824320508768094285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716381882880339178729523 1074572824320508768094285)
            ·
              refine ⟨402964809120190788035357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1074572824320508768094285 402964809120190788035357)
              ·
                refine ⟨151111803420071545513259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402964809120190788035357 151111803420071545513259)
                ·
                  rfl

theorem cell19_496613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 3].length) (baseStart_496613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496613 prefixEnd_496613 := by exact prefixLift 496613
  have htrace : WordTrace (prefixWord ++ tailWord_496613) baseStart_496613 baseEnd_496613 := by
    simpa [prefixWord, tailWord_496613, baseEnd_496613] using wordTrace_append hprefix tailTrace_496613
  have hstable : (prefixWord ++ tailWord_496613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496613).length < 2 ^ (prefixWord ++ tailWord_496613).sum := by decide
  have hdescent : baseEnd_496613 < baseStart_496613 := by decide
  rcases family_descends (prefixWord ++ tailWord_496613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496615 : List Nat := [1, 1, 5, 2, 2, 2, 3, 3]
def baseStart_496615 : Nat := 118140960795 + 496615 * 2 ^ 59
def prefixEnd_496615 : Nat := 4983230072969 + 3 ^ 40 * 496615 * 2
def baseEnd_496615 : Nat := 151112411989736133468809

theorem tailTrace_496615 : CollatzResearch.WordTrace tailWord_496615 prefixEnd_496615 151112411989736133468809 := by
  unfold tailWord_496615
  simp only [CollatzResearch.WordTrace]
  refine ⟨18113037095856144934635299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12075358063904096623090199 18113037095856144934635299)
  ·
    refine ⟨27169555643784217401952949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18113037095856144934635299 27169555643784217401952949)
    ·
      refine ⟨2547145841604770381433089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27169555643784217401952949 2547145841604770381433089)
      ·
        refine ⟨1910359381203577786074817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2547145841604770381433089 1910359381203577786074817)
        ·
          refine ⟨1432769535902683339556113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1910359381203577786074817 1432769535902683339556113)
          ·
            refine ⟨1074577151927012504667085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1432769535902683339556113 1074577151927012504667085)
            ·
              refine ⟨402966431972629689250157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1074577151927012504667085 402966431972629689250157)
              ·
                refine ⟨151112411989736133468809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402966431972629689250157 151112411989736133468809)
                ·
                  rfl

theorem cell19_496615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 3].length) (baseStart_496615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496615 prefixEnd_496615 := by exact prefixLift 496615
  have htrace : WordTrace (prefixWord ++ tailWord_496615) baseStart_496615 baseEnd_496615 := by
    simpa [prefixWord, tailWord_496615, baseEnd_496615] using wordTrace_append hprefix tailTrace_496615
  have hstable : (prefixWord ++ tailWord_496615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496615).length < 2 ^ (prefixWord ++ tailWord_496615).sum := by decide
  have hdescent : baseEnd_496615 < baseStart_496615 := by decide
  rcases family_descends (prefixWord ++ tailWord_496615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496672 : List Nat := [2, 1, 1, 7, 1, 1, 1, 5]
def baseStart_496672 : Nat := 118140960795 + 496672 * 2 ^ 59
def prefixEnd_496672 : Nat := 4983230072969 + 3 ^ 40 * 496672 * 2
def baseEnd_496672 : Nat := 151129756225176890201987

theorem tailTrace_496672 : CollatzResearch.WordTrace tailWord_496672 prefixEnd_496672 151129756225176890201987 := by
  unfold tailWord_496672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9057558028324821834730135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12076744037766429112973513 9057558028324821834730135)
  ·
    refine ⟨13586337042487232752095203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9057558028324821834730135 13586337042487232752095203)
    ·
      refine ⟨20379505563730849128142805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13586337042487232752095203 20379505563730849128142805)
      ·
        refine ⟨477644661649941776440847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20379505563730849128142805 477644661649941776440847)
        ·
          refine ⟨716466992474912664661271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477644661649941776440847 716466992474912664661271)
          ·
            refine ⟨1074700488712368996991907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716466992474912664661271 1074700488712368996991907)
            ·
              refine ⟨1612050733068553495487861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074700488712368996991907 1612050733068553495487861)
              ·
                refine ⟨151129756225176890201987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1612050733068553495487861 151129756225176890201987)
                ·
                  rfl

theorem cell19_496672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_496672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496672 prefixEnd_496672 := by exact prefixLift 496672
  have htrace : WordTrace (prefixWord ++ tailWord_496672) baseStart_496672 baseEnd_496672 := by
    simpa [prefixWord, tailWord_496672, baseEnd_496672] using wordTrace_append hprefix tailTrace_496672
  have hstable : (prefixWord ++ tailWord_496672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496672).length < 2 ^ (prefixWord ++ tailWord_496672).sum := by decide
  have hdescent : baseEnd_496672 < baseStart_496672 := by decide
  rcases family_descends (prefixWord ++ tailWord_496672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496674 : List Nat := [3, 3, 1, 1, 1, 4, 1, 5]
def baseStart_496674 : Nat := 118140960795 + 496674 * 2 ^ 59
def prefixEnd_496674 : Nat := 4983230072969 + 3 ^ 40 * 496674 * 2
def baseEnd_496674 : Nat := 151130364794841478157537

theorem tailTrace_496674 : CollatzResearch.WordTrace tailWord_496674 prefixEnd_496674 151130364794841478157537 := by
  unfold tailWord_496674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4528797250660599502758269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12076792668428265340688717 4528797250660599502758269)
  ·
    refine ⟨1698298968997724813534351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4528797250660599502758269 1698298968997724813534351)
    ·
      refine ⟨2547448453496587220301527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1698298968997724813534351 2547448453496587220301527)
      ·
        refine ⟨3821172680244880830452291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547448453496587220301527 3821172680244880830452291)
        ·
          refine ⟨5731759020367321245678437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3821172680244880830452291 5731759020367321245678437)
          ·
            refine ⟨1074704816318872733564707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5731759020367321245678437 1074704816318872733564707)
            ·
              refine ⟨1612057224478309100347061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074704816318872733564707 1612057224478309100347061)
              ·
                refine ⟨151130364794841478157537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1612057224478309100347061 151130364794841478157537)
                ·
                  rfl

theorem cell19_496674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_496674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496674 prefixEnd_496674 := by exact prefixLift 496674
  have htrace : WordTrace (prefixWord ++ tailWord_496674) baseStart_496674 baseEnd_496674 := by
    simpa [prefixWord, tailWord_496674, baseEnd_496674] using wordTrace_append hprefix tailTrace_496674
  have hstable : (prefixWord ++ tailWord_496674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496674).length < 2 ^ (prefixWord ++ tailWord_496674).sum := by decide
  have hdescent : baseEnd_496674 < baseStart_496674 := by decide
  rcases family_descends (prefixWord ++ tailWord_496674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496710 : List Nat := [6, 1, 1, 1, 1, 2, 1, 6]
def baseStart_496710 : Nat := 118140960795 + 496710 * 2 ^ 59
def prefixEnd_496710 : Nat := 4983230072969 + 3 ^ 40 * 496710 * 2
def baseEnd_496710 : Nat := 151141319048804061357439

theorem tailTrace_496710 : CollatzResearch.WordTrace tailWord_496710 prefixEnd_496710 151141319048804061357439 := by
  unfold tailWord_496710
  simp only [CollatzResearch.WordTrace]
  refine ⟨566140688453499254979487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12077668020341317439562389 566140688453499254979487)
  ·
    refine ⟨849211032680248882469231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 566140688453499254979487 849211032680248882469231)
    ·
      refine ⟨1273816549020373323703847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849211032680248882469231 1273816549020373323703847)
      ·
        refine ⟨1910724823530559985555771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273816549020373323703847 1910724823530559985555771)
        ·
          refine ⟨2866087235295839978333657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910724823530559985555771 2866087235295839978333657)
          ·
            refine ⟨2149565426471879983750243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2866087235295839978333657 2149565426471879983750243)
            ·
              refine ⟨3224348139707819975625365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149565426471879983750243 3224348139707819975625365)
              ·
                refine ⟨151141319048804061357439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3224348139707819975625365 151141319048804061357439)
                ·
                  rfl

theorem cell19_496710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_496710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496710 prefixEnd_496710 := by exact prefixLift 496710
  have htrace : WordTrace (prefixWord ++ tailWord_496710) baseStart_496710 baseEnd_496710 := by
    simpa [prefixWord, tailWord_496710, baseEnd_496710] using wordTrace_append hprefix tailTrace_496710
  have hstable : (prefixWord ++ tailWord_496710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496710).length < 2 ^ (prefixWord ++ tailWord_496710).sum := by decide
  have hdescent : baseEnd_496710 < baseStart_496710 := by decide
  rcases family_descends (prefixWord ++ tailWord_496710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496714 : List Nat := [3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_496714 : Nat := 118140960795 + 496714 * 2 ^ 59
def prefixEnd_496714 : Nat := 4983230072969 + 3 ^ 40 * 496714 * 2
def baseEnd_496714 : Nat := 151142536188133237268539

theorem tailTrace_496714 : CollatzResearch.WordTrace tailWord_496714 prefixEnd_496714 151142536188133237268539 := by
  unfold tailWord_496714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4529161980624371210622299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12077765281664989894992797 4529161980624371210622299)
  ·
    refine ⟨6793742970936556815933449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4529161980624371210622299 6793742970936556815933449)
    ·
      refine ⟨5095307228202417611950087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6793742970936556815933449 5095307228202417611950087)
      ·
        refine ⟨7642960842303626417925131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5095307228202417611950087 7642960842303626417925131)
        ·
          refine ⟨11464441263455439626887697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7642960842303626417925131 11464441263455439626887697)
          ·
            refine ⟨8598330947591579720165773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11464441263455439626887697 8598330947591579720165773)
            ·
              refine ⟨3224374105346842395062165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8598330947591579720165773 3224374105346842395062165)
              ·
                refine ⟨151142536188133237268539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3224374105346842395062165 151142536188133237268539)
                ·
                  rfl

theorem cell19_496714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_496714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496714 prefixEnd_496714 := by exact prefixLift 496714
  have htrace : WordTrace (prefixWord ++ tailWord_496714) baseStart_496714 baseEnd_496714 := by
    simpa [prefixWord, tailWord_496714, baseEnd_496714] using wordTrace_append hprefix tailTrace_496714
  have hstable : (prefixWord ++ tailWord_496714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496714).length < 2 ^ (prefixWord ++ tailWord_496714).sum := by decide
  have hdescent : baseEnd_496714 < baseStart_496714 := by decide
  rcases family_descends (prefixWord ++ tailWord_496714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496769 : List Nat := [1, 2, 4, 2, 2, 1, 3, 4]
def baseStart_496769 : Nat := 118140960795 + 496769 * 2 ^ 59
def prefixEnd_496769 : Nat := 4983230072969 + 3 ^ 40 * 496769 * 2
def baseEnd_496769 : Nat := 151159271853909406046167

theorem tailTrace_496769 : CollatzResearch.WordTrace tailWord_496769 prefixEnd_496769 151159271853909406046167 := by
  unfold tailWord_496769
  simp only [CollatzResearch.WordTrace]
  refine ⟨18118653937298229235741361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12079102624865486157160907 18118653937298229235741361)
  ·
    refine ⟨13588990452973671926806021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18118653937298229235741361 13588990452973671926806021)
    ·
      refine ⟨2547935709932563486276129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13588990452973671926806021 2547935709932563486276129)
      ·
        refine ⟨1910951782449422614707097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2547935709932563486276129 1910951782449422614707097)
        ·
          refine ⟨1433213836837066961030323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1910951782449422614707097 1433213836837066961030323)
          ·
            refine ⟨2149820755255600441545485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433213836837066961030323 2149820755255600441545485)
            ·
              refine ⟨806182783220850165579557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2149820755255600441545485 806182783220850165579557)
              ·
                refine ⟨151159271853909406046167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 806182783220850165579557 151159271853909406046167)
                ·
                  rfl

theorem cell19_496769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_496769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496769 prefixEnd_496769 := by exact prefixLift 496769
  have htrace : WordTrace (prefixWord ++ tailWord_496769) baseStart_496769 baseEnd_496769 := by
    simpa [prefixWord, tailWord_496769, baseEnd_496769] using wordTrace_append hprefix tailTrace_496769
  have hstable : (prefixWord ++ tailWord_496769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496769).length < 2 ^ (prefixWord ++ tailWord_496769).sum := by decide
  have hdescent : baseEnd_496769 < baseStart_496769 := by decide
  rcases family_descends (prefixWord ++ tailWord_496769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496786 : List Nat := [3, 2, 3, 1, 1, 3, 3, 3]
def baseStart_496786 : Nat := 118140960795 + 496786 * 2 ^ 59
def prefixEnd_496786 : Nat := 4983230072969 + 3 ^ 40 * 496786 * 2
def baseEnd_496786 : Nat := 151164444696058403668343

theorem tailTrace_496786 : CollatzResearch.WordTrace tailWord_496786 prefixEnd_496786 151164444696058403668343 := by
  unfold tailWord_496786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4529818494559160284777553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12079515985491094092740141 4529818494559160284777553)
  ·
    refine ⟨3397363870919370213583165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4529818494559160284777553 3397363870919370213583165)
    ·
      refine ⟨1274011451594763830093687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3397363870919370213583165 1274011451594763830093687)
      ·
        refine ⟨1911017177392145745140531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274011451594763830093687 1911017177392145745140531)
        ·
          refine ⟨2866525766088218617710797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911017177392145745140531 2866525766088218617710797)
          ·
            refine ⟨1074947162283081981641549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2866525766088218617710797 1074947162283081981641549)
            ·
              refine ⟨403105185856155743115581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1074947162283081981641549 403105185856155743115581)
              ·
                refine ⟨151164444696058403668343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403105185856155743115581 151164444696058403668343)
                ·
                  rfl

theorem cell19_496786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_496786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496786 prefixEnd_496786 := by exact prefixLift 496786
  have htrace : WordTrace (prefixWord ++ tailWord_496786) baseStart_496786 baseEnd_496786 := by
    simpa [prefixWord, tailWord_496786, baseEnd_496786] using wordTrace_append hprefix tailTrace_496786
  have hstable : (prefixWord ++ tailWord_496786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496786).length < 2 ^ (prefixWord ++ tailWord_496786).sum := by decide
  have hdescent : baseEnd_496786 < baseStart_496786 := by decide
  rcases family_descends (prefixWord ++ tailWord_496786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496807 : List Nat := [1, 1, 6, 2, 1, 2, 6]
def baseStart_496807 : Nat := 118140960795 + 496807 * 2 ^ 59
def prefixEnd_496807 : Nat := 4983230072969 + 3 ^ 40 * 496807 * 2
def baseEnd_496807 : Nat := 50390278225845525733873

theorem tailTrace_496807 : CollatzResearch.WordTrace tailWord_496807 prefixEnd_496807 50390278225845525733873 := by
  unfold tailWord_496807
  simp only [CollatzResearch.WordTrace]
  refine ⟨18120039911160561725624675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12080026607440374483749783 18120039911160561725624675)
  ·
    refine ⟨27180059866740842588437013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18120039911160561725624675 27180059866740842588437013)
    ·
      refine ⟨1274065306253476996332985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27180059866740842588437013 1274065306253476996332985)
      ·
        refine ⟨955548979690107747249739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1274065306253476996332985 955548979690107747249739)
        ·
          refine ⟨1433323469535161620874609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955548979690107747249739 1433323469535161620874609)
          ·
            refine ⟨1074992602151371215655957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1433323469535161620874609 1074992602151371215655957)
            ·
              refine ⟨50390278225845525733873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1074992602151371215655957 50390278225845525733873)
              ·
                rfl

theorem cell19_496807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_496807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496807 prefixEnd_496807 := by exact prefixLift 496807
  have htrace : WordTrace (prefixWord ++ tailWord_496807) baseStart_496807 baseEnd_496807 := by
    simpa [prefixWord, tailWord_496807, baseEnd_496807] using wordTrace_append hprefix tailTrace_496807
  have hstable : (prefixWord ++ tailWord_496807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496807).length < 2 ^ (prefixWord ++ tailWord_496807).sum := by decide
  have hdescent : baseEnd_496807 < baseStart_496807 := by decide
  rcases family_descends (prefixWord ++ tailWord_496807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496938 : List Nat := [3, 1, 4, 2, 1, 3, 1, 4]
def baseStart_496938 : Nat := 118140960795 + 496938 * 2 ^ 59
def prefixEnd_496938 : Nat := 4983230072969 + 3 ^ 40 * 496938 * 2
def baseEnd_496938 : Nat := 151210695990567088290151

theorem tailTrace_496938 : CollatzResearch.WordTrace tailWord_496938 prefixEnd_496938 151210695990567088290151 := by
  unfold tailWord_496938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4531204468421492774660867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12083211915790647399095645 4531204468421492774660867)
  ·
    refine ⟨6796806702632239161991301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4531204468421492774660867 6796806702632239161991301)
    ·
      refine ⟨1274401256743544842873369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6796806702632239161991301 1274401256743544842873369)
      ·
        refine ⟨955800942557658632155027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1274401256743544842873369 955800942557658632155027)
        ·
          refine ⟨1433701413836487948232541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955800942557658632155027 1433701413836487948232541)
          ·
            refine ⟨537638030188682980587203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1433701413836487948232541 537638030188682980587203)
            ·
              refine ⟨806457045283024470880805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537638030188682980587203 806457045283024470880805)
              ·
                refine ⟨151210695990567088290151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 806457045283024470880805 151210695990567088290151)
                ·
                  rfl

theorem cell19_496938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_496938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496938 prefixEnd_496938 := by exact prefixLift 496938
  have htrace : WordTrace (prefixWord ++ tailWord_496938) baseStart_496938 baseEnd_496938 := by
    simpa [prefixWord, tailWord_496938, baseEnd_496938] using wordTrace_append hprefix tailTrace_496938
  have hstable : (prefixWord ++ tailWord_496938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496938).length < 2 ^ (prefixWord ++ tailWord_496938).sum := by decide
  have hdescent : baseEnd_496938 < baseStart_496938 := by decide
  rcases family_descends (prefixWord ++ tailWord_496938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496959 : List Nat := [1, 1, 2, 2, 4, 3, 3, 3]
def baseStart_496959 : Nat := 118140960795 + 496959 * 2 ^ 59
def prefixEnd_496959 : Nat := 4983230072969 + 3 ^ 40 * 496959 * 2
def baseEnd_496959 : Nat := 151217085972045261823427

theorem tailTrace_496959 : CollatzResearch.WordTrace tailWord_496959 prefixEnd_496959 151217085972045261823427 := by
  unfold tailWord_496959
  simp only [CollatzResearch.WordTrace]
  refine ⟨18125583806609891685157931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12083722537739927790105287 18125583806609891685157931)
  ·
    refine ⟨27188375709914837527736897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18125583806609891685157931 27188375709914837527736897)
    ·
      refine ⟨20391281782436128145802673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27188375709914837527736897 20391281782436128145802673)
      ·
        refine ⟨15293461336827096109352005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20391281782436128145802673 15293461336827096109352005)
        ·
          refine ⟨2867524000655080520503501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15293461336827096109352005 2867524000655080520503501)
          ·
            refine ⟨1075321500245655195188813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2867524000655080520503501 1075321500245655195188813)
            ·
              refine ⟨403245562592120698195805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1075321500245655195188813 403245562592120698195805)
              ·
                refine ⟨151217085972045261823427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403245562592120698195805 151217085972045261823427)
                ·
                  rfl

theorem cell19_496959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 3].length) (baseStart_496959 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496959 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496959 prefixEnd_496959 := by exact prefixLift 496959
  have htrace : WordTrace (prefixWord ++ tailWord_496959) baseStart_496959 baseEnd_496959 := by
    simpa [prefixWord, tailWord_496959, baseEnd_496959] using wordTrace_append hprefix tailTrace_496959
  have hstable : (prefixWord ++ tailWord_496959).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496959).length < 2 ^ (prefixWord ++ tailWord_496959).sum := by decide
  have hdescent : baseEnd_496959 < baseStart_496959 := by decide
  rcases family_descends (prefixWord ++ tailWord_496959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496980 : List Nat := [2, 4, 1, 1, 2, 1, 8]
def baseStart_496980 : Nat := 118140960795 + 496980 * 2 ^ 59
def prefixEnd_496980 : Nat := 4983230072969 + 3 ^ 40 * 496980 * 2
def baseEnd_496980 : Nat := 50407825317841145118901

theorem tailTrace_496980 : CollatzResearch.WordTrace tailWord_496980 prefixEnd_496980 50407825317841145118901 := by
  unfold tailWord_496980
  simp only [CollatzResearch.WordTrace]
  refine ⟨9063174869766906135836197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12084233159689208181114929 9063174869766906135836197)
  ·
    refine ⟨1699345288081294900469287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9063174869766906135836197 1699345288081294900469287)
    ·
      refine ⟨2549017932121942350703931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1699345288081294900469287 2549017932121942350703931)
      ·
        refine ⟨3823526898182913526055897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2549017932121942350703931 3823526898182913526055897)
        ·
          refine ⟨2867645173637185144541923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3823526898182913526055897 2867645173637185144541923)
          ·
            refine ⟨4301467760455777716812885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867645173637185144541923 4301467760455777716812885)
            ·
              refine ⟨50407825317841145118901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4301467760455777716812885 50407825317841145118901)
              ·
                rfl

theorem cell19_496980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_496980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_496980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_496980 prefixEnd_496980 := by exact prefixLift 496980
  have htrace : WordTrace (prefixWord ++ tailWord_496980) baseStart_496980 baseEnd_496980 := by
    simpa [prefixWord, tailWord_496980, baseEnd_496980] using wordTrace_append hprefix tailTrace_496980
  have hstable : (prefixWord ++ tailWord_496980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496980).length < 2 ^ (prefixWord ++ tailWord_496980).sum := by decide
  have hdescent : baseEnd_496980 < baseStart_496980 := by decide
  rcases family_descends (prefixWord ++ tailWord_496980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497052 : List Nat := [2, 2, 3, 4, 1, 1, 2, 4]
def baseStart_497052 : Nat := 118140960795 + 497052 * 2 ^ 59
def prefixEnd_497052 : Nat := 4983230072969 + 3 ^ 40 * 497052 * 2
def baseEnd_497052 : Nat := 151245384461448601756507

theorem tailTrace_497052 : CollatzResearch.WordTrace tailWord_497052 prefixEnd_497052 151245384461448601756507 := by
  unfold tailWord_497052
  simp only [CollatzResearch.WordTrace]
  refine ⟨9064487897636484284146705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12085983863515312378862273 9064487897636484284146705)
  ·
    refine ⟨6798365923227363213110029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9064487897636484284146705 6798365923227363213110029)
    ·
      refine ⟨2549387221210261204916261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6798365923227363213110029 2549387221210261204916261)
      ·
        refine ⟨478010103976923975921799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2549387221210261204916261 478010103976923975921799)
        ·
          refine ⟨717015155965385963882699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478010103976923975921799 717015155965385963882699)
          ·
            refine ⟨1075522733948078945824049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717015155965385963882699 1075522733948078945824049)
            ·
              refine ⟨806642050461059209368037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075522733948078945824049 806642050461059209368037)
              ·
                refine ⟨151245384461448601756507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 806642050461059209368037 151245384461448601756507)
                ·
                  rfl

theorem cell19_497052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_497052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497052 prefixEnd_497052 := by exact prefixLift 497052
  have htrace : WordTrace (prefixWord ++ tailWord_497052) baseStart_497052 baseEnd_497052 := by
    simpa [prefixWord, tailWord_497052, baseEnd_497052] using wordTrace_append hprefix tailTrace_497052
  have hstable : (prefixWord ++ tailWord_497052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497052).length < 2 ^ (prefixWord ++ tailWord_497052).sum := by decide
  have hdescent : baseEnd_497052 < baseStart_497052 := by decide
  rcases family_descends (prefixWord ++ tailWord_497052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497056 : List Nat := [2, 1, 1, 4, 1, 2, 4, 4]
def baseStart_497056 : Nat := 118140960795 + 497056 * 2 ^ 59
def prefixEnd_497056 : Nat := 4983230072969 + 3 ^ 40 * 497056 * 2
def baseEnd_497056 : Nat := 151246601600777777667607

theorem tailTrace_497056 : CollatzResearch.WordTrace tailWord_497056 prefixEnd_497056 151246601600777777667607 := by
  unfold tailWord_497056
  simp only [CollatzResearch.WordTrace]
  refine ⟨9064560843629238625719511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12086081124838984834292681 9064560843629238625719511)
  ·
    refine ⟨13596841265443857938579267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9064560843629238625719511 13596841265443857938579267)
    ·
      refine ⟨20395261898165786907868901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13596841265443857938579267 20395261898165786907868901)
      ·
        refine ⟨3824111605906085045225419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20395261898165786907868901 3824111605906085045225419)
        ·
          refine ⟨5736167408859127567838129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3824111605906085045225419 5736167408859127567838129)
          ·
            refine ⟨4302125556644345675878597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5736167408859127567838129 4302125556644345675878597)
            ·
              refine ⟨806648541870814814227237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4302125556644345675878597 806648541870814814227237)
              ·
                refine ⟨151246601600777777667607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 806648541870814814227237 151246601600777777667607)
                ·
                  rfl

theorem cell19_497056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_497056 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497056 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497056 prefixEnd_497056 := by exact prefixLift 497056
  have htrace : WordTrace (prefixWord ++ tailWord_497056) baseStart_497056 baseEnd_497056 := by
    simpa [prefixWord, tailWord_497056, baseEnd_497056] using wordTrace_append hprefix tailTrace_497056
  have hstable : (prefixWord ++ tailWord_497056).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497056).length < 2 ^ (prefixWord ++ tailWord_497056).sum := by decide
  have hdescent : baseEnd_497056 < baseStart_497056 := by decide
  rcases family_descends (prefixWord ++ tailWord_497056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497113 : List Nat := [1, 2, 1, 2, 4, 2, 3, 4]
def baseStart_497113 : Nat := 118140960795 + 497113 * 2 ^ 59
def prefixEnd_497113 : Nat := 4983230072969 + 3 ^ 40 * 497113 * 2
def baseEnd_497113 : Nat := 151263945836218534400785

theorem tailTrace_497113 : CollatzResearch.WordTrace tailWord_497113 prefixEnd_497113 151263945836218534400785 := by
  unfold tailWord_497113
  simp only [CollatzResearch.WordTrace]
  refine ⟨18131200648051975986263993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12087467098701317324175995 18131200648051975986263993)
  ·
    refine ⟨13598400486038981989697995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18131200648051975986263993 13598400486038981989697995)
    ·
      refine ⟨20397600729058472984546993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13598400486038981989697995 20397600729058472984546993)
      ·
        refine ⟨15298200546793854738410245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20397600729058472984546993 15298200546793854738410245)
        ·
          refine ⟨2868412602523847763451921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15298200546793854738410245 2868412602523847763451921)
          ·
            refine ⟨2151309451892885822588941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868412602523847763451921 2151309451892885822588941)
            ·
              refine ⟨806741044459832183470853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2151309451892885822588941 806741044459832183470853)
              ·
                refine ⟨151263945836218534400785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 806741044459832183470853 151263945836218534400785)
                ·
                  rfl

theorem cell19_497113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_497113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497113 prefixEnd_497113 := by exact prefixLift 497113
  have htrace : WordTrace (prefixWord ++ tailWord_497113) baseStart_497113 baseEnd_497113 := by
    simpa [prefixWord, tailWord_497113, baseEnd_497113] using wordTrace_append hprefix tailTrace_497113
  have hstable : (prefixWord ++ tailWord_497113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497113).length < 2 ^ (prefixWord ++ tailWord_497113).sum := by decide
  have hdescent : baseEnd_497113 < baseStart_497113 := by decide
  rcases family_descends (prefixWord ++ tailWord_497113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497208 : List Nat := [2, 1, 2, 1, 4, 4, 5]
def baseStart_497208 : Nat := 118140960795 + 497208 * 2 ^ 59
def prefixEnd_497208 : Nat := 4983230072969 + 3 ^ 40 * 497208 * 2
def baseEnd_497208 : Nat := 50430950965095487429805

theorem tailTrace_497208 : CollatzResearch.WordTrace tailWord_497208 prefixEnd_497208 50430950965095487429805 := by
  unfold tailWord_497208
  simp only [CollatzResearch.WordTrace]
  refine ⟨9067332791353903605486139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12089777055138538140648185 9067332791353903605486139)
  ·
    refine ⟨13600999187030855408229209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9067332791353903605486139 13600999187030855408229209)
    ·
      refine ⟨10200749390273141556171907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13600999187030855408229209 10200749390273141556171907)
      ·
        refine ⟨15301124085409712334257861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10200749390273141556171907 15301124085409712334257861)
        ·
          refine ⟨2868960766014321062673349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15301124085409712334257861 2868960766014321062673349)
          ·
            refine ⟨537930143627685199251253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2868960766014321062673349 537930143627685199251253)
            ·
              refine ⟨50430950965095487429805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 537930143627685199251253 50430950965095487429805)
              ·
                rfl

theorem cell19_497208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_497208 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497208 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497208 prefixEnd_497208 := by exact prefixLift 497208
  have htrace : WordTrace (prefixWord ++ tailWord_497208) baseStart_497208 baseEnd_497208 := by
    simpa [prefixWord, tailWord_497208, baseEnd_497208] using wordTrace_append hprefix tailTrace_497208
  have hstable : (prefixWord ++ tailWord_497208).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497208).length < 2 ^ (prefixWord ++ tailWord_497208).sum := by decide
  have hdescent : baseEnd_497208 < baseStart_497208 := by decide
  rcases family_descends (prefixWord ++ tailWord_497208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497343 : List Nat := [1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_497343 : Nat := 118140960795 + 497343 * 2 ^ 59
def prefixEnd_497343 : Nat := 4983230072969 + 3 ^ 40 * 497343 * 2
def baseEnd_497343 : Nat := 151333931347646149289047

theorem tailTrace_497343 : CollatzResearch.WordTrace tailWord_497343 prefixEnd_497343 151333931347646149289047 := by
  unfold tailWord_497343
  simp only [CollatzResearch.WordTrace]
  refine ⟨18139589437218725267136683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12093059624812483511424455 18139589437218725267136683)
  ·
    refine ⟨27209384155828087900705025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18139589437218725267136683 27209384155828087900705025)
    ·
      refine ⟨20407038116871065925528769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27209384155828087900705025 20407038116871065925528769)
      ·
        refine ⟨15305278587653299444146577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20407038116871065925528769 15305278587653299444146577)
        ·
          refine ⟨11478958940739974583109933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15305278587653299444146577 11478958940739974583109933)
          ·
            refine ⟨4304609602777490468666225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11478958940739974583109933 4304609602777490468666225)
            ·
              refine ⟨3228457202083117851499669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4304609602777490468666225 3228457202083117851499669)
              ·
                refine ⟨151333931347646149289047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3228457202083117851499669 151333931347646149289047)
                ·
                  rfl

theorem cell19_497343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_497343 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497343 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497343 prefixEnd_497343 := by exact prefixLift 497343
  have htrace : WordTrace (prefixWord ++ tailWord_497343) baseStart_497343 baseEnd_497343 := by
    simpa [prefixWord, tailWord_497343, baseEnd_497343] using wordTrace_append hprefix tailTrace_497343
  have hstable : (prefixWord ++ tailWord_497343).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497343).length < 2 ^ (prefixWord ++ tailWord_497343).sum := by decide
  have hdescent : baseEnd_497343 < baseStart_497343 := by decide
  rcases family_descends (prefixWord ++ tailWord_497343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497356 : List Nat := [2, 2, 1, 5, 2, 2, 2, 3]
def baseStart_497356 : Nat := 118140960795 + 497356 * 2 ^ 59
def prefixEnd_497356 : Nat := 4983230072969 + 3 ^ 40 * 497356 * 2
def baseEnd_497356 : Nat := 151337887050465971000123

theorem tailTrace_497356 : CollatzResearch.WordTrace tailWord_497356 prefixEnd_497356 151337887050465971000123 := by
  unfold tailWord_497356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9070031793085814243679961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12093375724114418991573281 9070031793085814243679961)
  ·
    refine ⟨6802523844814360682759971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9070031793085814243679961 6802523844814360682759971)
    ·
      refine ⟨10203785767221541024139957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6802523844814360682759971 10203785767221541024139957)
      ·
        refine ⟨956604915677019471013121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10203785767221541024139957 956604915677019471013121)
        ·
          refine ⟨717453686757764603259841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956604915677019471013121 717453686757764603259841)
          ·
            refine ⟨538090265068323452444881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717453686757764603259841 538090265068323452444881)
            ·
              refine ⟨403567698801242589333661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538090265068323452444881 403567698801242589333661)
              ·
                refine ⟨151337887050465971000123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403567698801242589333661 151337887050465971000123)
                ·
                  rfl

theorem cell19_497356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_497356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497356 prefixEnd_497356 := by exact prefixLift 497356
  have htrace : WordTrace (prefixWord ++ tailWord_497356) baseStart_497356 baseEnd_497356 := by
    simpa [prefixWord, tailWord_497356, baseEnd_497356] using wordTrace_append hprefix tailTrace_497356
  have hstable : (prefixWord ++ tailWord_497356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497356).length < 2 ^ (prefixWord ++ tailWord_497356).sum := by decide
  have hdescent : baseEnd_497356 < baseStart_497356 := by decide
  rcases family_descends (prefixWord ++ tailWord_497356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497377 : List Nat := [1, 2, 3, 1, 6, 1, 5]
def baseStart_497377 : Nat := 118140960795 + 497377 * 2 ^ 59
def prefixEnd_497377 : Nat := 4983230072969 + 3 ^ 40 * 497377 * 2
def baseEnd_497377 : Nat := 50448092343981381511133

theorem tailTrace_497377 : CollatzResearch.WordTrace tailWord_497377 prefixEnd_497377 50448092343981381511133 := by
  unfold tailWord_497377
  simp only [CollatzResearch.WordTrace]
  refine ⟨18140829519095549073874385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12093886346063699382582923 18140829519095549073874385)
  ·
    refine ⟨13605622139321661805405789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18140829519095549073874385 13605622139321661805405789)
    ·
      refine ⟨5102108302245623177027171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13605622139321661805405789 5102108302245623177027171)
      ·
        refine ⟨7653162453368434765540757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5102108302245623177027171 7653162453368434765540757)
        ·
          refine ⟨358741990001645379634723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7653162453368434765540757 358741990001645379634723)
          ·
            refine ⟨538112985002468069452085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358741990001645379634723 538112985002468069452085)
            ·
              refine ⟨50448092343981381511133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 538112985002468069452085 50448092343981381511133)
              ·
                rfl

theorem cell19_497377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 5].length) (baseStart_497377 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497377 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497377 prefixEnd_497377 := by exact prefixLift 497377
  have htrace : WordTrace (prefixWord ++ tailWord_497377) baseStart_497377 baseEnd_497377 := by
    simpa [prefixWord, tailWord_497377, baseEnd_497377] using wordTrace_append hprefix tailTrace_497377
  have hstable : (prefixWord ++ tailWord_497377).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497377).length < 2 ^ (prefixWord ++ tailWord_497377).sum := by decide
  have hdescent : baseEnd_497377 < baseStart_497377 := by decide
  rcases family_descends (prefixWord ++ tailWord_497377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497398 : List Nat := [5, 1, 1, 1, 1, 3, 1, 6]
def baseStart_497398 : Nat := 118140960795 + 497398 * 2 ^ 59
def prefixEnd_497398 : Nat := 4983230072969 + 3 ^ 40 * 497398 * 2
def baseEnd_497398 : Nat := 151350667013422318066675

theorem tailTrace_497398 : CollatzResearch.WordTrace tailWord_497398 prefixEnd_497398 151350667013422318066675 := by
  unfold tailWord_497398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133849715751216853774303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12094396968012979773592565 1133849715751216853774303)
  ·
    refine ⟨1700774573626825280661455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1133849715751216853774303 1700774573626825280661455)
    ·
      refine ⟨2551161860440237920992183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700774573626825280661455 2551161860440237920992183)
      ·
        refine ⟨3826742790660356881488275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551161860440237920992183 3826742790660356881488275)
        ·
          refine ⟨5740114185990535322232413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826742790660356881488275 5740114185990535322232413)
          ·
            refine ⟨2152542819746450745837155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5740114185990535322232413 2152542819746450745837155)
            ·
              refine ⟨3228814229619676118755733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152542819746450745837155 3228814229619676118755733)
              ·
                refine ⟨151350667013422318066675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3228814229619676118755733 151350667013422318066675)
                ·
                  rfl

theorem cell19_497398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_497398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497398 prefixEnd_497398 := by exact prefixLift 497398
  have htrace : WordTrace (prefixWord ++ tailWord_497398) baseStart_497398 baseEnd_497398 := by
    simpa [prefixWord, tailWord_497398, baseEnd_497398] using wordTrace_append hprefix tailTrace_497398
  have hstable : (prefixWord ++ tailWord_497398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497398).length < 2 ^ (prefixWord ++ tailWord_497398).sum := by decide
  have hdescent : baseEnd_497398 < baseStart_497398 := by decide
  rcases family_descends (prefixWord ++ tailWord_497398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497419 : List Nat := [1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_497419 : Nat := 118140960795 + 497419 * 2 ^ 59
def prefixEnd_497419 : Nat := 4983230072969 + 3 ^ 40 * 497419 * 2
def baseEnd_497419 : Nat := 151357056994900491599951

theorem tailTrace_497419 : CollatzResearch.WordTrace tailWord_497419 prefixEnd_497419 151357056994900491599951 := by
  unfold tailWord_497419
  simp only [CollatzResearch.WordTrace]
  refine ⟨18142361384943390246903311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12094907589962260164602207 18142361384943390246903311)
  ·
    refine ⟨27213542077415085370354967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18142361384943390246903311 27213542077415085370354967)
    ·
      refine ⟨40820313116122628055532451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27213542077415085370354967 40820313116122628055532451)
      ·
        refine ⟨61230469674183942083298677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40820313116122628055532451 61230469674183942083298677)
        ·
          refine ⟨5740356531954744570309251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61230469674183942083298677 5740356531954744570309251)
          ·
            refine ⟨8610534797932116855463877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740356531954744570309251 8610534797932116855463877)
            ·
              refine ⟨1614475274612271910399477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8610534797932116855463877 1614475274612271910399477)
              ·
                refine ⟨151357056994900491599951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1614475274612271910399477 151357056994900491599951)
                ·
                  rfl

theorem cell19_497419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_497419 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497419 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497419 prefixEnd_497419 := by exact prefixLift 497419
  have htrace : WordTrace (prefixWord ++ tailWord_497419) baseStart_497419 baseEnd_497419 := by
    simpa [prefixWord, tailWord_497419, baseEnd_497419] using wordTrace_append hprefix tailTrace_497419
  have hstable : (prefixWord ++ tailWord_497419).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497419).length < 2 ^ (prefixWord ++ tailWord_497419).sum := by decide
  have hdescent : baseEnd_497419 < baseStart_497419 := by decide
  rcases family_descends (prefixWord ++ tailWord_497419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497622 : List Nat := [5, 2, 1, 1, 3, 2, 1, 4]
def baseStart_497622 : Nat := 118140960795 + 497622 * 2 ^ 59
def prefixEnd_497622 : Nat := 4983230072969 + 3 ^ 40 * 497622 * 2
def baseEnd_497622 : Nat := 151418826815856169088287

theorem tailTrace_497622 : CollatzResearch.WordTrace tailWord_497622 prefixEnd_497622 151418826815856169088287 := by
  unfold tailWord_497622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134360337700497244783945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12099843602138637277695413 1134360337700497244783945)
  ·
    refine ⟨850770253275372933587959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1134360337700497244783945 850770253275372933587959)
    ·
      refine ⟨1276155379913059400381939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850770253275372933587959 1276155379913059400381939)
      ·
        refine ⟨1914233069869589100572909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1276155379913059400381939 1914233069869589100572909)
        ·
          refine ⟨717837401201095912714841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1914233069869589100572909 717837401201095912714841)
          ·
            refine ⟨538378050900821934536131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717837401201095912714841 538378050900821934536131)
            ·
              refine ⟨807567076351232901804197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538378050900821934536131 807567076351232901804197)
              ·
                refine ⟨151418826815856169088287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 807567076351232901804197 151418826815856169088287)
                ·
                  rfl

theorem cell19_497622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_497622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497622 prefixEnd_497622 := by exact prefixLift 497622
  have htrace : WordTrace (prefixWord ++ tailWord_497622) baseStart_497622 baseEnd_497622 := by
    simpa [prefixWord, tailWord_497622, baseEnd_497622] using wordTrace_append hprefix tailTrace_497622
  have hstable : (prefixWord ++ tailWord_497622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497622).length < 2 ^ (prefixWord ++ tailWord_497622).sum := by decide
  have hdescent : baseEnd_497622 < baseStart_497622 := by decide
  rcases family_descends (prefixWord ++ tailWord_497622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497721 : List Nat := [1, 2, 1, 5, 3, 2, 5]
def baseStart_497721 : Nat := 118140960795 + 497721 * 2 ^ 59
def prefixEnd_497721 : Nat := 4983230072969 + 3 ^ 40 * 497721 * 2
def baseEnd_497721 : Nat := 50482983671417757629339

theorem tailTrace_497721 : CollatzResearch.WordTrace tailWord_497721 prefixEnd_497721 50482983671417757629339 := by
  unfold tailWord_497721
  simp only [CollatzResearch.WordTrace]
  refine ⟨18153376229849295824397017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12102250819899530549598011 18153376229849295824397017)
  ·
    refine ⟨13615032172386971868297763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18153376229849295824397017 13615032172386971868297763)
    ·
      refine ⟨20422548258580457802446645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13615032172386971868297763 20422548258580457802446645)
      ·
        refine ⟨1914613899241917918979373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20422548258580457802446645 1914613899241917918979373)
        ·
          refine ⟨717980212215719219617265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1914613899241917918979373 717980212215719219617265)
          ·
            refine ⟨538485159161789414712949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717980212215719219617265 538485159161789414712949)
            ·
              refine ⟨50482983671417757629339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 538485159161789414712949 50482983671417757629339)
              ·
                rfl

theorem cell19_497721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_497721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497721 prefixEnd_497721 := by exact prefixLift 497721
  have htrace : WordTrace (prefixWord ++ tailWord_497721) baseStart_497721 baseEnd_497721 := by
    simpa [prefixWord, tailWord_497721, baseEnd_497721] using wordTrace_append hprefix tailTrace_497721
  have hstable : (prefixWord ++ tailWord_497721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497721).length < 2 ^ (prefixWord ++ tailWord_497721).sum := by decide
  have hdescent : baseEnd_497721 < baseStart_497721 := by decide
  rcases family_descends (prefixWord ++ tailWord_497721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497742 : List Nat := [4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_497742 : Nat := 118140960795 + 497742 * 2 ^ 59
def prefixEnd_497742 : Nat := 4983230072969 + 3 ^ 40 * 497742 * 2
def baseEnd_497742 : Nat := 151455340995731446421293

theorem tailTrace_497742 : CollatzResearch.WordTrace tailWord_497742 prefixEnd_497742 151455340995731446421293 := by
  unfold tailWord_497742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2269267770346652051363935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12102761441848810940607653 2269267770346652051363935)
  ·
    refine ⟨3403901655519978077045903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2269267770346652051363935 3403901655519978077045903)
    ·
      refine ⟨5105852483279967115568855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3403901655519978077045903 5105852483279967115568855)
      ·
        refine ⟨7658778724919950673353283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5105852483279967115568855 7658778724919950673353283)
        ·
          refine ⟨11488168087379926010029925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658778724919950673353283 11488168087379926010029925)
          ·
            refine ⟨2154031516383736126880611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11488168087379926010029925 2154031516383736126880611)
            ·
              refine ⟨3231047274575604190320917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2154031516383736126880611 3231047274575604190320917)
              ·
                refine ⟨151455340995731446421293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3231047274575604190320917 151455340995731446421293)
                ·
                  rfl

theorem cell19_497742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_497742 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497742 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497742 prefixEnd_497742 := by exact prefixLift 497742
  have htrace : WordTrace (prefixWord ++ tailWord_497742) baseStart_497742 baseEnd_497742 := by
    simpa [prefixWord, tailWord_497742, baseEnd_497742] using wordTrace_append hprefix tailTrace_497742
  have hstable : (prefixWord ++ tailWord_497742).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497742).length < 2 ^ (prefixWord ++ tailWord_497742).sum := by decide
  have hdescent : baseEnd_497742 < baseStart_497742 := by decide
  rcases family_descends (prefixWord ++ tailWord_497742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497797 : List Nat := [1, 3, 1, 1, 5, 3, 1, 4]
def baseStart_497797 : Nat := 118140960795 + 497797 * 2 ^ 59
def prefixEnd_497797 : Nat := 4983230072969 + 3 ^ 40 * 497797 * 2
def baseEnd_497797 : Nat := 151472076661507615198921

theorem tailTrace_497797 : CollatzResearch.WordTrace tailWord_497797 prefixEnd_497797 151472076661507615198921 := by
  unfold tailWord_497797
  simp only [CollatzResearch.WordTrace]
  refine ⟨18156148177573960804163645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12104098785049307202775763 18156148177573960804163645)
  ·
    refine ⟨6808555566590235301561367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18156148177573960804163645 6808555566590235301561367)
    ·
      refine ⟨10212833349885352952342051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6808555566590235301561367 10212833349885352952342051)
      ·
        refine ⟨15319250024828029428513077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10212833349885352952342051 15319250024828029428513077)
        ·
          refine ⟨1436179689827627758923101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15319250024828029428513077 1436179689827627758923101)
          ·
            refine ⟨538567383685360409596163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1436179689827627758923101 538567383685360409596163)
            ·
              refine ⟨807851075528040614394245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538567383685360409596163 807851075528040614394245)
              ·
                refine ⟨151472076661507615198921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 807851075528040614394245 151472076661507615198921)
                ·
                  rfl

theorem cell19_497797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_497797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497797 prefixEnd_497797 := by exact prefixLift 497797
  have htrace : WordTrace (prefixWord ++ tailWord_497797) baseStart_497797 baseEnd_497797 := by
    simpa [prefixWord, tailWord_497797, baseEnd_497797] using wordTrace_append hprefix tailTrace_497797
  have hstable : (prefixWord ++ tailWord_497797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497797).length < 2 ^ (prefixWord ++ tailWord_497797).sum := by decide
  have hdescent : baseEnd_497797 < baseStart_497797 := by decide
  rcases family_descends (prefixWord ++ tailWord_497797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497799 : List Nat := [1, 1, 4, 2, 1, 1, 5, 4]
def baseStart_497799 : Nat := 118140960795 + 497799 * 2 ^ 59
def prefixEnd_497799 : Nat := 4983230072969 + 3 ^ 40 * 497799 * 2
def baseEnd_497799 : Nat := 151472685231172203154471

theorem tailTrace_497799 : CollatzResearch.WordTrace tailWord_497799 prefixEnd_497799 151472685231172203154471 := by
  unfold tailWord_497799
  simp only [CollatzResearch.WordTrace]
  refine ⟨18156221123566715145736451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12104147415711143430490967 18156221123566715145736451)
  ·
    refine ⟨27234331685350072718604677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18156221123566715145736451 27234331685350072718604677)
    ·
      refine ⟨5106437191003138634738377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27234331685350072718604677 5106437191003138634738377)
      ·
        refine ⟨3829827893252353976053783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5106437191003138634738377 3829827893252353976053783)
        ·
          refine ⟨5744741839878530964080675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3829827893252353976053783 5744741839878530964080675)
          ·
            refine ⟨8617112759817796446121013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5744741839878530964080675 8617112759817796446121013)
            ·
              refine ⟨807854321232918416823845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8617112759817796446121013 807854321232918416823845)
              ·
                refine ⟨151472685231172203154471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 807854321232918416823845 151472685231172203154471)
                ·
                  rfl

theorem cell19_497799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_497799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497799 prefixEnd_497799 := by exact prefixLift 497799
  have htrace : WordTrace (prefixWord ++ tailWord_497799) baseStart_497799 baseEnd_497799 := by
    simpa [prefixWord, tailWord_497799, baseEnd_497799] using wordTrace_append hprefix tailTrace_497799
  have hstable : (prefixWord ++ tailWord_497799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497799).length < 2 ^ (prefixWord ++ tailWord_497799).sum := by decide
  have hdescent : baseEnd_497799 < baseStart_497799 := by decide
  rcases family_descends (prefixWord ++ tailWord_497799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497812 : List Nat := [2, 4, 2, 3, 1, 1, 3, 3]
def baseStart_497812 : Nat := 118140960795 + 497812 * 2 ^ 59
def prefixEnd_497812 : Nat := 4983230072969 + 3 ^ 40 * 497812 * 2
def baseEnd_497812 : Nat := 151476640933992024865547

theorem tailTrace_497812 : CollatzResearch.WordTrace tailWord_497812 prefixEnd_497812 151476640933992024865547 := by
  unfold tailWord_497812
  simp only [CollatzResearch.WordTrace]
  refine ⟨9078347636259809182979845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12104463515013078910639793 9078347636259809182979845)
  ·
    refine ⟨1702190181798714221808721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9078347636259809182979845 1702190181798714221808721)
    ·
      refine ⟨1276642636349035666356541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1702190181798714221808721 1276642636349035666356541)
      ·
        refine ⟨478740988630888374883703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1276642636349035666356541 478740988630888374883703)
        ·
          refine ⟨718111482946332562325555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478740988630888374883703 718111482946332562325555)
          ·
            refine ⟨1077167224419498843488333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718111482946332562325555 1077167224419498843488333)
            ·
              refine ⟨403937709157312066308125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1077167224419498843488333 403937709157312066308125)
              ·
                refine ⟨151476640933992024865547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403937709157312066308125 151476640933992024865547)
                ·
                  rfl

theorem cell19_497812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_497812 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497812 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497812 prefixEnd_497812 := by exact prefixLift 497812
  have htrace : WordTrace (prefixWord ++ tailWord_497812) baseStart_497812 baseEnd_497812 := by
    simpa [prefixWord, tailWord_497812, baseEnd_497812] using wordTrace_append hprefix tailTrace_497812
  have hstable : (prefixWord ++ tailWord_497812).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497812).length < 2 ^ (prefixWord ++ tailWord_497812).sum := by decide
  have hdescent : baseEnd_497812 < baseStart_497812 := by decide
  rcases family_descends (prefixWord ++ tailWord_497812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497949 : List Nat := [1, 4, 2, 3, 3, 6]
def baseStart_497949 : Nat := 118140960795 + 497949 * 2 ^ 59
def prefixEnd_497949 : Nat := 4983230072969 + 3 ^ 40 * 497949 * 2
def baseEnd_497949 : Nat := 16835369772890699980081

theorem tailTrace_497949 : CollatzResearch.WordTrace tailWord_497949 prefixEnd_497949 16835369772890699980081 := by
  unfold tailWord_497949
  simp only [CollatzResearch.WordTrace]
  refine ⟨18161692073023290763696901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12107794715348860509131267 18161692073023290763696901)
  ·
    refine ⟨3405317263691867018193169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18161692073023290763696901 3405317263691867018193169)
    ·
      refine ⟨2553987947768900263644877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3405317263691867018193169 2553987947768900263644877)
      ·
        refine ⟨957745480413337598866829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2553987947768900263644877 957745480413337598866829)
        ·
          refine ⟨359154555155001599575061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 957745480413337598866829 359154555155001599575061)
          ·
            refine ⟨16835369772890699980081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 359154555155001599575061 16835369772890699980081)
            ·
              rfl

theorem cell19_497949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 6].length) (baseStart_497949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497949 prefixEnd_497949 := by exact prefixLift 497949
  have htrace : WordTrace (prefixWord ++ tailWord_497949) baseStart_497949 baseEnd_497949 := by
    simpa [prefixWord, tailWord_497949, baseEnd_497949] using wordTrace_append hprefix tailTrace_497949
  have hstable : (prefixWord ++ tailWord_497949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497949).length < 2 ^ (prefixWord ++ tailWord_497949).sum := by decide
  have hdescent : baseEnd_497949 < baseStart_497949 := by decide
  rcases family_descends (prefixWord ++ tailWord_497949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497985 : List Nat := [1, 2, 5, 2, 2, 1, 3, 3]
def baseStart_497985 : Nat := 118140960795 + 497985 * 2 ^ 59
def prefixEnd_497985 : Nat := 4983230072969 + 3 ^ 40 * 497985 * 2
def baseEnd_497985 : Nat := 151529282209978883020631

theorem tailTrace_497985 : CollatzResearch.WordTrace tailWord_497985 prefixEnd_497985 151529282209978883020631 := by
  unfold tailWord_497985
  simp only [CollatzResearch.WordTrace]
  refine ⟨18163005100892868912007409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12108670067261912608004939 18163005100892868912007409)
  ·
    refine ⟨13622253825669651684005557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18163005100892868912007409 13622253825669651684005557)
    ·
      refine ⟨1277086296156529845375521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13622253825669651684005557 1277086296156529845375521)
      ·
        refine ⟨957814722117397384031641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1277086296156529845375521 957814722117397384031641)
        ·
          refine ⟨718361041588048038023731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957814722117397384031641 718361041588048038023731)
          ·
            refine ⟨1077541562382072057035597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718361041588048038023731 1077541562382072057035597)
            ·
              refine ⟨404078085893277021388349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1077541562382072057035597 404078085893277021388349)
              ·
                refine ⟨151529282209978883020631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404078085893277021388349 151529282209978883020631)
                ·
                  rfl

theorem cell19_497985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 3].length) (baseStart_497985 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_497985 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_497985 prefixEnd_497985 := by exact prefixLift 497985
  have htrace : WordTrace (prefixWord ++ tailWord_497985) baseStart_497985 baseEnd_497985 := by
    simpa [prefixWord, tailWord_497985, baseEnd_497985] using wordTrace_append hprefix tailTrace_497985
  have hstable : (prefixWord ++ tailWord_497985).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497985).length < 2 ^ (prefixWord ++ tailWord_497985).sum := by decide
  have hdescent : baseEnd_497985 < baseStart_497985 := by decide
  rcases family_descends (prefixWord ++ tailWord_497985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498038 : List Nat := [5, 1, 1, 4, 2, 1, 2, 3]
def baseStart_498038 : Nat := 118140960795 + 498038 * 2 ^ 59
def prefixEnd_498038 : Nat := 4983230072969 + 3 ^ 40 * 498038 * 2
def baseEnd_498038 : Nat := 151545409306090463842709

theorem tailTrace_498038 : CollatzResearch.WordTrace tailWord_498038 prefixEnd_498038 151545409306090463842709 := by
  unfold tailWord_498038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135308635606303685230423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12109958779800572642457845 1135308635606303685230423)
  ·
    refine ⟨1702962953409455527845635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1135308635606303685230423 1702962953409455527845635)
    ·
      refine ⟨2554444430114183291768453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702962953409455527845635 2554444430114183291768453)
      ·
        refine ⟨478958330646409367206585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2554444430114183291768453 478958330646409367206585)
        ·
          refine ⟨359218747984807025404939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478958330646409367206585 359218747984807025404939)
          ·
            refine ⟨538828121977210538107409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359218747984807025404939 538828121977210538107409)
            ·
              refine ⟨404121091482907903580557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538828121977210538107409 404121091482907903580557)
              ·
                refine ⟨151545409306090463842709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404121091482907903580557 151545409306090463842709)
                ·
                  rfl

theorem cell19_498038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_498038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498038 prefixEnd_498038 := by exact prefixLift 498038
  have htrace : WordTrace (prefixWord ++ tailWord_498038) baseStart_498038 baseEnd_498038 := by
    simpa [prefixWord, tailWord_498038, baseEnd_498038] using wordTrace_append hprefix tailTrace_498038
  have hstable : (prefixWord ++ tailWord_498038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498038).length < 2 ^ (prefixWord ++ tailWord_498038).sum := by decide
  have hdescent : baseEnd_498038 < baseStart_498038 := by decide
  rcases family_descends (prefixWord ++ tailWord_498038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498124 : List Nat := [2, 2, 1, 4, 10]
def baseStart_498124 : Nat := 118140960795 + 498124 * 2 ^ 59
def prefixEnd_498124 : Nat := 4983230072969 + 3 ^ 40 * 498124 * 2
def baseEnd_498124 : Nat := 5613762140802509108569

theorem tailTrace_498124 : CollatzResearch.WordTrace tailWord_498124 prefixEnd_498124 5613762140802509108569 := by
  unfold tailWord_498124
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084037423694647825658713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12112049898259530434211617 9084037423694647825658713)
  ·
    refine ⟨6813028067770985869244035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9084037423694647825658713 6813028067770985869244035)
    ·
      refine ⟨10219542101656478803866053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6813028067770985869244035 10219542101656478803866053)
      ·
        refine ⟨1916164144060589775724885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10219542101656478803866053 1916164144060589775724885)
        ·
          refine ⟨5613762140802509108569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1916164144060589775724885 5613762140802509108569)
          ·
            rfl

theorem cell19_498124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 10].length) (baseStart_498124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498124 prefixEnd_498124 := by exact prefixLift 498124
  have htrace : WordTrace (prefixWord ++ tailWord_498124) baseStart_498124 baseEnd_498124 := by
    simpa [prefixWord, tailWord_498124, baseEnd_498124] using wordTrace_append hprefix tailTrace_498124
  have hstable : (prefixWord ++ tailWord_498124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498124).length < 2 ^ (prefixWord ++ tailWord_498124).sum := by decide
  have hdescent : baseEnd_498124 < baseStart_498124 := by decide
  rcases family_descends (prefixWord ++ tailWord_498124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498158 : List Nat := [4, 1, 2, 1, 2, 3, 3, 3]
def baseStart_498158 : Nat := 118140960795 + 498158 * 2 ^ 59
def prefixEnd_498158 : Nat := 4983230072969 + 3 ^ 40 * 498158 * 2
def baseEnd_498158 : Nat := 151581923485965741175715

theorem tailTrace_498158 : CollatzResearch.WordTrace tailWord_498158 prefixEnd_498158 151581923485965741175715 := by
  unfold tailWord_498158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271164366158264932256891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12112876619510746305370085 2271164366158264932256891)
  ·
    refine ⟨3406746549237397398385337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2271164366158264932256891 3406746549237397398385337)
    ·
      refine ⟨2555059911928048048789003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3406746549237397398385337 2555059911928048048789003)
      ·
        refine ⟨3832589867892072073183505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2555059911928048048789003 3832589867892072073183505)
        ·
          refine ⟨2874442400919054054887629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3832589867892072073183505 2874442400919054054887629)
          ·
            refine ⟨1077915900344645270582861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2874442400919054054887629 1077915900344645270582861)
            ·
              refine ⟨404218462629241976468573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1077915900344645270582861 404218462629241976468573)
              ·
                refine ⟨151581923485965741175715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404218462629241976468573 151581923485965741175715)
                ·
                  rfl

theorem cell19_498158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_498158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498158 prefixEnd_498158 := by exact prefixLift 498158
  have htrace : WordTrace (prefixWord ++ tailWord_498158) baseStart_498158 baseEnd_498158 := by
    simpa [prefixWord, tailWord_498158, baseEnd_498158] using wordTrace_append hprefix tailTrace_498158
  have hstable : (prefixWord ++ tailWord_498158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498158).length < 2 ^ (prefixWord ++ tailWord_498158).sum := by decide
  have hdescent : baseEnd_498158 < baseStart_498158 := by decide
  rcases family_descends (prefixWord ++ tailWord_498158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498160 : List Nat := [2, 1, 1, 1, 3, 3, 5, 3]
def baseStart_498160 : Nat := 118140960795 + 498160 * 2 ^ 59
def prefixEnd_498160 : Nat := 4983230072969 + 3 ^ 40 * 498160 * 2
def baseEnd_498160 : Nat := 151582532055630329131265

theorem tailTrace_498160 : CollatzResearch.WordTrace tailWord_498160 prefixEnd_498160 151582532055630329131265 := by
  unfold tailWord_498160
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084693937629436899813967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12112925250172582533085289 9084693937629436899813967)
  ·
    refine ⟨13627040906444155349720951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9084693937629436899813967 13627040906444155349720951)
    ·
      refine ⟨20440561359666233024581427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13627040906444155349720951 20440561359666233024581427)
      ·
        refine ⟨30660842039499349536872141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20440561359666233024581427 30660842039499349536872141)
        ·
          refine ⟨11497815764812256076327053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30660842039499349536872141 11497815764812256076327053)
          ·
            refine ⟨4311680911804596028622645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11497815764812256076327053 4311680911804596028622645)
            ·
              refine ⟨404220085481680877683373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4311680911804596028622645 404220085481680877683373)
              ·
                refine ⟨151582532055630329131265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404220085481680877683373 151582532055630329131265)
                ·
                  rfl

theorem cell19_498160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_498160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498160 prefixEnd_498160 := by exact prefixLift 498160
  have htrace : WordTrace (prefixWord ++ tailWord_498160) baseStart_498160 baseEnd_498160 := by
    simpa [prefixWord, tailWord_498160, baseEnd_498160] using wordTrace_append hprefix tailTrace_498160
  have hstable : (prefixWord ++ tailWord_498160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498160).length < 2 ^ (prefixWord ++ tailWord_498160).sum := by decide
  have hdescent : baseEnd_498160 < baseStart_498160 := by decide
  rcases family_descends (prefixWord ++ tailWord_498160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498236 : List Nat := [2, 2, 2, 2, 3, 3, 5]
def baseStart_498236 : Nat := 118140960795 + 498236 * 2 ^ 59
def prefixEnd_498236 : Nat := 4983230072969 + 3 ^ 40 * 498236 * 2
def baseEnd_498236 : Nat := 50535219234294890480723

theorem tailTrace_498236 : CollatzResearch.WordTrace tailWord_498236 prefixEnd_498236 50535219234294890480723 := by
  unfold tailWord_498236
  simp only [CollatzResearch.WordTrace]
  refine ⟨9086079911491769389697281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12114773215322359186263041 9086079911491769389697281)
  ·
    refine ⟨6814559933618827042272961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9086079911491769389697281 6814559933618827042272961)
    ·
      refine ⟨5110919950214120281704721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6814559933618827042272961 5110919950214120281704721)
      ·
        refine ⟨3833189962660590211278541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5110919950214120281704721 3833189962660590211278541)
        ·
          refine ⟨1437446235997721329229453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3833189962660590211278541 1437446235997721329229453)
          ·
            refine ⟨539042338499145498461045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1437446235997721329229453 539042338499145498461045)
            ·
              refine ⟨50535219234294890480723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 539042338499145498461045 50535219234294890480723)
              ·
                rfl

theorem cell19_498236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_498236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498236 prefixEnd_498236 := by exact prefixLift 498236
  have htrace : WordTrace (prefixWord ++ tailWord_498236) baseStart_498236 baseEnd_498236 := by
    simpa [prefixWord, tailWord_498236, baseEnd_498236] using wordTrace_append hprefix tailTrace_498236
  have hstable : (prefixWord ++ tailWord_498236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498236).length < 2 ^ (prefixWord ++ tailWord_498236).sum := by decide
  have hdescent : baseEnd_498236 < baseStart_498236 := by decide
  rcases family_descends (prefixWord ++ tailWord_498236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498253 : List Nat := [1, 6, 1, 1, 2, 2, 2, 4]
def baseStart_498253 : Nat := 118140960795 + 498253 * 2 ^ 59
def prefixEnd_498253 : Nat := 4983230072969 + 3 ^ 40 * 498253 * 2
def baseEnd_498253 : Nat := 151610830545033669064345

theorem tailTrace_498253 : CollatzResearch.WordTrace tailWord_498253 prefixEnd_498253 151610830545033669064345 := by
  unfold tailWord_498253
  simp only [CollatzResearch.WordTrace]
  refine ⟨18172779863921950682763413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12115186575947967121842275 18172779863921950682763413)
  ·
    refine ⟨851849056121341438254535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18172779863921950682763413 851849056121341438254535)
    ·
      refine ⟨1277773584182012157381803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 851849056121341438254535 1277773584182012157381803)
      ·
        refine ⟨1916660376273018236072705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277773584182012157381803 1916660376273018236072705)
        ·
          refine ⟨1437495282204763677054529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1916660376273018236072705 1437495282204763677054529)
          ·
            refine ⟨1078121461653572757790897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1437495282204763677054529 1078121461653572757790897)
            ·
              refine ⟨808591096240179568343173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1078121461653572757790897 808591096240179568343173)
              ·
                refine ⟨151610830545033669064345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 808591096240179568343173 151610830545033669064345)
                ·
                  rfl

theorem cell19_498253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_498253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498253 prefixEnd_498253 := by exact prefixLift 498253
  have htrace : WordTrace (prefixWord ++ tailWord_498253) baseStart_498253 baseEnd_498253 := by
    simpa [prefixWord, tailWord_498253, baseEnd_498253] using wordTrace_append hprefix tailTrace_498253
  have hstable : (prefixWord ++ tailWord_498253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498253).length < 2 ^ (prefixWord ++ tailWord_498253).sum := by decide
  have hdescent : baseEnd_498253 < baseStart_498253 := by decide
  rcases family_descends (prefixWord ++ tailWord_498253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498257 : List Nat := [1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_498257 : Nat := 118140960795 + 498257 * 2 ^ 59
def prefixEnd_498257 : Nat := 4983230072969 + 3 ^ 40 * 498257 * 2
def baseEnd_498257 : Nat := 151612047684362844975445

theorem tailTrace_498257 : CollatzResearch.WordTrace tailWord_498257 prefixEnd_498257 151612047684362844975445 := by
  unfold tailWord_498257
  simp only [CollatzResearch.WordTrace]
  refine ⟨18172925755907459365909025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12115283837271639577272683 18172925755907459365909025)
  ·
    refine ⟨13629694316930594524431769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18172925755907459365909025 13629694316930594524431769)
    ·
      refine ⟨10222270737697945893323827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13629694316930594524431769 10222270737697945893323827)
      ·
        refine ⟨15333406106546918839985741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10222270737697945893323827 15333406106546918839985741)
        ·
          refine ⟨5750027289955094564994653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15333406106546918839985741 5750027289955094564994653)
          ·
            refine ⟨2156260233733160461872995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5750027289955094564994653 2156260233733160461872995)
            ·
              refine ⟨3234390350599740692809493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2156260233733160461872995 3234390350599740692809493)
              ·
                refine ⟨151612047684362844975445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3234390350599740692809493 151612047684362844975445)
                ·
                  rfl

theorem cell19_498257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_498257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498257 prefixEnd_498257 := by exact prefixLift 498257
  have htrace : WordTrace (prefixWord ++ tailWord_498257) baseStart_498257 baseEnd_498257 := by
    simpa [prefixWord, tailWord_498257, baseEnd_498257] using wordTrace_append hprefix tailTrace_498257
  have hstable : (prefixWord ++ tailWord_498257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498257).length < 2 ^ (prefixWord ++ tailWord_498257).sum := by decide
  have hdescent : baseEnd_498257 < baseStart_498257 := by decide
  rcases family_descends (prefixWord ++ tailWord_498257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498276 : List Nat := [2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_498276 : Nat := 118140960795 + 498276 * 2 ^ 59
def prefixEnd_498276 : Nat := 4983230072969 + 3 ^ 40 * 498276 * 2
def baseEnd_498276 : Nat := 151617829096176430553171

theorem tailTrace_498276 : CollatzResearch.WordTrace tailWord_498276 prefixEnd_498276 151617829096176430553171 := by
  unfold tailWord_498276
  simp only [CollatzResearch.WordTrace]
  refine ⟨9086809371419312805425341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12115745828559083740567121 9086809371419312805425341)
  ·
    refine ⟨3407553514282242302034503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9086809371419312805425341 3407553514282242302034503)
    ·
      refine ⟨5111330271423363453051755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407553514282242302034503 5111330271423363453051755)
      ·
        refine ⟨7666995407135045179577633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5111330271423363453051755 7666995407135045179577633)
        ·
          refine ⟨5750246555351283884683225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7666995407135045179577633 5750246555351283884683225)
          ·
            refine ⟨4312684916513462913512419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5750246555351283884683225 4312684916513462913512419)
            ·
              refine ⟨6469027374770194370268629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312684916513462913512419 6469027374770194370268629)
              ·
                refine ⟨151617829096176430553171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6469027374770194370268629 151617829096176430553171)
                ·
                  rfl

theorem cell19_498276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_498276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498276 prefixEnd_498276 := by exact prefixLift 498276
  have htrace : WordTrace (prefixWord ++ tailWord_498276) baseStart_498276 baseEnd_498276 := by
    simpa [prefixWord, tailWord_498276, baseEnd_498276] using wordTrace_append hprefix tailTrace_498276
  have hstable : (prefixWord ++ tailWord_498276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498276).length < 2 ^ (prefixWord ++ tailWord_498276).sum := by decide
  have hdescent : baseEnd_498276 < baseStart_498276 := by decide
  rcases family_descends (prefixWord ++ tailWord_498276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498293 : List Nat := [1, 3, 4, 2, 2, 7]
def baseStart_498293 : Nat := 118140960795 + 498293 * 2 ^ 59
def prefixEnd_498293 : Nat := 4983230072969 + 3 ^ 40 * 498293 * 2
def baseEnd_498293 : Nat := 16847000215369492019483

theorem tailTrace_498293 : CollatzResearch.WordTrace tailWord_498293 prefixEnd_498293 16847000215369492019483 := by
  unfold tailWord_498293
  simp only [CollatzResearch.WordTrace]
  refine ⟨18174238783777037514219533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12116159189184691676146355 18174238783777037514219533)
  ·
    refine ⟨6815339543916389067832325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18174238783777037514219533 6815339543916389067832325)
    ·
      refine ⟨1277876164484322950218561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6815339543916389067832325 1277876164484322950218561)
      ·
        refine ⟨958407123363242212663921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1277876164484322950218561 958407123363242212663921)
        ·
          refine ⟨718805342522431659497941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 958407123363242212663921 718805342522431659497941)
          ·
            refine ⟨16847000215369492019483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 718805342522431659497941 16847000215369492019483)
            ·
              rfl

theorem cell19_498293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 7].length) (baseStart_498293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498293 prefixEnd_498293 := by exact prefixLift 498293
  have htrace : WordTrace (prefixWord ++ tailWord_498293) baseStart_498293 baseEnd_498293 := by
    simpa [prefixWord, tailWord_498293, baseEnd_498293] using wordTrace_append hprefix tailTrace_498293
  have hstable : (prefixWord ++ tailWord_498293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498293).length < 2 ^ (prefixWord ++ tailWord_498293).sum := by decide
  have hdescent : baseEnd_498293 < baseStart_498293 := by decide
  rcases family_descends (prefixWord ++ tailWord_498293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498333 : List Nat := [1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_498333 : Nat := 118140960795 + 498333 * 2 ^ 59
def prefixEnd_498333 : Nat := 4983230072969 + 3 ^ 40 * 498333 * 2
def baseEnd_498333 : Nat := 151635173331617187286349

theorem tailTrace_498333 : CollatzResearch.WordTrace tailWord_498333 prefixEnd_498333 151635173331617187286349 := by
  unfold tailWord_498333
  simp only [CollatzResearch.WordTrace]
  refine ⟨18175697703632124345675653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12117131802421416230450435 18175697703632124345675653)
  ·
    refine ⟨3407943319431023314814185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18175697703632124345675653 3407943319431023314814185)
    ·
      refine ⟨2555957489573267486110639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3407943319431023314814185 2555957489573267486110639)
      ·
        refine ⟨3833936234359901229165959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2555957489573267486110639 3833936234359901229165959)
        ·
          refine ⟨5750904351539851843748939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833936234359901229165959 5750904351539851843748939)
          ·
            refine ⟨8626356527309777765623409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750904351539851843748939 8626356527309777765623409)
            ·
              refine ⟨6469767395482333324217557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8626356527309777765623409 6469767395482333324217557)
              ·
                refine ⟨151635173331617187286349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6469767395482333324217557 151635173331617187286349)
                ·
                  rfl

theorem cell19_498333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_498333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498333 prefixEnd_498333 := by exact prefixLift 498333
  have htrace : WordTrace (prefixWord ++ tailWord_498333) baseStart_498333 baseEnd_498333 := by
    simpa [prefixWord, tailWord_498333, baseEnd_498333] using wordTrace_append hprefix tailTrace_498333
  have hstable : (prefixWord ++ tailWord_498333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498333).length < 2 ^ (prefixWord ++ tailWord_498333).sum := by decide
  have hdescent : baseEnd_498333 < baseStart_498333 := by decide
  rcases family_descends (prefixWord ++ tailWord_498333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498428 : List Nat := [2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_498428 : Nat := 118140960795 + 498428 * 2 ^ 59
def prefixEnd_498428 : Nat := 4983230072969 + 3 ^ 40 * 498428 * 2
def baseEnd_498428 : Nat := 151664080390685115174979

theorem tailTrace_498428 : CollatzResearch.WordTrace tailWord_498428 prefixEnd_498428 151664080390685115174979 := by
  unfold tailWord_498428
  simp only [CollatzResearch.WordTrace]
  refine ⟨9089581319143977785191969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12119441758858637046922625 9089581319143977785191969)
  ·
    refine ⟨6817185989357983338893977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9089581319143977785191969 6817185989357983338893977)
    ·
      refine ⟨5112889492018487504170483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6817185989357983338893977 5112889492018487504170483)
      ·
        refine ⟨7669334238027731256255725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5112889492018487504170483 7669334238027731256255725)
        ·
          refine ⟨2876000339260399221095897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7669334238027731256255725 2876000339260399221095897)
          ·
            refine ⟨2157000254445299415821923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2876000339260399221095897 2157000254445299415821923)
            ·
              refine ⟨3235500381667949123732885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157000254445299415821923 3235500381667949123732885)
              ·
                refine ⟨151664080390685115174979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3235500381667949123732885 151664080390685115174979)
                ·
                  rfl

theorem cell19_498428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_498428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498428 prefixEnd_498428 := by exact prefixLift 498428
  have htrace : WordTrace (prefixWord ++ tailWord_498428) baseStart_498428 baseEnd_498428 := by
    simpa [prefixWord, tailWord_498428, baseEnd_498428] using wordTrace_append hprefix tailTrace_498428
  have hstable : (prefixWord ++ tailWord_498428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498428).length < 2 ^ (prefixWord ++ tailWord_498428).sum := by decide
  have hdescent : baseEnd_498428 < baseStart_498428 := by decide
  rcases family_descends (prefixWord ++ tailWord_498428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498466 : List Nat := [3, 3, 1, 1, 2, 9]
def baseStart_498466 : Nat := 118140960795 + 498466 * 2 ^ 59
def prefixEnd_498466 : Nat := 4983230072969 + 3 ^ 40 * 498466 * 2
def baseEnd_498466 : Nat := 16852849246034698481159

theorem tailTrace_498466 : CollatzResearch.WordTrace tailWord_498466 prefixEnd_498466 16852849246034698481159 := by
  unfold tailWord_498466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545137153037572015066813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12120365741433525373511501 4545137153037572015066813)
  ·
    refine ⟨1704426432389089505650055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4545137153037572015066813 1704426432389089505650055)
    ·
      refine ⟨2556639648583634258475083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1704426432389089505650055 2556639648583634258475083)
      ·
        refine ⟨3834959472875451387712625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2556639648583634258475083 3834959472875451387712625)
        ·
          refine ⟨2876219604656588540784469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3834959472875451387712625 2876219604656588540784469)
          ·
            refine ⟨16852849246034698481159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2876219604656588540784469 16852849246034698481159)
            ·
              rfl

theorem cell19_498466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 9].length) (baseStart_498466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498466 prefixEnd_498466 := by exact prefixLift 498466
  have htrace : WordTrace (prefixWord ++ tailWord_498466) baseStart_498466 baseEnd_498466 := by
    simpa [prefixWord, tailWord_498466, baseEnd_498466] using wordTrace_append hprefix tailTrace_498466
  have hstable : (prefixWord ++ tailWord_498466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498466).length < 2 ^ (prefixWord ++ tailWord_498466).sum := by decide
  have hdescent : baseEnd_498466 < baseStart_498466 := by decide
  rcases family_descends (prefixWord ++ tailWord_498466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498477 : List Nat := [1, 5, 3, 2, 2, 1, 1, 4]
def baseStart_498477 : Nat := 118140960795 + 498477 * 2 ^ 59
def prefixEnd_498477 : Nat := 4983230072969 + 3 ^ 40 * 498477 * 2
def baseEnd_498477 : Nat := 151678990347467520085957

theorem tailTrace_498477 : CollatzResearch.WordTrace tailWord_498477 prefixEnd_498477 151678990347467520085957 := by
  unfold tailWord_498477
  simp only [CollatzResearch.WordTrace]
  refine ⟨18180949815110436938917685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12120633210073624625945123 18180949815110436938917685)
  ·
    refine ⟨1704464045166603463023533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18180949815110436938917685 1704464045166603463023533)
    ·
      refine ⟨639174016937476298633825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1704464045166603463023533 639174016937476298633825)
      ·
        refine ⟨479380512703107223975369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639174016937476298633825 479380512703107223975369)
        ·
          refine ⟨359535384527330417981527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479380512703107223975369 359535384527330417981527)
          ·
            refine ⟨539303076790995626972291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359535384527330417981527 539303076790995626972291)
            ·
              refine ⟨808954615186493440458437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539303076790995626972291 808954615186493440458437)
              ·
                refine ⟨151678990347467520085957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 808954615186493440458437 151678990347467520085957)
                ·
                  rfl

theorem cell19_498477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 4].length) (baseStart_498477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498477 prefixEnd_498477 := by exact prefixLift 498477
  have htrace : WordTrace (prefixWord ++ tailWord_498477) baseStart_498477 baseEnd_498477 := by
    simpa [prefixWord, tailWord_498477, baseEnd_498477] using wordTrace_append hprefix tailTrace_498477
  have hstable : (prefixWord ++ tailWord_498477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498477).length < 2 ^ (prefixWord ++ tailWord_498477).sum := by decide
  have hdescent : baseEnd_498477 < baseStart_498477 := by decide
  rcases family_descends (prefixWord ++ tailWord_498477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498483 : List Nat := [1, 1, 1, 2, 6, 3, 1, 4]
def baseStart_498483 : Nat := 118140960795 + 498483 * 2 ^ 59
def prefixEnd_498483 : Nat := 4983230072969 + 3 ^ 40 * 498483 * 2
def baseEnd_498483 : Nat := 151680816056461283952607

theorem tailTrace_498483 : CollatzResearch.WordTrace tailWord_498483 prefixEnd_498483 151680816056461283952607 := by
  unfold tailWord_498483
  simp only [CollatzResearch.WordTrace]
  refine ⟨18181168653088699963636103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12120779102059133309090735 18181168653088699963636103)
  ·
    refine ⟨27271752979633049945454155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18181168653088699963636103 27271752979633049945454155)
    ·
      refine ⟨40907629469449574918181233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27271752979633049945454155 40907629469449574918181233)
      ·
        refine ⟨30680722102087181188635925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40907629469449574918181233 30680722102087181188635925)
        ·
          refine ⟨1438158848535336618217309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30680722102087181188635925 1438158848535336618217309)
          ·
            refine ⟨539309568200751231831491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1438158848535336618217309 539309568200751231831491)
            ·
              refine ⟨808964352301126847747237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539309568200751231831491 808964352301126847747237)
              ·
                refine ⟨151680816056461283952607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 808964352301126847747237 151680816056461283952607)
                ·
                  rfl

theorem cell19_498483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_498483 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498483 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498483 prefixEnd_498483 := by exact prefixLift 498483
  have htrace : WordTrace (prefixWord ++ tailWord_498483) baseStart_498483 baseEnd_498483 := by
    simpa [prefixWord, tailWord_498483, baseEnd_498483] using wordTrace_append hprefix tailTrace_498483
  have hstable : (prefixWord ++ tailWord_498483).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498483).length < 2 ^ (prefixWord ++ tailWord_498483).sum := by decide
  have hdescent : baseEnd_498483 < baseStart_498483 := by decide
  rcases family_descends (prefixWord ++ tailWord_498483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498639 : List Nat := [1, 1, 2, 1, 1, 13]
def baseStart_498639 : Nat := 118140960795 + 498639 * 2 ^ 59
def prefixEnd_498639 : Nat := 4983230072969 + 3 ^ 40 * 498639 * 2
def baseEnd_498639 : Nat := 16858698276699904942835

theorem tailTrace_498639 : CollatzResearch.WordTrace tailWord_498639 prefixEnd_498639 16858698276699904942835 := by
  unfold tailWord_498639
  simp only [CollatzResearch.WordTrace]
  refine ⟨18186858440523538606314971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12124572293682359070876647 18186858440523538606314971)
  ·
    refine ⟨27280287660785307909472457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18186858440523538606314971 27280287660785307909472457)
    ·
      refine ⟨20460215745588980932104343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27280287660785307909472457 20460215745588980932104343)
      ·
        refine ⟨30690323618383471398156515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20460215745588980932104343 30690323618383471398156515)
        ·
          refine ⟨46035485427575207097234773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30690323618383471398156515 46035485427575207097234773)
          ·
            refine ⟨16858698276699904942835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 46035485427575207097234773 16858698276699904942835)
            ·
              rfl

theorem cell19_498639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 13].length) (baseStart_498639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498639 prefixEnd_498639 := by exact prefixLift 498639
  have htrace : WordTrace (prefixWord ++ tailWord_498639) baseStart_498639 baseEnd_498639 := by
    simpa [prefixWord, tailWord_498639, baseEnd_498639] using wordTrace_append hprefix tailTrace_498639
  have hstable : (prefixWord ++ tailWord_498639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498639).length < 2 ^ (prefixWord ++ tailWord_498639).sum := by decide
  have hdescent : baseEnd_498639 < baseStart_498639 := by decide
  rcases family_descends (prefixWord ++ tailWord_498639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498673 : List Nat := [1, 2, 2, 2, 4, 2, 3, 3]
def baseStart_498673 : Nat := 118140960795 + 498673 * 2 ^ 59
def prefixEnd_498673 : Nat := 4983230072969 + 3 ^ 40 * 498673 * 2
def baseEnd_498673 : Nat := 151738630174597139729867

theorem tailTrace_498673 : CollatzResearch.WordTrace tailWord_498673 prefixEnd_498673 151738630174597139729867 := by
  unfold tailWord_498673
  simp only [CollatzResearch.WordTrace]
  refine ⟨18188098522400362413052673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12125399014933574942035115 18188098522400362413052673)
  ·
    refine ⟨13641073891800271809789505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18188098522400362413052673 13641073891800271809789505)
    ·
      refine ⟨10230805418850203857342129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13641073891800271809789505 10230805418850203857342129)
      ·
        refine ⟨7673104064137652893006597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10230805418850203857342129 7673104064137652893006597)
        ·
          refine ⟨1438707012025809917438737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7673104064137652893006597 1438707012025809917438737)
          ·
            refine ⟨1079030259019357438079053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1438707012025809917438737 1079030259019357438079053)
            ·
              refine ⟨404636347132259039279645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1079030259019357438079053 404636347132259039279645)
              ·
                refine ⟨151738630174597139729867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404636347132259039279645 151738630174597139729867)
                ·
                  rfl

theorem cell19_498673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 3].length) (baseStart_498673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498673 prefixEnd_498673 := by exact prefixLift 498673
  have htrace : WordTrace (prefixWord ++ tailWord_498673) baseStart_498673 baseEnd_498673 := by
    simpa [prefixWord, tailWord_498673, baseEnd_498673] using wordTrace_append hprefix tailTrace_498673
  have hstable : (prefixWord ++ tailWord_498673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498673).length < 2 ^ (prefixWord ++ tailWord_498673).sum := by decide
  have hdescent : baseEnd_498673 < baseStart_498673 := by decide
  rcases family_descends (prefixWord ++ tailWord_498673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498690 : List Nat := [3, 4, 1, 3, 1, 1, 6]
def baseStart_498690 : Nat := 118140960795 + 498690 * 2 ^ 59
def prefixEnd_498690 : Nat := 4983230072969 + 3 ^ 40 * 498690 * 2
def baseEnd_498690 : Nat := 50581267672248712450681

theorem tailTrace_498690 : CollatzResearch.WordTrace tailWord_498690 prefixEnd_498690 50581267672248712450681 := by
  unfold tailWord_498690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547179640834693579105381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12125812375559182877614349 4547179640834693579105381)
  ·
    refine ⟨852596182656505046082259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4547179640834693579105381 852596182656505046082259)
    ·
      refine ⟨1278894273984757569123389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 852596182656505046082259 1278894273984757569123389)
      ·
        refine ⟨479585352744284088421271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1278894273984757569123389 479585352744284088421271)
        ·
          refine ⟨719378029116426132631907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479585352744284088421271 719378029116426132631907)
          ·
            refine ⟨1079067043674639198947861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719378029116426132631907 1079067043674639198947861)
            ·
              refine ⟨50581267672248712450681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1079067043674639198947861 50581267672248712450681)
              ·
                rfl

theorem cell19_498690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 6].length) (baseStart_498690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498690 prefixEnd_498690 := by exact prefixLift 498690
  have htrace : WordTrace (prefixWord ++ tailWord_498690) baseStart_498690 baseEnd_498690 := by
    simpa [prefixWord, tailWord_498690, baseEnd_498690] using wordTrace_append hprefix tailTrace_498690
  have hstable : (prefixWord ++ tailWord_498690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498690).length < 2 ^ (prefixWord ++ tailWord_498690).sum := by decide
  have hdescent : baseEnd_498690 < baseStart_498690 := by decide
  rcases family_descends (prefixWord ++ tailWord_498690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498730 : List Nat := [3, 1, 4, 1, 3, 1, 1, 5]
def baseStart_498730 : Nat := 118140960795 + 498730 * 2 ^ 59
def prefixEnd_498730 : Nat := 4983230072969 + 3 ^ 40 * 498730 * 2
def baseEnd_498730 : Nat := 151755974410037896463045

theorem tailTrace_498730 : CollatzResearch.WordTrace tailWord_498730 prefixEnd_498730 151755974410037896463045 := by
  unfold tailWord_498730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547544370798465286969411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12126784988795907431918429 4547544370798465286969411)
  ·
    refine ⟨6821316556197697930454117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4547544370798465286969411 6821316556197697930454117)
    ·
      refine ⟨1278996854287068361960147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6821316556197697930454117 1278996854287068361960147)
      ·
        refine ⟨1918495281430602542940221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278996854287068361960147 1918495281430602542940221)
        ·
          refine ⟨719435730536475953602583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1918495281430602542940221 719435730536475953602583)
          ·
            refine ⟨1079153595804713930403875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719435730536475953602583 1079153595804713930403875)
            ·
              refine ⟨1618730393707070895605813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079153595804713930403875 1618730393707070895605813)
              ·
                refine ⟨151755974410037896463045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1618730393707070895605813 151755974410037896463045)
                ·
                  rfl

theorem cell19_498730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_498730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498730 prefixEnd_498730 := by exact prefixLift 498730
  have htrace : WordTrace (prefixWord ++ tailWord_498730) baseStart_498730 baseEnd_498730 := by
    simpa [prefixWord, tailWord_498730, baseEnd_498730] using wordTrace_append hprefix tailTrace_498730
  have hstable : (prefixWord ++ tailWord_498730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498730).length < 2 ^ (prefixWord ++ tailWord_498730).sum := by decide
  have hdescent : baseEnd_498730 < baseStart_498730 := by decide
  rcases family_descends (prefixWord ++ tailWord_498730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498770 : List Nat := [3, 2, 2, 1, 3, 1, 1, 6]
def baseStart_498770 : Nat := 118140960795 + 498770 * 2 ^ 59
def prefixEnd_498770 : Nat := 4983230072969 + 3 ^ 40 * 498770 * 2
def baseEnd_498770 : Nat := 151768145803329655574047

theorem tailTrace_498770 : CollatzResearch.WordTrace tailWord_498770 prefixEnd_498770 151768145803329655574047 := by
  unfold tailWord_498770
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547909100762236994833441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12127757602032631986222509 4547909100762236994833441)
  ·
    refine ⟨3410931825571677746125081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4547909100762236994833441 3410931825571677746125081)
    ·
      refine ⟨2558198869178758309593811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3410931825571677746125081 2558198869178758309593811)
      ·
        refine ⟨3837298303768137464390717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558198869178758309593811 3837298303768137464390717)
        ·
          refine ⟨1438986863913051549146519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3837298303768137464390717 1438986863913051549146519)
          ·
            refine ⟨2158480295869577323719779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438986863913051549146519 2158480295869577323719779)
            ·
              refine ⟨3237720443804365985579669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158480295869577323719779 3237720443804365985579669)
              ·
                refine ⟨151768145803329655574047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3237720443804365985579669 151768145803329655574047)
                ·
                  rfl

theorem cell19_498770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_498770 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498770 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498770 prefixEnd_498770 := by exact prefixLift 498770
  have htrace : WordTrace (prefixWord ++ tailWord_498770) baseStart_498770 baseEnd_498770 := by
    simpa [prefixWord, tailWord_498770, baseEnd_498770] using wordTrace_append hprefix tailTrace_498770
  have hstable : (prefixWord ++ tailWord_498770).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498770).length < 2 ^ (prefixWord ++ tailWord_498770).sum := by decide
  have hdescent : baseEnd_498770 < baseStart_498770 := by decide
  rcases family_descends (prefixWord ++ tailWord_498770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498844 : List Nat := [2, 2, 3, 2, 1, 3, 3, 3]
def baseStart_498844 : Nat := 118140960795 + 498844 * 2 ^ 59
def prefixEnd_498844 : Nat := 4983230072969 + 3 ^ 40 * 498844 * 2
def baseEnd_498844 : Nat := 151790662880919409929401

theorem tailTrace_498844 : CollatzResearch.WordTrace tailWord_498844 prefixEnd_498844 151790662880919409929401 := by
  unfold tailWord_498844
  simp only [CollatzResearch.WordTrace]
  refine ⟨9097167702390429308763793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12129556936520572411685057 9097167702390429308763793)
  ·
    refine ⟨6822875776792821981572845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9097167702390429308763793 6822875776792821981572845)
    ·
      refine ⟨2558578416297308243089817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6822875776792821981572845 2558578416297308243089817)
      ·
        refine ⟨1918933812222981182317363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2558578416297308243089817 1918933812222981182317363)
        ·
          refine ⟨2878400718334471773476045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918933812222981182317363 2878400718334471773476045)
          ·
            refine ⟨1079400269375426915053517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2878400718334471773476045 1079400269375426915053517)
            ·
              refine ⟨404775101015785093145069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1079400269375426915053517 404775101015785093145069)
              ·
                refine ⟨151790662880919409929401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404775101015785093145069 151790662880919409929401)
                ·
                  rfl

theorem cell19_498844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_498844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498844 prefixEnd_498844 := by exact prefixLift 498844
  have htrace : WordTrace (prefixWord ++ tailWord_498844) baseStart_498844 baseEnd_498844 := by
    simpa [prefixWord, tailWord_498844, baseEnd_498844] using wordTrace_append hprefix tailTrace_498844
  have hstable : (prefixWord ++ tailWord_498844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498844).length < 2 ^ (prefixWord ++ tailWord_498844).sum := by decide
  have hdescent : baseEnd_498844 < baseStart_498844 := by decide
  rcases family_descends (prefixWord ++ tailWord_498844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498865 : List Nat := [1, 2, 2, 5, 1, 2, 6]
def baseStart_498865 : Nat := 118140960795 + 498865 * 2 ^ 59
def prefixEnd_498865 : Nat := 4983230072969 + 3 ^ 40 * 498865 * 2
def baseEnd_498865 : Nat := 50599017620799194487559

theorem tailTrace_498865 : CollatzResearch.WordTrace tailWord_498865 prefixEnd_498865 50599017620799194487559 := by
  unfold tailWord_498865
  simp only [CollatzResearch.WordTrace]
  refine ⟨18195101337704779204042049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12130067558469852802694699 18195101337704779204042049)
  ·
    refine ⟨13646326003278584403031537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18195101337704779204042049 13646326003278584403031537)
    ·
      refine ⟨10234744502458938302273653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13646326003278584403031537 10234744502458938302273653)
      ·
        refine ⟨959507297105525465838155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10234744502458938302273653 959507297105525465838155)
        ·
          refine ⟨1439260945658288198757233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959507297105525465838155 1439260945658288198757233)
          ·
            refine ⟨1079445709243716149067925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1439260945658288198757233 1079445709243716149067925)
            ·
              refine ⟨50599017620799194487559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1079445709243716149067925 50599017620799194487559)
              ·
                rfl

theorem cell19_498865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_498865 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498865 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498865 prefixEnd_498865 := by exact prefixLift 498865
  have htrace : WordTrace (prefixWord ++ tailWord_498865) baseStart_498865 baseEnd_498865 := by
    simpa [prefixWord, tailWord_498865, baseEnd_498865] using wordTrace_append hprefix tailTrace_498865
  have hstable : (prefixWord ++ tailWord_498865).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498865).length < 2 ^ (prefixWord ++ tailWord_498865).sum := by decide
  have hdescent : baseEnd_498865 < baseStart_498865 := by decide
  rcases family_descends (prefixWord ++ tailWord_498865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498901 : List Nat := [1, 3, 2, 4, 1, 1, 4, 3]
def baseStart_498901 : Nat := 118140960795 + 498901 * 2 ^ 59
def prefixEnd_498901 : Nat := 4983230072969 + 3 ^ 40 * 498901 * 2
def baseEnd_498901 : Nat := 151808007116360166662579

theorem tailTrace_498901 : CollatzResearch.WordTrace tailWord_498901 prefixEnd_498901 151808007116360166662579 := by
  unfold tailWord_498901
  simp only [CollatzResearch.WordTrace]
  refine ⟨18196414365574357352352557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12130942910382904901568371 18196414365574357352352557)
  ·
    refine ⟨6823655387090384007132209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18196414365574357352352557 6823655387090384007132209)
    ·
      refine ⟨5117741540317788005349157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6823655387090384007132209 5117741540317788005349157)
      ·
        refine ⟨959576538809585251002967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5117741540317788005349157 959576538809585251002967)
        ·
          refine ⟨1439364808214377876504451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959576538809585251002967 1439364808214377876504451)
          ·
            refine ⟨2159047212321566814756677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439364808214377876504451 2159047212321566814756677)
            ·
              refine ⟨404821352310293777766877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2159047212321566814756677 404821352310293777766877)
              ·
                refine ⟨151808007116360166662579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404821352310293777766877 151808007116360166662579)
                ·
                  rfl

theorem cell19_498901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 3].length) (baseStart_498901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498901 prefixEnd_498901 := by exact prefixLift 498901
  have htrace : WordTrace (prefixWord ++ tailWord_498901) baseStart_498901 baseEnd_498901 := by
    simpa [prefixWord, tailWord_498901, baseEnd_498901] using wordTrace_append hprefix tailTrace_498901
  have hstable : (prefixWord ++ tailWord_498901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498901).length < 2 ^ (prefixWord ++ tailWord_498901).sum := by decide
  have hdescent : baseEnd_498901 < baseStart_498901 := by decide
  rcases family_descends (prefixWord ++ tailWord_498901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498903 : List Nat := [1, 1, 3, 2, 1, 2, 6, 3]
def baseStart_498903 : Nat := 118140960795 + 498903 * 2 ^ 59
def prefixEnd_498903 : Nat := 4983230072969 + 3 ^ 40 * 498903 * 2
def baseEnd_498903 : Nat := 151808615686024754618129

theorem tailTrace_498903 : CollatzResearch.WordTrace tailWord_498903 prefixEnd_498903 151808615686024754618129 := by
  unfold tailWord_498903
  simp only [CollatzResearch.WordTrace]
  refine ⟨18196487311567111693925363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12130991541044741129283575 18196487311567111693925363)
  ·
    refine ⟨27294730967350667540888045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18196487311567111693925363 27294730967350667540888045)
    ·
      refine ⟨10235524112756500327833017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27294730967350667540888045 10235524112756500327833017)
      ·
        refine ⟨7676643084567375245874763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10235524112756500327833017 7676643084567375245874763)
        ·
          refine ⟨11514964626851062868812145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7676643084567375245874763 11514964626851062868812145)
          ·
            refine ⟨8636223470138297151609109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11514964626851062868812145 8636223470138297151609109)
            ·
              refine ⟨404822975162732678981677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8636223470138297151609109 404822975162732678981677)
              ·
                refine ⟨151808615686024754618129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404822975162732678981677 151808615686024754618129)
                ·
                  rfl

theorem cell19_498903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 3].length) (baseStart_498903 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498903 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498903 prefixEnd_498903 := by exact prefixLift 498903
  have htrace : WordTrace (prefixWord ++ tailWord_498903) baseStart_498903 baseEnd_498903 := by
    simpa [prefixWord, tailWord_498903, baseEnd_498903] using wordTrace_append hprefix tailTrace_498903
  have hstable : (prefixWord ++ tailWord_498903).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498903).length < 2 ^ (prefixWord ++ tailWord_498903).sum := by decide
  have hdescent : baseEnd_498903 < baseStart_498903 := by decide
  rcases family_descends (prefixWord ++ tailWord_498903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498922 : List Nat := [3, 1, 3, 1, 1, 5, 5]
def baseStart_498922 : Nat := 118140960795 + 498922 * 2 ^ 59
def prefixEnd_498922 : Nat := 4983230072969 + 3 ^ 40 * 498922 * 2
def baseEnd_498922 : Nat := 50604799032612780065285

theorem tailTrace_498922 : CollatzResearch.WordTrace tailWord_498922 prefixEnd_498922 50604799032612780065285 := by
  unfold tailWord_498922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4549295074624569484716755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12131453532332185292578013 4549295074624569484716755)
  ·
    refine ⟨6823942611936854227075133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4549295074624569484716755 6823942611936854227075133)
    ·
      refine ⟨2558978479476320335153175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6823942611936854227075133 2558978479476320335153175)
      ·
        refine ⟨3838467719214480502729763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558978479476320335153175 3838467719214480502729763)
        ·
          refine ⟨5757701578821720754094645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3838467719214480502729763 5757701578821720754094645)
          ·
            refine ⟨539784523014536320696373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5757701578821720754094645 539784523014536320696373)
            ·
              refine ⟨50604799032612780065285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 539784523014536320696373 50604799032612780065285)
              ·
                rfl

theorem cell19_498922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_498922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498922 prefixEnd_498922 := by exact prefixLift 498922
  have htrace : WordTrace (prefixWord ++ tailWord_498922) baseStart_498922 baseEnd_498922 := by
    simpa [prefixWord, tailWord_498922, baseEnd_498922] using wordTrace_append hprefix tailTrace_498922
  have hstable : (prefixWord ++ tailWord_498922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498922).length < 2 ^ (prefixWord ++ tailWord_498922).sum := by decide
  have hdescent : baseEnd_498922 < baseStart_498922 := by decide
  rcases family_descends (prefixWord ++ tailWord_498922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498924 : List Nat := [2, 2, 1, 1, 2, 4, 7]
def baseStart_498924 : Nat := 118140960795 + 498924 * 2 ^ 59
def prefixEnd_498924 : Nat := 4983230072969 + 3 ^ 40 * 498924 * 2
def baseEnd_498924 : Nat := 50605001889167642717135

theorem tailTrace_498924 : CollatzResearch.WordTrace tailWord_498924 prefixEnd_498924 50605001889167642717135 := by
  unfold tailWord_498924
  simp only [CollatzResearch.WordTrace]
  refine ⟨9098626622245516140219913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12131502162994021520293217 9098626622245516140219913)
  ·
    refine ⟨6823969966684137105164935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9098626622245516140219913 6823969966684137105164935)
    ·
      refine ⟨10235954950026205657747403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6823969966684137105164935 10235954950026205657747403)
      ·
        refine ⟨15353932425039308486621105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10235954950026205657747403 15353932425039308486621105)
        ·
          refine ⟨11515449318779481364965829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15353932425039308486621105 11515449318779481364965829)
          ·
            refine ⟨2159146747271152755931093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11515449318779481364965829 2159146747271152755931093)
            ·
              refine ⟨50605001889167642717135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2159146747271152755931093 50605001889167642717135)
              ·
                rfl

theorem cell19_498924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_498924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498924 prefixEnd_498924 := by exact prefixLift 498924
  have htrace : WordTrace (prefixWord ++ tailWord_498924) baseStart_498924 baseEnd_498924 := by
    simpa [prefixWord, tailWord_498924, baseEnd_498924] using wordTrace_append hprefix tailTrace_498924
  have hstable : (prefixWord ++ tailWord_498924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498924).length < 2 ^ (prefixWord ++ tailWord_498924).sum := by decide
  have hdescent : baseEnd_498924 < baseStart_498924 := by decide
  rcases family_descends (prefixWord ++ tailWord_498924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498943 : List Nat := [1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_498943 : Nat := 118140960795 + 498943 * 2 ^ 59
def prefixEnd_498943 : Nat := 4983230072969 + 3 ^ 40 * 498943 * 2
def baseEnd_498943 : Nat := 151820787079316513729131

theorem tailTrace_498943 : CollatzResearch.WordTrace tailWord_498943 prefixEnd_498943 151820787079316513729131 := by
  unfold tailWord_498943
  simp only [CollatzResearch.WordTrace]
  refine ⟨18197946231422198525381483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12131964154281465683587655 18197946231422198525381483)
  ·
    refine ⟨27296919347133297788072225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18197946231422198525381483 27296919347133297788072225)
    ·
      refine ⟨20472689510349973341054169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27296919347133297788072225 20472689510349973341054169)
      ·
        refine ⟨15354517132762480005790627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20472689510349973341054169 15354517132762480005790627)
        ·
          refine ⟨23031775699143720008685941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15354517132762480005790627 23031775699143720008685941)
          ·
            refine ⟨2159228971794723750814307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23031775699143720008685941 2159228971794723750814307)
            ·
              refine ⟨3238843457692085626221461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159228971794723750814307 3238843457692085626221461)
              ·
                refine ⟨151820787079316513729131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3238843457692085626221461 151820787079316513729131)
                ·
                  rfl

theorem cell19_498943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_498943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498943 prefixEnd_498943 := by exact prefixLift 498943
  have htrace : WordTrace (prefixWord ++ tailWord_498943) baseStart_498943 baseEnd_498943 := by
    simpa [prefixWord, tailWord_498943, baseEnd_498943] using wordTrace_append hprefix tailTrace_498943
  have hstable : (prefixWord ++ tailWord_498943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498943).length < 2 ^ (prefixWord ++ tailWord_498943).sum := by decide
  have hdescent : baseEnd_498943 < baseStart_498943 := by decide
  rcases family_descends (prefixWord ++ tailWord_498943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498981 : List Nat := [1, 3, 1, 2, 4, 8]
def baseStart_498981 : Nat := 118140960795 + 498981 * 2 ^ 59
def prefixEnd_498981 : Nat := 4983230072969 + 3 ^ 40 * 498981 * 2
def baseEnd_498981 : Nat := 16870261100327076098287

theorem tailTrace_498981 : CollatzResearch.WordTrace tailWord_498981 prefixEnd_498981 16870261100327076098287 := by
  unfold tailWord_498981
  simp only [CollatzResearch.WordTrace]
  refine ⟨18199332205284531015264797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12132888136856354010176531 18199332205284531015264797)
  ·
    refine ⟨6824749576981699130724299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18199332205284531015264797 6824749576981699130724299)
    ·
      refine ⟨10237124365472548696086449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6824749576981699130724299 10237124365472548696086449)
      ·
        refine ⟨7677843274104411522064837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10237124365472548696086449 7677843274104411522064837)
        ·
          refine ⟨1439595613894577160387157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7677843274104411522064837 1439595613894577160387157)
          ·
            refine ⟨16870261100327076098287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1439595613894577160387157 16870261100327076098287)
            ·
              rfl

theorem cell19_498981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 8].length) (baseStart_498981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498981 prefixEnd_498981 := by exact prefixLift 498981
  have htrace : WordTrace (prefixWord ++ tailWord_498981) baseStart_498981 baseEnd_498981 := by
    simpa [prefixWord, tailWord_498981, baseEnd_498981] using wordTrace_append hprefix tailTrace_498981
  have hstable : (prefixWord ++ tailWord_498981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498981).length < 2 ^ (prefixWord ++ tailWord_498981).sum := by decide
  have hdescent : baseEnd_498981 < baseStart_498981 := by decide
  rcases family_descends (prefixWord ++ tailWord_498981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499030 : List Nat := [5, 2, 3, 1, 1, 1, 6]
def baseStart_499030 : Nat := 118140960795 + 499030 * 2 ^ 59
def prefixEnd_499030 : Nat := 4983230072969 + 3 ^ 40 * 499030 * 2
def baseEnd_499030 : Nat := 50615753286575363265187

theorem tailTrace_499030 : CollatzResearch.WordTrace tailWord_499030 prefixEnd_499030 50615753286575363265187 := by
  unfold tailWord_499030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1137569961381688273987409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12134079588071341589199029 1137569961381688273987409)
  ·
    refine ⟨853177471036266205490557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1137569961381688273987409 853177471036266205490557)
    ·
      refine ⟨319941551638599827058959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 853177471036266205490557 319941551638599827058959)
      ·
        refine ⟨479912327457899740588439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319941551638599827058959 479912327457899740588439)
        ·
          refine ⟨719868491186849610882659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479912327457899740588439 719868491186849610882659)
          ·
            refine ⟨1079802736780274416323989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719868491186849610882659 1079802736780274416323989)
            ·
              refine ⟨50615753286575363265187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1079802736780274416323989 50615753286575363265187)
              ·
                rfl

theorem cell19_499030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 6].length) (baseStart_499030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499030 prefixEnd_499030 := by exact prefixLift 499030
  have htrace : WordTrace (prefixWord ++ tailWord_499030) baseStart_499030 baseEnd_499030 := by
    simpa [prefixWord, tailWord_499030, baseEnd_499030] using wordTrace_append hprefix tailTrace_499030
  have hstable : (prefixWord ++ tailWord_499030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499030).length < 2 ^ (prefixWord ++ tailWord_499030).sum := by decide
  have hdescent : baseEnd_499030 < baseStart_499030 := by decide
  rcases family_descends (prefixWord ++ tailWord_499030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499070 : List Nat := [4, 2, 3, 2, 1, 1, 1, 5]
def baseStart_499070 : Nat := 118140960795 + 499070 * 2 ^ 59
def prefixEnd_499070 : Nat := 4983230072969 + 3 ^ 40 * 499070 * 2
def baseEnd_499070 : Nat := 151859431253017848906563

theorem tailTrace_499070 : CollatzResearch.WordTrace tailWord_499070 prefixEnd_499070 151859431253017848906563 := by
  unfold tailWord_499070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2275322287745262401906833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12135052201308066143503109 2275322287745262401906833)
  ·
    refine ⟨1706491715808946801430125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2275322287745262401906833 1706491715808946801430125)
    ·
      refine ⟨639934393428355050536297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1706491715808946801430125 639934393428355050536297)
      ·
        refine ⟨479950795071266287902223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639934393428355050536297 479950795071266287902223)
        ·
          refine ⟨719926192606899431853335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479950795071266287902223 719926192606899431853335)
          ·
            refine ⟨1079889288910349147780003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719926192606899431853335 1079889288910349147780003)
            ·
              refine ⟨1619833933365523721670005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079889288910349147780003 1619833933365523721670005)
              ·
                refine ⟨151859431253017848906563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1619833933365523721670005 151859431253017848906563)
                ·
                  rfl

theorem cell19_499070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_499070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499070 prefixEnd_499070 := by exact prefixLift 499070
  have htrace : WordTrace (prefixWord ++ tailWord_499070) baseStart_499070 baseEnd_499070 := by
    simpa [prefixWord, tailWord_499070, baseEnd_499070] using wordTrace_append hprefix tailTrace_499070
  have hstable : (prefixWord ++ tailWord_499070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499070).length < 2 ^ (prefixWord ++ tailWord_499070).sum := by decide
  have hdescent : baseEnd_499070 < baseStart_499070 := by decide
  rcases family_descends (prefixWord ++ tailWord_499070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499133 : List Nat := [1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_499133 : Nat := 118140960795 + 499133 * 2 ^ 59
def prefixEnd_499133 : Nat := 4983230072969 + 3 ^ 40 * 499133 * 2
def baseEnd_499133 : Nat := 151878601197452369506391

theorem tailTrace_499133 : CollatzResearch.WordTrace tailWord_499133 prefixEnd_499133 151878601197452369506391 := by
  unfold tailWord_499133
  simp only [CollatzResearch.WordTrace]
  refine ⟨18204876100733860974798053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12136584067155907316532035 18204876100733860974798053)
  ·
    refine ⟨3413414268887598932774635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18204876100733860974798053 3413414268887598932774635)
    ·
      refine ⟨5120121403331398399161953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3413414268887598932774635 5120121403331398399161953)
      ·
        refine ⟨3840091052498548799371465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5120121403331398399161953 3840091052498548799371465)
        ·
          refine ⟨2880068289373911599528599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3840091052498548799371465 2880068289373911599528599)
          ·
            refine ⟨4320102434060867399292899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880068289373911599528599 4320102434060867399292899)
            ·
              refine ⟨6480153651091301098939349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320102434060867399292899 6480153651091301098939349)
              ·
                refine ⟨151878601197452369506391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6480153651091301098939349 151878601197452369506391)
                ·
                  rfl

theorem cell19_499133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_499133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499133 prefixEnd_499133 := by exact prefixLift 499133
  have htrace : WordTrace (prefixWord ++ tailWord_499133) baseStart_499133 baseEnd_499133 := by
    simpa [prefixWord, tailWord_499133, baseEnd_499133] using wordTrace_append hprefix tailTrace_499133
  have hstable : (prefixWord ++ tailWord_499133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499133).length < 2 ^ (prefixWord ++ tailWord_499133).sum := by decide
  have hdescent : baseEnd_499133 < baseStart_499133 := by decide
  rcases family_descends (prefixWord ++ tailWord_499133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499169 : List Nat := [1, 2, 3, 1, 2, 5, 1, 4]
def baseStart_499169 : Nat := 118140960795 + 499169 * 2 ^ 59
def prefixEnd_499169 : Nat := 4983230072969 + 3 ^ 40 * 499169 * 2
def baseEnd_499169 : Nat := 151889555451414952706293

theorem tailTrace_499169 : CollatzResearch.WordTrace tailWord_499169 prefixEnd_499169 151889555451414952706293 := by
  unfold tailWord_499169
  simp only [CollatzResearch.WordTrace]
  refine ⟨18206189128603439123108561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12137459419068959415405707 18206189128603439123108561)
  ·
    refine ⟨13654641846452579342331421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18206189128603439123108561 13654641846452579342331421)
    ·
      refine ⟨5120490692419717253374283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13654641846452579342331421 5120490692419717253374283)
      ·
        refine ⟨7680736038629575880061425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5120490692419717253374283 7680736038629575880061425)
        ·
          refine ⟨5760552028972181910046069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7680736038629575880061425 5760552028972181910046069)
          ·
            refine ⟨540051752716142054066819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5760552028972181910046069 540051752716142054066819)
            ·
              refine ⟨810077629074213081100229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540051752716142054066819 810077629074213081100229)
              ·
                refine ⟨151889555451414952706293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 810077629074213081100229 151889555451414952706293)
                ·
                  rfl

theorem cell19_499169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_499169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499169 prefixEnd_499169 := by exact prefixLift 499169
  have htrace : WordTrace (prefixWord ++ tailWord_499169) baseStart_499169 baseEnd_499169 := by
    simpa [prefixWord, tailWord_499169, baseEnd_499169] using wordTrace_append hprefix tailTrace_499169
  have hstable : (prefixWord ++ tailWord_499169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499169).length < 2 ^ (prefixWord ++ tailWord_499169).sum := by decide
  have hdescent : baseEnd_499169 < baseStart_499169 := by decide
  rcases family_descends (prefixWord ++ tailWord_499169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499186 : List Nat := [3, 2, 1, 4, 1, 2, 3, 3]
def baseStart_499186 : Nat := 118140960795 + 499186 * 2 ^ 59
def prefixEnd_499186 : Nat := 4983230072969 + 3 ^ 40 * 499186 * 2
def baseEnd_499186 : Nat := 151894728293563950328469

theorem tailTrace_499186 : CollatzResearch.WordTrace tailWord_499186 prefixEnd_499186 151894728293563950328469 := by
  unfold tailWord_499186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4551702292385462756619353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12137872779694567350984941 4551702292385462756619353)
  ·
    refine ⟨3413776719289097067464515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4551702292385462756619353 3413776719289097067464515)
    ·
      refine ⟨5120665078933645601196773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3413776719289097067464515 5120665078933645601196773)
      ·
        refine ⟨960124702300058550224395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5120665078933645601196773 960124702300058550224395)
        ·
          refine ⟨1440187053450087825336593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960124702300058550224395 1440187053450087825336593)
          ·
            refine ⟨1080140290087565869002445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1440187053450087825336593 1080140290087565869002445)
            ·
              refine ⟨405052608782837200875917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1080140290087565869002445 405052608782837200875917)
              ·
                refine ⟨151894728293563950328469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405052608782837200875917 151894728293563950328469)
                ·
                  rfl

theorem cell19_499186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_499186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499186 prefixEnd_499186 := by exact prefixLift 499186
  have htrace : WordTrace (prefixWord ++ tailWord_499186) baseStart_499186 baseEnd_499186 := by
    simpa [prefixWord, tailWord_499186, baseEnd_499186] using wordTrace_append hprefix tailTrace_499186
  have hstable : (prefixWord ++ tailWord_499186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499186).length < 2 ^ (prefixWord ++ tailWord_499186).sum := by decide
  have hdescent : baseEnd_499186 < baseStart_499186 := by decide
  rcases family_descends (prefixWord ++ tailWord_499186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499228 : List Nat := [2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_499228 : Nat := 118140960795 + 499228 * 2 ^ 59
def prefixEnd_499228 : Nat := 4983230072969 + 3 ^ 40 * 499228 * 2
def baseEnd_499228 : Nat := 151907508256520297395021

theorem tailTrace_499228 : CollatzResearch.WordTrace tailWord_499228 prefixEnd_499228 151907508256520297395021 := by
  unfold tailWord_499228
  simp only [CollatzResearch.WordTrace]
  refine ⟨9104170517694846099753169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12138894023593128133004225 9104170517694846099753169)
  ·
    refine ⟨6828127888271134574814877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9104170517694846099753169 6828127888271134574814877)
    ·
      refine ⟨2560547958101675465555579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6828127888271134574814877 2560547958101675465555579)
      ·
        refine ⟨3840821937152513198333369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2560547958101675465555579 3840821937152513198333369)
        ·
          refine ⟨2880616452864384898750027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3840821937152513198333369 2880616452864384898750027)
          ·
            refine ⟨4320924679296577348125041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880616452864384898750027 4320924679296577348125041)
            ·
              refine ⟨3240693509472433011093781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4320924679296577348125041 3240693509472433011093781)
              ·
                refine ⟨151907508256520297395021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3240693509472433011093781 151907508256520297395021)
                ·
                  rfl

theorem cell19_499228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_499228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499228 prefixEnd_499228 := by exact prefixLift 499228
  have htrace : WordTrace (prefixWord ++ tailWord_499228) baseStart_499228 baseEnd_499228 := by
    simpa [prefixWord, tailWord_499228, baseEnd_499228] using wordTrace_append hprefix tailTrace_499228
  have hstable : (prefixWord ++ tailWord_499228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499228).length < 2 ^ (prefixWord ++ tailWord_499228).sum := by decide
  have hdescent : baseEnd_499228 < baseStart_499228 := by decide
  rcases family_descends (prefixWord ++ tailWord_499228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499336 : List Nat := [2, 1, 3, 5, 2, 1, 1, 4]
def baseStart_499336 : Nat := 118140960795 + 499336 * 2 ^ 59
def prefixEnd_499336 : Nat := 4983230072969 + 3 ^ 40 * 499336 * 2
def baseEnd_499336 : Nat := 151940371018408046994727

theorem tailTrace_499336 : CollatzResearch.WordTrace tailWord_499336 prefixEnd_499336 151940371018408046994727 := by
  unfold tailWord_499336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9106140059499213322218931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12141520079332284429625241 9106140059499213322218931)
  ·
    refine ⟨13659210089248819983328397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9106140059499213322218931 13659210089248819983328397)
    ·
      refine ⟨5122203783468307493748149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13659210089248819983328397 5122203783468307493748149)
      ·
        refine ⟨480206604700153827538889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5122203783468307493748149 480206604700153827538889)
        ·
          refine ⟨360154953525115370654167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480206604700153827538889 360154953525115370654167)
          ·
            refine ⟨540232430287673055981251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360154953525115370654167 540232430287673055981251)
            ·
              refine ⟨810348645431509583971877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540232430287673055981251 810348645431509583971877)
              ·
                refine ⟨151940371018408046994727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 810348645431509583971877 151940371018408046994727)
                ·
                  rfl

theorem cell19_499336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_499336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499336 prefixEnd_499336 := by exact prefixLift 499336
  have htrace : WordTrace (prefixWord ++ tailWord_499336) baseStart_499336 baseEnd_499336 := by
    simpa [prefixWord, tailWord_499336, baseEnd_499336] using wordTrace_append hprefix tailTrace_499336
  have hstable : (prefixWord ++ tailWord_499336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499336).length < 2 ^ (prefixWord ++ tailWord_499336).sum := by decide
  have hdescent : baseEnd_499336 < baseStart_499336 := by decide
  rcases family_descends (prefixWord ++ tailWord_499336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499418 : List Nat := [3, 1, 1, 2, 2, 4, 1, 5]
def baseStart_499418 : Nat := 118140960795 + 499418 * 2 ^ 59
def prefixEnd_499418 : Nat := 4983230072969 + 3 ^ 40 * 499418 * 2
def baseEnd_499418 : Nat := 151965322374656153172281

theorem tailTrace_499418 : CollatzResearch.WordTrace tailWord_499418 prefixEnd_499418 151965322374656153172281 := by
  unfold tailWord_499418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4553817726175338662230727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12143513936467569765948605 4553817726175338662230727)
  ·
    refine ⟨6830726589263007993346091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4553817726175338662230727 6830726589263007993346091)
    ·
      refine ⟨10246089883894511990019137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6830726589263007993346091 10246089883894511990019137)
      ·
        refine ⟨7684567412920883992514353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10246089883894511990019137 7684567412920883992514353)
        ·
          refine ⟨5763425559690662994385765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7684567412920883992514353 5763425559690662994385765)
          ·
            refine ⟨1080642292441999311447331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5763425559690662994385765 1080642292441999311447331)
            ·
              refine ⟨1620963438662998967170997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080642292441999311447331 1620963438662998967170997)
              ·
                refine ⟨151965322374656153172281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1620963438662998967170997 151965322374656153172281)
                ·
                  rfl

theorem cell19_499418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_499418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499418 prefixEnd_499418 := by exact prefixLift 499418
  have htrace : WordTrace (prefixWord ++ tailWord_499418) baseStart_499418 baseEnd_499418 := by
    simpa [prefixWord, tailWord_499418, baseEnd_499418] using wordTrace_append hprefix tailTrace_499418
  have hstable : (prefixWord ++ tailWord_499418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499418).length < 2 ^ (prefixWord ++ tailWord_499418).sum := by decide
  have hdescent : baseEnd_499418 < baseStart_499418 := by decide
  rcases family_descends (prefixWord ++ tailWord_499418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499437 : List Nat := [1, 5, 1, 2, 1, 2, 7]
def baseStart_499437 : Nat := 118140960795 + 499437 * 2 ^ 59
def prefixEnd_499437 : Nat := 4983230072969 + 3 ^ 40 * 499437 * 2
def baseEnd_499437 : Nat := 50657034595489912916669

theorem tailTrace_499437 : CollatzResearch.WordTrace tailWord_499437 prefixEnd_499437 50657034595489912916669 := by
  unfold tailWord_499437
  simp only [CollatzResearch.WordTrace]
  refine ⟨18215963891632520893864565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12143975927755013929243043 18215963891632520893864565)
  ·
    refine ⟨1707746614840548833799803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18215963891632520893864565 1707746614840548833799803)
    ·
      refine ⟨2561619922260823250699705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1707746614840548833799803 2561619922260823250699705)
      ·
        refine ⟨1921214941695617438024779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2561619922260823250699705 1921214941695617438024779)
        ·
          refine ⟨2881822412543426157037169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921214941695617438024779 2881822412543426157037169)
          ·
            refine ⟨2161366809407569617777877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2881822412543426157037169 2161366809407569617777877)
            ·
              refine ⟨50657034595489912916669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2161366809407569617777877 50657034595489912916669)
              ·
                rfl

theorem cell19_499437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_499437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499437 prefixEnd_499437 := by exact prefixLift 499437
  have htrace : WordTrace (prefixWord ++ tailWord_499437) baseStart_499437 baseEnd_499437 := by
    simpa [prefixWord, tailWord_499437, baseEnd_499437] using wordTrace_append hprefix tailTrace_499437
  have hstable : (prefixWord ++ tailWord_499437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499437).length < 2 ^ (prefixWord ++ tailWord_499437).sum := by decide
  have hdescent : baseEnd_499437 < baseStart_499437 := by decide
  rcases family_descends (prefixWord ++ tailWord_499437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499509 : List Nat := [1, 3, 3, 1, 5, 1, 1, 4]
def baseStart_499509 : Nat := 118140960795 + 499509 * 2 ^ 59
def prefixEnd_499509 : Nat := 4983230072969 + 3 ^ 40 * 499509 * 2
def baseEnd_499509 : Nat := 151993012294394905149811

theorem tailTrace_499509 : CollatzResearch.WordTrace tailWord_499509 prefixEnd_499509 151993012294394905149811 := by
  unfold tailWord_499509
  simp only [CollatzResearch.WordTrace]
  refine ⟨18218589947371677190485581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12145726631581118126990387 18218589947371677190485581)
  ·
    refine ⟨6831971230264378946432093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18218589947371677190485581 6831971230264378946432093)
    ·
      refine ⟨2561989211349142104912035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6831971230264378946432093 2561989211349142104912035)
      ·
        refine ⟨3842983817023713157368053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561989211349142104912035 3842983817023713157368053)
        ·
          refine ⟨360279732845973108503255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3842983817023713157368053 360279732845973108503255)
          ·
            refine ⟨540419599268959662754883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360279732845973108503255 540419599268959662754883)
            ·
              refine ⟨810629398903439494132325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540419599268959662754883 810629398903439494132325)
              ·
                refine ⟨151993012294394905149811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 810629398903439494132325 151993012294394905149811)
                ·
                  rfl

theorem cell19_499509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 4].length) (baseStart_499509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499509 prefixEnd_499509 := by exact prefixLift 499509
  have htrace : WordTrace (prefixWord ++ tailWord_499509) baseStart_499509 baseEnd_499509 := by
    simpa [prefixWord, tailWord_499509, baseEnd_499509] using wordTrace_append hprefix tailTrace_499509
  have hstable : (prefixWord ++ tailWord_499509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499509).length < 2 ^ (prefixWord ++ tailWord_499509).sum := by decide
  have hdescent : baseEnd_499509 < baseStart_499509 := by decide
  rcases family_descends (prefixWord ++ tailWord_499509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499526 : List Nat := [6, 1, 1, 2, 1, 2, 3, 3]
def baseStart_499526 : Nat := 118140960795 + 499526 * 2 ^ 59
def prefixEnd_499526 : Nat := 4983230072969 + 3 ^ 40 * 499526 * 2
def baseEnd_499526 : Nat := 151998185136543902771987

theorem tailTrace_499526 : CollatzResearch.WordTrace tailWord_499526 prefixEnd_499526 151998185136543902771987 := by
  unfold tailWord_499526
  simp only [CollatzResearch.WordTrace]
  refine ⟨569350312134690284182951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12146139992206726062569621 569350312134690284182951)
  ·
    refine ⟨854025468202035426274427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 569350312134690284182951 854025468202035426274427)
    ·
      refine ⟨1281038202303053139411641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854025468202035426274427 1281038202303053139411641)
      ·
        refine ⟨960778651727289854558731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1281038202303053139411641 960778651727289854558731)
        ·
          refine ⟨1441167977590934781838097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960778651727289854558731 1441167977590934781838097)
          ·
            refine ⟨1080875983193201086378573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1441167977590934781838097 1080875983193201086378573)
            ·
              refine ⟨405328493697450407391965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1080875983193201086378573 405328493697450407391965)
              ·
                refine ⟨151998185136543902771987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405328493697450407391965 151998185136543902771987)
                ·
                  rfl

theorem cell19_499526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_499526 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499526 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499526 prefixEnd_499526 := by exact prefixLift 499526
  have htrace : WordTrace (prefixWord ++ tailWord_499526) baseStart_499526 baseEnd_499526 := by
    simpa [prefixWord, tailWord_499526, baseEnd_499526] using wordTrace_append hprefix tailTrace_499526
  have hstable : (prefixWord ++ tailWord_499526).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499526).length < 2 ^ (prefixWord ++ tailWord_499526).sum := by decide
  have hdescent : baseEnd_499526 < baseStart_499526 := by decide
  rcases family_descends (prefixWord ++ tailWord_499526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499553 : List Nat := [1, 2, 3, 1, 1, 1, 10]
def baseStart_499553 : Nat := 118140960795 + 499553 * 2 ^ 59
def prefixEnd_499553 : Nat := 4983230072969 + 3 ^ 40 * 499553 * 2
def baseEnd_499553 : Nat := 50668800275671946723971

theorem tailTrace_499553 : CollatzResearch.WordTrace tailWord_499553 prefixEnd_499553 50668800275671946723971 := by
  unfold tailWord_499553
  simp only [CollatzResearch.WordTrace]
  refine ⟨18220194759212272705087313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12146796506141515136724875 18220194759212272705087313)
  ·
    refine ⟨13665146069409204528815485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18220194759212272705087313 13665146069409204528815485)
    ·
      refine ⟨5124429776028451698305807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13665146069409204528815485 5124429776028451698305807)
      ·
        refine ⟨7686644664042677547458711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5124429776028451698305807 7686644664042677547458711)
        ·
          refine ⟨11529966996064016321188067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7686644664042677547458711 11529966996064016321188067)
          ·
            refine ⟨17294950494096024481782101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529966996064016321188067 17294950494096024481782101)
            ·
              refine ⟨50668800275671946723971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17294950494096024481782101 50668800275671946723971)
              ·
                rfl

theorem cell19_499553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_499553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499553 prefixEnd_499553 := by exact prefixLift 499553
  have htrace : WordTrace (prefixWord ++ tailWord_499553) baseStart_499553 baseEnd_499553 := by
    simpa [prefixWord, tailWord_499553, baseEnd_499553] using wordTrace_append hprefix tailTrace_499553
  have hstable : (prefixWord ++ tailWord_499553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499553).length < 2 ^ (prefixWord ++ tailWord_499553).sum := by decide
  have hdescent : baseEnd_499553 < baseStart_499553 := by decide
  rcases family_descends (prefixWord ++ tailWord_499553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499587 : List Nat := [1, 1, 1, 3, 4, 4, 2, 3]
def baseStart_499587 : Nat := 118140960795 + 499587 * 2 ^ 59
def prefixEnd_499587 : Nat := 4983230072969 + 3 ^ 40 * 499587 * 2
def baseEnd_499587 : Nat := 152016746511313835416265

theorem tailTrace_499587 : CollatzResearch.WordTrace tailWord_499587 prefixEnd_499587 152016746511313835416265 := by
  unfold tailWord_499587
  simp only [CollatzResearch.WordTrace]
  refine ⟨18221434841089096511825015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12147623227392731007883343 18221434841089096511825015)
  ·
    refine ⟨27332152261633644767737523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18221434841089096511825015 27332152261633644767737523)
    ·
      refine ⟨40998228392450467151606285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27332152261633644767737523 40998228392450467151606285)
      ·
        refine ⟨15374335647168925181852357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40998228392450467151606285 15374335647168925181852357)
        ·
          refine ⟨2882687933844173471597317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15374335647168925181852357 2882687933844173471597317)
          ·
            refine ⟨540503987595782525924497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2882687933844173471597317 540503987595782525924497)
            ·
              refine ⟨405377990696836894443373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540503987595782525924497 405377990696836894443373)
              ·
                refine ⟨152016746511313835416265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405377990696836894443373 152016746511313835416265)
                ·
                  rfl

theorem cell19_499587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 3].length) (baseStart_499587 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499587 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499587 prefixEnd_499587 := by exact prefixLift 499587
  have htrace : WordTrace (prefixWord ++ tailWord_499587) baseStart_499587 baseEnd_499587 := by
    simpa [prefixWord, tailWord_499587, baseEnd_499587] using wordTrace_append hprefix tailTrace_499587
  have hstable : (prefixWord ++ tailWord_499587).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499587).length < 2 ^ (prefixWord ++ tailWord_499587).sum := by decide
  have hdescent : baseEnd_499587 < baseStart_499587 := by decide
  rcases family_descends (prefixWord ++ tailWord_499587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499646 : List Nat := [4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_499646 : Nat := 118140960795 + 499646 * 2 ^ 59
def prefixEnd_499646 : Nat := 4983230072969 + 3 ^ 40 * 499646 * 2
def baseEnd_499646 : Nat := 152034699316419180104993

theorem tailTrace_499646 : CollatzResearch.WordTrace tailWord_499646 prefixEnd_499646 152034699316419180104993 := by
  unfold tailWord_499646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2277948343484418698527849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12149057831916899725481861 2277948343484418698527849)
  ·
    refine ⟨1708461257613314023895887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2277948343484418698527849 1708461257613314023895887)
    ·
      refine ⟨2562691886419971035843831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1708461257613314023895887 2562691886419971035843831)
      ·
        refine ⟨3844037829629956553765747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2562691886419971035843831 3844037829629956553765747)
        ·
          refine ⟨5766056744444934830648621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844037829629956553765747 5766056744444934830648621)
          ·
            refine ⟨2162271279166850561493233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5766056744444934830648621 2162271279166850561493233)
            ·
              refine ⟨1621703459375137921119925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2162271279166850561493233 1621703459375137921119925)
              ·
                refine ⟨152034699316419180104993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1621703459375137921119925 152034699316419180104993)
                ·
                  rfl

theorem cell19_499646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_499646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499646 prefixEnd_499646 := by exact prefixLift 499646
  have htrace : WordTrace (prefixWord ++ tailWord_499646) baseStart_499646 baseEnd_499646 := by
    simpa [prefixWord, tailWord_499646, baseEnd_499646] using wordTrace_append hprefix tailTrace_499646
  have hstable : (prefixWord ++ tailWord_499646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499646).length < 2 ^ (prefixWord ++ tailWord_499646).sum := by decide
  have hdescent : baseEnd_499646 < baseStart_499646 := by decide
  rcases family_descends (prefixWord ++ tailWord_499646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499648 : List Nat := [2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_499648 : Nat := 118140960795 + 499648 * 2 ^ 59
def prefixEnd_499648 : Nat := 4983230072969 + 3 ^ 40 * 499648 * 2
def baseEnd_499648 : Nat := 152035307886083768060543

theorem tailTrace_499648 : CollatzResearch.WordTrace tailWord_499648 prefixEnd_499648 152035307886083768060543 := by
  unfold tailWord_499648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9111829846934051964897799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12149106462578735953197065 9111829846934051964897799)
  ·
    refine ⟨13667744770401077947346699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9111829846934051964897799 13667744770401077947346699)
    ·
      refine ⟨20501617155601616921020049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13667744770401077947346699 20501617155601616921020049)
      ·
        refine ⟨15376212866701212690765037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20501617155601616921020049 15376212866701212690765037)
        ·
          refine ⟨5766079825012954759036889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15376212866701212690765037 5766079825012954759036889)
          ·
            refine ⟨4324559868759716069277667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5766079825012954759036889 4324559868759716069277667)
            ·
              refine ⟨6486839803139574103916501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324559868759716069277667 6486839803139574103916501)
              ·
                refine ⟨152035307886083768060543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6486839803139574103916501 152035307886083768060543)
                ·
                  rfl

theorem cell19_499648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_499648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499648 prefixEnd_499648 := by exact prefixLift 499648
  have htrace : WordTrace (prefixWord ++ tailWord_499648) baseStart_499648 baseEnd_499648 := by
    simpa [prefixWord, tailWord_499648, baseEnd_499648] using wordTrace_append hprefix tailTrace_499648
  have hstable : (prefixWord ++ tailWord_499648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499648).length < 2 ^ (prefixWord ++ tailWord_499648).sum := by decide
  have hdescent : baseEnd_499648 < baseStart_499648 := by decide
  rcases family_descends (prefixWord ++ tailWord_499648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499676 : List Nat := [2, 2, 6, 1, 2, 1, 1, 4]
def baseStart_499676 : Nat := 118140960795 + 499676 * 2 ^ 59
def prefixEnd_499676 : Nat := 4983230072969 + 3 ^ 40 * 499676 * 2
def baseEnd_499676 : Nat := 152043827861387999438245

theorem tailTrace_499676 : CollatzResearch.WordTrace tailWord_499676 prefixEnd_499676 152043827861387999438245 := by
  unfold tailWord_499676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9112340468883332355907441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12149787291844443141209921 9112340468883332355907441)
  ·
    refine ⟨6834255351662499266930581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9112340468883332355907441 6834255351662499266930581)
    ·
      refine ⟨320355719609179653137371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6834255351662499266930581 320355719609179653137371)
      ·
        refine ⟨480533579413769479706057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320355719609179653137371 480533579413769479706057)
        ·
          refine ⟨360400184560327109779543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480533579413769479706057 360400184560327109779543)
          ·
            refine ⟨540600276840490664669315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360400184560327109779543 540600276840490664669315)
            ·
              refine ⟨810900415260735997003973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540600276840490664669315 810900415260735997003973)
              ·
                refine ⟨152043827861387999438245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 810900415260735997003973 152043827861387999438245)
                ·
                  rfl

theorem cell19_499676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_499676 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499676 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499676 prefixEnd_499676 := by exact prefixLift 499676
  have htrace : WordTrace (prefixWord ++ tailWord_499676) baseStart_499676 baseEnd_499676 := by
    simpa [prefixWord, tailWord_499676, baseEnd_499676] using wordTrace_append hprefix tailTrace_499676
  have hstable : (prefixWord ++ tailWord_499676).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499676).length < 2 ^ (prefixWord ++ tailWord_499676).sum := by decide
  have hdescent : baseEnd_499676 < baseStart_499676 := by decide
  rcases family_descends (prefixWord ++ tailWord_499676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499722 : List Nat := [3, 1, 2, 2, 4, 1, 6]
def baseStart_499722 : Nat := 118140960795 + 499722 * 2 ^ 59
def prefixEnd_499722 : Nat := 4983230072969 + 3 ^ 40 * 499722 * 2
def baseEnd_499722 : Nat := 50685941654557840805299

theorem tailTrace_499722 : CollatzResearch.WordTrace tailWord_499722 prefixEnd_499722 50685941654557840805299 := by
  unfold tailWord_499722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4556589673900003641997355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12150905797066676378659613 4556589673900003641997355)
  ·
    refine ⟨6834884510850005462996033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4556589673900003641997355 6834884510850005462996033)
    ·
      refine ⟨5126163383137504097247025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6834884510850005462996033 5126163383137504097247025)
      ·
        refine ⟨3844622537353128072935269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5126163383137504097247025 3844622537353128072935269)
        ·
          refine ⟨720866725753711513675363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3844622537353128072935269 720866725753711513675363)
          ·
            refine ⟨1081300088630567270513045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720866725753711513675363 1081300088630567270513045)
            ·
              refine ⟨50685941654557840805299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1081300088630567270513045 50685941654557840805299)
              ·
                rfl

theorem cell19_499722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_499722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499722 prefixEnd_499722 := by exact prefixLift 499722
  have htrace : WordTrace (prefixWord ++ tailWord_499722) baseStart_499722 baseEnd_499722 := by
    simpa [prefixWord, tailWord_499722, baseEnd_499722] using wordTrace_append hprefix tailTrace_499722
  have hstable : (prefixWord ++ tailWord_499722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499722).length < 2 ^ (prefixWord ++ tailWord_499722).sum := by decide
  have hdescent : baseEnd_499722 < baseStart_499722 := by decide
  rcases family_descends (prefixWord ++ tailWord_499722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499724 : List Nat := [2, 2, 1, 2, 3, 1, 8]
def baseStart_499724 : Nat := 118140960795 + 499724 * 2 ^ 59
def prefixEnd_499724 : Nat := 4983230072969 + 3 ^ 40 * 499724 * 2
def baseEnd_499724 : Nat := 50686144511112703457149

theorem tailTrace_499724 : CollatzResearch.WordTrace tailWord_499724 prefixEnd_499724 50686144511112703457149 := by
  unfold tailWord_499724
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113215820796384454781113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12150954427728512606374817 9113215820796384454781113)
  ·
    refine ⟨6834911865597288341085835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9113215820796384454781113 6834911865597288341085835)
    ·
      refine ⟨10252367798395932511628753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6834911865597288341085835 10252367798395932511628753)
      ·
        refine ⟨7689275848796949383721565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10252367798395932511628753 7689275848796949383721565)
        ·
          refine ⟨2883478443298856018895587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7689275848796949383721565 2883478443298856018895587)
          ·
            refine ⟨4325217664948284028343381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883478443298856018895587 4325217664948284028343381)
            ·
              refine ⟨50686144511112703457149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4325217664948284028343381 50686144511112703457149)
              ·
                rfl

theorem cell19_499724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_499724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499724 prefixEnd_499724 := by exact prefixLift 499724
  have htrace : WordTrace (prefixWord ++ tailWord_499724) baseStart_499724 baseEnd_499724 := by
    simpa [prefixWord, tailWord_499724, baseEnd_499724] using wordTrace_append hprefix tailTrace_499724
  have hstable : (prefixWord ++ tailWord_499724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499724).length < 2 ^ (prefixWord ++ tailWord_499724).sum := by decide
  have hdescent : baseEnd_499724 < baseStart_499724 := by decide
  rcases family_descends (prefixWord ++ tailWord_499724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499743 : List Nat := [1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_499743 : Nat := 118140960795 + 499743 * 2 ^ 59
def prefixEnd_499743 : Nat := 4983230072969 + 3 ^ 40 * 499743 * 2
def baseEnd_499743 : Nat := 152064214945151695949173

theorem tailTrace_499743 : CollatzResearch.WordTrace tailWord_499743 prefixEnd_499743 152064214945151695949173 := by
  unfold tailWord_499743
  simp only [CollatzResearch.WordTrace]
  refine ⟨18227124628523935154503883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12151416419015956769669255 18227124628523935154503883)
  ·
    refine ⟨27340686942785902731755825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18227124628523935154503883 27340686942785902731755825)
    ·
      refine ⟨20505515207089427048816869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27340686942785902731755825 20505515207089427048816869)
      ·
        refine ⟨3844784101329267571653163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20505515207089427048816869 3844784101329267571653163)
        ·
          refine ⟨5767176151993901357479745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844784101329267571653163 5767176151993901357479745)
          ·
            refine ⟨4325382113995426018109809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5767176151993901357479745 4325382113995426018109809)
            ·
              refine ⟨3244036585496569513582357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4325382113995426018109809 3244036585496569513582357)
              ·
                refine ⟨152064214945151695949173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3244036585496569513582357 152064214945151695949173)
                ·
                  rfl

theorem cell19_499743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_499743 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499743 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499743 prefixEnd_499743 := by exact prefixLift 499743
  have htrace : WordTrace (prefixWord ++ tailWord_499743) baseStart_499743 baseEnd_499743 := by
    simpa [prefixWord, tailWord_499743, baseEnd_499743] using wordTrace_append hprefix tailTrace_499743
  have hstable : (prefixWord ++ tailWord_499743).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499743).length < 2 ^ (prefixWord ++ tailWord_499743).sum := by decide
  have hdescent : baseEnd_499743 < baseStart_499743 := by decide
  rcases family_descends (prefixWord ++ tailWord_499743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499758 : List Nat := [4, 1, 3, 1, 1, 2, 4, 3]
def baseStart_499758 : Nat := 118140960795 + 499758 * 2 ^ 59
def prefixEnd_499758 : Nat := 4983230072969 + 3 ^ 40 * 499758 * 2
def baseEnd_499758 : Nat := 152068779217636105615799

theorem tailTrace_499758 : CollatzResearch.WordTrace tailWord_499758 prefixEnd_499758 152068779217636105615799 := by
  unfold tailWord_499758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278458965433699089537491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12151781148979728477533285 2278458965433699089537491)
  ·
    refine ⟨3417688448150548634306237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2278458965433699089537491 3417688448150548634306237)
    ·
      refine ⟨1281633168056455737864839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3417688448150548634306237 1281633168056455737864839)
      ·
        refine ⟨1922449752084683606797259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281633168056455737864839 1922449752084683606797259)
        ·
          refine ⟨2883674628127025410195889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922449752084683606797259 2883674628127025410195889)
          ·
            refine ⟨2162755971095269057646917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2883674628127025410195889 2162755971095269057646917)
            ·
              refine ⟨405516744580362948308797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2162755971095269057646917 405516744580362948308797)
              ·
                refine ⟨152068779217636105615799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405516744580362948308797 152068779217636105615799)
                ·
                  rfl

theorem cell19_499758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_499758 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499758 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499758 prefixEnd_499758 := by exact prefixLift 499758
  have htrace : WordTrace (prefixWord ++ tailWord_499758) baseStart_499758 baseEnd_499758 := by
    simpa [prefixWord, tailWord_499758, baseEnd_499758] using wordTrace_append hprefix tailTrace_499758
  have hstable : (prefixWord ++ tailWord_499758).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499758).length < 2 ^ (prefixWord ++ tailWord_499758).sum := by decide
  have hdescent : baseEnd_499758 < baseStart_499758 := by decide
  rcases family_descends (prefixWord ++ tailWord_499758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499760 : List Nat := [2, 1, 1, 1, 2, 5, 4, 3]
def baseStart_499760 : Nat := 118140960795 + 499760 * 2 ^ 59
def prefixEnd_499760 : Nat := 4983230072969 + 3 ^ 40 * 499760 * 2
def baseEnd_499760 : Nat := 152069387787300693571349

theorem tailTrace_499760 : CollatzResearch.WordTrace tailWord_499760 prefixEnd_499760 152069387787300693571349 := by
  unfold tailWord_499760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113872334731173528936367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12151829779641564705248489 9113872334731173528936367)
  ·
    refine ⟨13670808502096760293404551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9113872334731173528936367 13670808502096760293404551)
    ·
      refine ⟨20506212753145140440106827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13670808502096760293404551 20506212753145140440106827)
      ·
        refine ⟨30759319129717710660160241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20506212753145140440106827 30759319129717710660160241)
        ·
          refine ⟨23069489347288282995120181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30759319129717710660160241 23069489347288282995120181)
          ·
            refine ⟨2162764626308276530792517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23069489347288282995120181 2162764626308276530792517)
            ·
              refine ⟨405518367432801849523597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2162764626308276530792517 405518367432801849523597)
              ·
                refine ⟨152069387787300693571349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405518367432801849523597 152069387787300693571349)
                ·
                  rfl

theorem cell19_499760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_499760 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499760 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499760 prefixEnd_499760 := by exact prefixLift 499760
  have htrace : WordTrace (prefixWord ++ tailWord_499760) baseStart_499760 baseEnd_499760 := by
    simpa [prefixWord, tailWord_499760, baseEnd_499760] using wordTrace_append hprefix tailTrace_499760
  have hstable : (prefixWord ++ tailWord_499760).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499760).length < 2 ^ (prefixWord ++ tailWord_499760).sum := by decide
  have hdescent : baseEnd_499760 < baseStart_499760 := by decide
  rcases family_descends (prefixWord ++ tailWord_499760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499800 : List Nat := [2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_499800 : Nat := 118140960795 + 499800 * 2 ^ 59
def prefixEnd_499800 : Nat := 4983230072969 + 3 ^ 40 * 499800 * 2
def baseEnd_499800 : Nat := 152081559180592452682351

theorem tailTrace_499800 : CollatzResearch.WordTrace tailWord_499800 prefixEnd_499800 152081559180592452682351 := by
  unfold tailWord_499800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9114601794658716944664427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12152802392878289259552569 9114601794658716944664427)
  ·
    refine ⟨13671902691988075416996641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9114601794658716944664427 13671902691988075416996641)
    ·
      refine ⟨10253927018991056562747481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13671902691988075416996641 10253927018991056562747481)
      ·
        refine ⟨7690445264243292422060611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10253927018991056562747481 7690445264243292422060611)
        ·
          refine ⟨11535667896364938633090917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690445264243292422060611 11535667896364938633090917)
          ·
            refine ⟨2162937730568425993704547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11535667896364938633090917 2162937730568425993704547)
            ·
              refine ⟨3244406595852638990556821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162937730568425993704547 3244406595852638990556821)
              ·
                refine ⟨152081559180592452682351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3244406595852638990556821 152081559180592452682351)
                ·
                  rfl

theorem cell19_499800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_499800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499800 prefixEnd_499800 := by exact prefixLift 499800
  have htrace : WordTrace (prefixWord ++ tailWord_499800) baseStart_499800 baseEnd_499800 := by
    simpa [prefixWord, tailWord_499800, baseEnd_499800] using wordTrace_append hprefix tailTrace_499800
  have hstable : (prefixWord ++ tailWord_499800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499800).length < 2 ^ (prefixWord ++ tailWord_499800).sum := by decide
  have hdescent : baseEnd_499800 < baseStart_499800 := by decide
  rcases family_descends (prefixWord ++ tailWord_499800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499870 : List Nat := [4, 3, 1, 1, 3, 1, 3, 3]
def baseStart_499870 : Nat := 118140960795 + 499870 * 2 ^ 59
def prefixEnd_499870 : Nat := 4983230072969 + 3 ^ 40 * 499870 * 2
def baseEnd_499870 : Nat := 152102859118853031126605

theorem tailTrace_499870 : CollatzResearch.WordTrace tailWord_499870 prefixEnd_499870 152102859118853031126605 := by
  unfold tailWord_499870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278969587382979480547133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12154504466042557229584709 2278969587382979480547133)
  ·
    refine ⟨854613595268617305205175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2278969587382979480547133 854613595268617305205175)
    ·
      refine ⟨1281920392902925957807763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854613595268617305205175 1281920392902925957807763)
      ·
        refine ⟨1922880589354388936711645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281920392902925957807763 1922880589354388936711645)
        ·
          refine ⟨721080221007895851266867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1922880589354388936711645 721080221007895851266867)
          ·
            refine ⟨1081620331511843776900301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721080221007895851266867 1081620331511843776900301)
            ·
              refine ⟨405607624316941416337613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1081620331511843776900301 405607624316941416337613)
              ·
                refine ⟨152102859118853031126605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405607624316941416337613 152102859118853031126605)
                ·
                  rfl

theorem cell19_499870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_499870 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499870 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499870 prefixEnd_499870 := by exact prefixLift 499870
  have htrace : WordTrace (prefixWord ++ tailWord_499870) baseStart_499870 baseEnd_499870 := by
    simpa [prefixWord, tailWord_499870, baseEnd_499870] using wordTrace_append hprefix tailTrace_499870
  have hstable : (prefixWord ++ tailWord_499870).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499870).length < 2 ^ (prefixWord ++ tailWord_499870).sum := by decide
  have hdescent : baseEnd_499870 < baseStart_499870 := by decide
  rcases family_descends (prefixWord ++ tailWord_499870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499895 : List Nat := [1, 1, 3, 1, 4, 3, 6]
def baseStart_499895 : Nat := 118140960795 + 499895 * 2 ^ 59
def prefixEnd_499895 : Nat := 4983230072969 + 3 ^ 40 * 499895 * 2
def baseEnd_499895 : Nat := 50703488746553460190327

theorem tailTrace_499895 : CollatzResearch.WordTrace tailWord_499895 prefixEnd_499895 50703488746553460190327 := by
  unfold tailWord_499895
  simp only [CollatzResearch.WordTrace]
  refine ⟨18232668523973265114037139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12155112349315510076024759 18232668523973265114037139)
  ·
    refine ⟨27349002785959897671055709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18232668523973265114037139 27349002785959897671055709)
    ·
      refine ⟨10255876044734961626645891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27349002785959897671055709 10255876044734961626645891)
      ·
        refine ⟨15383814067102442439968837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10255876044734961626645891 15383814067102442439968837)
        ·
          refine ⟨2884465137581707957494157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15383814067102442439968837 2884465137581707957494157)
          ·
            refine ⟨1081674426593140484060309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2884465137581707957494157 1081674426593140484060309)
            ·
              refine ⟨50703488746553460190327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1081674426593140484060309 50703488746553460190327)
              ·
                rfl

theorem cell19_499895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_499895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499895 prefixEnd_499895 := by exact prefixLift 499895
  have htrace : WordTrace (prefixWord ++ tailWord_499895) baseStart_499895 baseEnd_499895 := by
    simpa [prefixWord, tailWord_499895, baseEnd_499895] using wordTrace_append hprefix tailTrace_499895
  have hstable : (prefixWord ++ tailWord_499895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499895).length < 2 ^ (prefixWord ++ tailWord_499895).sum := by decide
  have hdescent : baseEnd_499895 < baseStart_499895 := by decide
  rcases family_descends (prefixWord ++ tailWord_499895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499914 : List Nat := [3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_499914 : Nat := 118140960795 + 499914 * 2 ^ 59
def prefixEnd_499914 : Nat := 4983230072969 + 3 ^ 40 * 499914 * 2
def baseEnd_499914 : Nat := 152116247651473966148707

theorem tailTrace_499914 : CollatzResearch.WordTrace tailWord_499914 prefixEnd_499914 152116247651473966148707 := by
  unfold tailWord_499914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4558340377726107839744699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12155574340602954239319197 4558340377726107839744699)
  ·
    refine ⟨6837510566589161759617049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4558340377726107839744699 6837510566589161759617049)
    ·
      refine ⟨5128132924941871319712787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6837510566589161759617049 5128132924941871319712787)
      ·
        refine ⟨7692199387412806979569181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5128132924941871319712787 7692199387412806979569181)
        ·
          refine ⟨2884574770279802617338443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7692199387412806979569181 2884574770279802617338443)
          ·
            refine ⟨4326862155419703926007665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884574770279802617338443 4326862155419703926007665)
            ·
              refine ⟨3245146616564777944505749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4326862155419703926007665 3245146616564777944505749)
              ·
                refine ⟨152116247651473966148707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3245146616564777944505749 152116247651473966148707)
                ·
                  rfl

theorem cell19_499914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_499914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499914 prefixEnd_499914 := by exact prefixLift 499914
  have htrace : WordTrace (prefixWord ++ tailWord_499914) baseStart_499914 baseEnd_499914 := by
    simpa [prefixWord, tailWord_499914, baseEnd_499914] using wordTrace_append hprefix tailTrace_499914
  have hstable : (prefixWord ++ tailWord_499914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499914).length < 2 ^ (prefixWord ++ tailWord_499914).sum := by decide
  have hdescent : baseEnd_499914 < baseStart_499914 := by decide
  rcases family_descends (prefixWord ++ tailWord_499914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499971 : List Nat := [1, 1, 1, 3, 2, 3, 4, 4]
def baseStart_499971 : Nat := 118140960795 + 499971 * 2 ^ 59
def prefixEnd_499971 : Nat := 4983230072969 + 3 ^ 40 * 499971 * 2
def baseEnd_499971 : Nat := 152133591886914722881885

theorem tailTrace_499971 : CollatzResearch.WordTrace tailWord_499971 prefixEnd_499971 152133591886914722881885 := by
  unfold tailWord_499971
  simp only [CollatzResearch.WordTrace]
  refine ⟨18235440471697930093803767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12156960314465286729202511 18235440471697930093803767)
  ·
    refine ⟨27353160707546895140705651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18235440471697930093803767 27353160707546895140705651)
    ·
      refine ⟨41029741061320342711058477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27353160707546895140705651 41029741061320342711058477)
      ·
        refine ⟨15386152897995128516646929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41029741061320342711058477 15386152897995128516646929)
        ·
          refine ⟨11539614673496346387485197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15386152897995128516646929 11539614673496346387485197)
          ·
            refine ⟨4327355502561129895306949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11539614673496346387485197 4327355502561129895306949)
            ·
              refine ⟨811379156730211855370053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4327355502561129895306949 811379156730211855370053)
              ·
                refine ⟨152133591886914722881885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 811379156730211855370053 152133591886914722881885)
                ·
                  rfl

theorem cell19_499971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_499971 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_499971 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_499971 prefixEnd_499971 := by exact prefixLift 499971
  have htrace : WordTrace (prefixWord ++ tailWord_499971) baseStart_499971 baseEnd_499971 := by
    simpa [prefixWord, tailWord_499971, baseEnd_499971] using wordTrace_append hprefix tailTrace_499971
  have hstable : (prefixWord ++ tailWord_499971).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499971).length < 2 ^ (prefixWord ++ tailWord_499971).sum := by decide
  have hdescent : baseEnd_499971 < baseStart_499971 := by decide
  rcases family_descends (prefixWord ++ tailWord_499971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500026 : List Nat := [3, 1, 1, 1, 4, 4, 1, 4]
def baseStart_500026 : Nat := 118140960795 + 500026 * 2 ^ 59
def prefixEnd_500026 : Nat := 4983230072969 + 3 ^ 40 * 500026 * 2
def baseEnd_500026 : Nat := 152150327552690891659513

theorem tailTrace_500026 : CollatzResearch.WordTrace tailWord_500026 prefixEnd_500026 152150327552690891659513 := by
  unfold tailWord_500026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559361621624668621763983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12158297657665782991370621 4559361621624668621763983)
  ·
    refine ⟨6839042432437002932645975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4559361621624668621763983 6839042432437002932645975)
    ·
      refine ⟨10258563648655504398968963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6839042432437002932645975 10258563648655504398968963)
      ·
        refine ⟨15387845472983256598453445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10258563648655504398968963 15387845472983256598453445)
        ·
          refine ⟨2885221026184360612210021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15387845472983256598453445 2885221026184360612210021)
          ·
            refine ⟨540978942409567614789379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2885221026184360612210021 540978942409567614789379)
            ·
              refine ⟨811468413614351422184069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540978942409567614789379 811468413614351422184069)
              ·
                refine ⟨152150327552690891659513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 811468413614351422184069 152150327552690891659513)
                ·
                  rfl

theorem cell19_500026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_500026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500026 prefixEnd_500026 := by exact prefixLift 500026
  have htrace : WordTrace (prefixWord ++ tailWord_500026) baseStart_500026 baseEnd_500026 := by
    simpa [prefixWord, tailWord_500026, baseEnd_500026] using wordTrace_append hprefix tailTrace_500026
  have hstable : (prefixWord ++ tailWord_500026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500026).length < 2 ^ (prefixWord ++ tailWord_500026).sum := by decide
  have hdescent : baseEnd_500026 < baseStart_500026 := by decide
  rcases family_descends (prefixWord ++ tailWord_500026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500104 : List Nat := [2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_500104 : Nat := 118140960795 + 500104 * 2 ^ 59
def prefixEnd_500104 : Nat := 4983230072969 + 3 ^ 40 * 500104 * 2
def baseEnd_500104 : Nat := 152174061769609821925967

theorem tailTrace_500104 : CollatzResearch.WordTrace tailWord_500104 prefixEnd_500104 152174061769609821925967 := by
  unfold tailWord_500104
  simp only [CollatzResearch.WordTrace]
  refine ⟨9120145690108046904197683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12160194253477395872263577 9120145690108046904197683)
  ·
    refine ⟨13680218535162070356296525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9120145690108046904197683 13680218535162070356296525)
    ·
      refine ⟨5130081950685776383611197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13680218535162070356296525 5130081950685776383611197)
      ·
        refine ⟨1923780731507166143854199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5130081950685776383611197 1923780731507166143854199)
        ·
          refine ⟨2885671097260749215781299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923780731507166143854199 2885671097260749215781299)
          ·
            refine ⟨4328506645891123823671949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885671097260749215781299 4328506645891123823671949)
            ·
              refine ⟨1623189992209171433876981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4328506645891123823671949 1623189992209171433876981)
              ·
                refine ⟨152174061769609821925967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1623189992209171433876981 152174061769609821925967)
                ·
                  rfl

theorem cell19_500104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_500104 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500104 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500104 prefixEnd_500104 := by exact prefixLift 500104
  have htrace : WordTrace (prefixWord ++ tailWord_500104) baseStart_500104 baseEnd_500104 := by
    simpa [prefixWord, tailWord_500104, baseEnd_500104] using wordTrace_append hprefix tailTrace_500104
  have hstable : (prefixWord ++ tailWord_500104).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500104).length < 2 ^ (prefixWord ++ tailWord_500104).sum := by decide
  have hdescent : baseEnd_500104 < baseStart_500104 := by decide
  rcases family_descends (prefixWord ++ tailWord_500104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500178 : List Nat := [3, 2, 2, 4, 1, 7]
def baseStart_500178 : Nat := 118140960795 + 500178 * 2 ^ 59
def prefixEnd_500178 : Nat := 4983230072969 + 3 ^ 40 * 500178 * 2
def baseEnd_500178 : Nat := 16910730983022175142369

theorem tailTrace_500178 : CollatzResearch.WordTrace tailWord_500178 prefixEnd_500178 16910730983022175142369 := by
  unfold tailWord_500178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4560747595487001111647297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12161993587965336297726125 4560747595487001111647297)
  ·
    refine ⟨3420560696615250833735473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4560747595487001111647297 3420560696615250833735473)
    ·
      refine ⟨2565420522461438125301605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3420560696615250833735473 2565420522461438125301605)
      ·
        refine ⟨481016347961519648494051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2565420522461438125301605 481016347961519648494051)
        ·
          refine ⟨721524521942279472741077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481016347961519648494051 721524521942279472741077)
          ·
            refine ⟨16910730983022175142369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 721524521942279472741077 16910730983022175142369)
            ·
              rfl

theorem cell19_500178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 7].length) (baseStart_500178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500178 prefixEnd_500178 := by exact prefixLift 500178
  have htrace : WordTrace (prefixWord ++ tailWord_500178) baseStart_500178 baseEnd_500178 := by
    simpa [prefixWord, tailWord_500178, baseEnd_500178] using wordTrace_append hprefix tailTrace_500178
  have hstable : (prefixWord ++ tailWord_500178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500178).length < 2 ^ (prefixWord ++ tailWord_500178).sum := by decide
  have hdescent : baseEnd_500178 < baseStart_500178 := by decide
  rcases family_descends (prefixWord ++ tailWord_500178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500180 : List Nat := [2, 4, 1, 2, 2, 8]
def baseStart_500180 : Nat := 118140960795 + 500180 * 2 ^ 59
def prefixEnd_500180 : Nat := 4983230072969 + 3 ^ 40 * 500180 * 2
def baseEnd_500180 : Nat := 16910798601873796026319

theorem tailTrace_500180 : CollatzResearch.WordTrace tailWord_500180 prefixEnd_500180 16910798601873796026319 := by
  unfold tailWord_500180
  simp only [CollatzResearch.WordTrace]
  refine ⟨9121531663970379394080997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12162042218627172525441329 9121531663970379394080997)
  ·
    refine ⟨1710287186994446136390187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9121531663970379394080997 1710287186994446136390187)
    ·
      refine ⟨2565430780491669204585281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710287186994446136390187 2565430780491669204585281)
      ·
        refine ⟨1924073085368751903438961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2565430780491669204585281 1924073085368751903438961)
        ·
          refine ⟨1443054814026563927579221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1924073085368751903438961 1443054814026563927579221)
          ·
            refine ⟨16910798601873796026319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1443054814026563927579221 16910798601873796026319)
            ·
              rfl

theorem cell19_500180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 8].length) (baseStart_500180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500180 prefixEnd_500180 := by exact prefixLift 500180
  have htrace : WordTrace (prefixWord ++ tailWord_500180) baseStart_500180 baseEnd_500180 := by
    simpa [prefixWord, tailWord_500180, baseEnd_500180] using wordTrace_append hprefix tailTrace_500180
  have hstable : (prefixWord ++ tailWord_500180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500180).length < 2 ^ (prefixWord ++ tailWord_500180).sum := by decide
  have hdescent : baseEnd_500180 < baseStart_500180 := by decide
  rcases family_descends (prefixWord ++ tailWord_500180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500195 : List Nat := [1, 1, 1, 6, 4, 1, 1, 4]
def baseStart_500195 : Nat := 118140960795 + 500195 * 2 ^ 59
def prefixEnd_500195 : Nat := 4983230072969 + 3 ^ 40 * 500195 * 2
def baseEnd_500195 : Nat := 152201751689348573903497

theorem tailTrace_500195 : CollatzResearch.WordTrace tailWord_500195 prefixEnd_500195 152201751689348573903497 := by
  unfold tailWord_500195
  simp only [CollatzResearch.WordTrace]
  refine ⟨18243610422886416349958039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12162406948590944233305359 18243610422886416349958039)
  ·
    refine ⟨27365415634329624524937059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18243610422886416349958039 27365415634329624524937059)
    ·
      refine ⟨41048123451494436787405589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27365415634329624524937059 41048123451494436787405589)
      ·
        refine ⟨1924130786788801724409637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41048123451494436787405589 1924130786788801724409637)
        ·
          refine ⟨360774522522900323326807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1924130786788801724409637 360774522522900323326807)
          ·
            refine ⟨541161783784350484990211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360774522522900323326807 541161783784350484990211)
            ·
              refine ⟨811742675676525727485317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541161783784350484990211 811742675676525727485317)
              ·
                refine ⟨152201751689348573903497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 811742675676525727485317 152201751689348573903497)
                ·
                  rfl

theorem cell19_500195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 4].length) (baseStart_500195 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500195 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500195 prefixEnd_500195 := by exact prefixLift 500195
  have htrace : WordTrace (prefixWord ++ tailWord_500195) baseStart_500195 baseEnd_500195 := by
    simpa [prefixWord, tailWord_500195, baseEnd_500195] using wordTrace_append hprefix tailTrace_500195
  have hstable : (prefixWord ++ tailWord_500195).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500195).length < 2 ^ (prefixWord ++ tailWord_500195).sum := by decide
  have hdescent : baseEnd_500195 < baseStart_500195 := by decide
  rcases family_descends (prefixWord ++ tailWord_500195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500201 : List Nat := [1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_500201 : Nat := 118140960795 + 500201 * 2 ^ 59
def prefixEnd_500201 : Nat := 4983230072969 + 3 ^ 40 * 500201 * 2
def baseEnd_500201 : Nat := 152203577398342337770147

theorem tailTrace_500201 : CollatzResearch.WordTrace tailWord_500201 prefixEnd_500201 152203577398342337770147 := by
  unfold tailWord_500201
  simp only [CollatzResearch.WordTrace]
  refine ⟨18243829260864679374676457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12162552840576452916450971 18243829260864679374676457)
  ·
    refine ⟨13682871945648509531007343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18243829260864679374676457 13682871945648509531007343)
    ·
      refine ⟨20524307918472764296511015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13682871945648509531007343 20524307918472764296511015)
      ·
        refine ⟨30786461877709146444766523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20524307918472764296511015 30786461877709146444766523)
        ·
          refine ⟨46179692816563719667149785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30786461877709146444766523 46179692816563719667149785)
          ·
            refine ⟨34634769612422789750362339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46179692816563719667149785 34634769612422789750362339)
            ·
              refine ⟨51952154418634184625543509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34634769612422789750362339 51952154418634184625543509)
              ·
                refine ⟨152203577398342337770147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51952154418634184625543509 152203577398342337770147)
                ·
                  rfl

theorem cell19_500201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_500201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500201 prefixEnd_500201 := by exact prefixLift 500201
  have htrace : WordTrace (prefixWord ++ tailWord_500201) baseStart_500201 baseEnd_500201 := by
    simpa [prefixWord, tailWord_500201, baseEnd_500201] using wordTrace_append hprefix tailTrace_500201
  have hstable : (prefixWord ++ tailWord_500201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500201).length < 2 ^ (prefixWord ++ tailWord_500201).sum := by decide
  have hdescent : baseEnd_500201 < baseStart_500201 := by decide
  rcases family_descends (prefixWord ++ tailWord_500201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500269 : List Nat := [1, 5, 4, 1, 1, 1, 1, 5]
def baseStart_500269 : Nat := 118140960795 + 500269 * 2 ^ 59
def prefixEnd_500269 : Nat := 4983230072969 + 3 ^ 40 * 500269 * 2
def baseEnd_500269 : Nat := 152224268766938328258851

theorem tailTrace_500269 : CollatzResearch.WordTrace tailWord_500269 prefixEnd_500269 152224268766938328258851 := by
  unfold tailWord_500269
  simp only [CollatzResearch.WordTrace]
  refine ⟨18246309424618326988151861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12164206283078884658767907 18246309424618326988151861)
  ·
    refine ⟨1710591508557968155139237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18246309424618326988151861 1710591508557968155139237)
    ·
      refine ⟨320735907854619029088607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1710591508557968155139237 320735907854619029088607)
      ·
        refine ⟨481103861781928543632911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320735907854619029088607 481103861781928543632911)
        ·
          refine ⟨721655792672892815449367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481103861781928543632911 721655792672892815449367)
          ·
            refine ⟨1082483689009339223174051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721655792672892815449367 1082483689009339223174051)
            ·
              refine ⟨1623725533514008834761077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082483689009339223174051 1623725533514008834761077)
              ·
                refine ⟨152224268766938328258851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1623725533514008834761077 152224268766938328258851)
                ·
                  rfl

theorem cell19_500269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 5].length) (baseStart_500269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500269 prefixEnd_500269 := by exact prefixLift 500269
  have htrace : WordTrace (prefixWord ++ tailWord_500269) baseStart_500269 baseEnd_500269 := by
    simpa [prefixWord, tailWord_500269, baseEnd_500269] using wordTrace_append hprefix tailTrace_500269
  have hstable : (prefixWord ++ tailWord_500269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500269).length < 2 ^ (prefixWord ++ tailWord_500269).sum := by decide
  have hdescent : baseEnd_500269 < baseStart_500269 := by decide
  rcases family_descends (prefixWord ++ tailWord_500269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500410 : List Nat := [3, 1, 1, 1, 2, 3, 8]
def baseStart_500410 : Nat := 118140960795 + 500410 * 2 ^ 59
def prefixEnd_500410 : Nat := 4983230072969 + 3 ^ 40 * 500410 * 2
def baseEnd_500410 : Nat := 50755724309430593041711

theorem tailTrace_500410 : CollatzResearch.WordTrace tailWord_500410 prefixEnd_500410 50755724309430593041711 := by
  unfold tailWord_500410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562863029276877017258671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12167634744738338712689789 4562863029276877017258671)
  ·
    refine ⟨6844294543915315525888007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4562863029276877017258671 6844294543915315525888007)
    ·
      refine ⟨10266441815872973288832011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6844294543915315525888007 10266441815872973288832011)
      ·
        refine ⟨15399662723809459933248017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10266441815872973288832011 15399662723809459933248017)
        ·
          refine ⟨11549747042857094949936013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15399662723809459933248017 11549747042857094949936013)
          ·
            refine ⟨4331155141071410606226005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11549747042857094949936013 4331155141071410606226005)
            ·
              refine ⟨50755724309430593041711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4331155141071410606226005 50755724309430593041711)
              ·
                rfl

theorem cell19_500410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_500410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500410 prefixEnd_500410 := by exact prefixLift 500410
  have htrace : WordTrace (prefixWord ++ tailWord_500410) baseStart_500410 baseEnd_500410 := by
    simpa [prefixWord, tailWord_500410, baseEnd_500410] using wordTrace_append hprefix tailTrace_500410
  have hstable : (prefixWord ++ tailWord_500410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500410).length < 2 ^ (prefixWord ++ tailWord_500410).sum := by decide
  have hdescent : baseEnd_500410 < baseStart_500410 := by decide
  rcases family_descends (prefixWord ++ tailWord_500410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500444 : List Nat := [2, 2, 5, 1, 1, 2, 1, 5]
def baseStart_500444 : Nat := 118140960795 + 500444 * 2 ^ 59
def prefixEnd_500444 : Nat := 4983230072969 + 3 ^ 40 * 500444 * 2
def baseEnd_500444 : Nat := 152277518612589774369485

theorem tailTrace_500444 : CollatzResearch.WordTrace tailWord_500444 prefixEnd_500444 152277518612589774369485 := by
  unfold tailWord_500444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9126346099492165937886193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12168461465989554583848257 9126346099492165937886193)
  ·
    refine ⟨6844759574619124453414645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9126346099492165937886193 6844759574619124453414645)
    ·
      refine ⟨641696210120542917507623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6844759574619124453414645 641696210120542917507623)
      ·
        refine ⟨962544315180814376261435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641696210120542917507623 962544315180814376261435)
        ·
          refine ⟨1443816472771221564392153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962544315180814376261435 1443816472771221564392153)
          ·
            refine ⟨1082862354578416173294115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1443816472771221564392153 1082862354578416173294115)
            ·
              refine ⟨1624293531867624259941173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082862354578416173294115 1624293531867624259941173)
              ·
                refine ⟨152277518612589774369485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1624293531867624259941173 152277518612589774369485)
                ·
                  rfl

theorem cell19_500444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_500444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500444 prefixEnd_500444 := by exact prefixLift 500444
  have htrace : WordTrace (prefixWord ++ tailWord_500444) baseStart_500444 baseEnd_500444 := by
    simpa [prefixWord, tailWord_500444, baseEnd_500444] using wordTrace_append hprefix tailTrace_500444
  have hstable : (prefixWord ++ tailWord_500444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500444).length < 2 ^ (prefixWord ++ tailWord_500444).sum := by decide
  have hdescent : baseEnd_500444 < baseStart_500444 := by decide
  rcases family_descends (prefixWord ++ tailWord_500444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500482 : List Nat := [3, 4, 1, 1, 1, 3, 2, 4]
def baseStart_500482 : Nat := 118140960795 + 500482 * 2 ^ 59
def prefixEnd_500482 : Nat := 4983230072969 + 3 ^ 40 * 500482 * 2
def baseEnd_500482 : Nat := 152289081436216945524937

theorem tailTrace_500482 : CollatzResearch.WordTrace tailWord_500482 prefixEnd_500482 152289081436216945524937 := by
  unfold tailWord_500482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4563519543211666091413925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12169385448564442910437133 4563519543211666091413925)
  ·
    refine ⟨855659914352187392140111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4563519543211666091413925 855659914352187392140111)
    ·
      refine ⟨1283489871528281088210167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855659914352187392140111 1283489871528281088210167)
      ·
        refine ⟨1925234807292421632315251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283489871528281088210167 1925234807292421632315251)
        ·
          refine ⟨2887852210938632448472877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925234807292421632315251 2887852210938632448472877)
          ·
            refine ⟨1082944579101987168177329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2887852210938632448472877 1082944579101987168177329)
            ·
              refine ⟨812208434326490376132997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082944579101987168177329 812208434326490376132997)
              ·
                refine ⟨152289081436216945524937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 812208434326490376132997 152289081436216945524937)
                ·
                  rfl

theorem cell19_500482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_500482 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500482 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500482 prefixEnd_500482 := by exact prefixLift 500482
  have htrace : WordTrace (prefixWord ++ tailWord_500482) baseStart_500482 baseEnd_500482 := by
    simpa [prefixWord, tailWord_500482, baseEnd_500482] using wordTrace_append hprefix tailTrace_500482
  have hstable : (prefixWord ++ tailWord_500482).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500482).length < 2 ^ (prefixWord ++ tailWord_500482).sum := by decide
  have hdescent : baseEnd_500482 < baseStart_500482 := by decide
  rcases family_descends (prefixWord ++ tailWord_500482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500484 : List Nat := [2, 3, 2, 2, 1, 1, 4, 4]
def baseStart_500484 : Nat := 118140960795 + 500484 * 2 ^ 59
def prefixEnd_500484 : Nat := 4983230072969 + 3 ^ 40 * 500484 * 2
def baseEnd_500484 : Nat := 152289690005881533480487

theorem tailTrace_500484 : CollatzResearch.WordTrace tailWord_500484 prefixEnd_500484 152289690005881533480487 := by
  unfold tailWord_500484
  simp only [CollatzResearch.WordTrace]
  refine ⟨9127075559419709353614253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12169434079226279138152337 9127075559419709353614253)
  ·
    refine ⟨3422653334782391007605345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9127075559419709353614253 3422653334782391007605345)
    ·
      refine ⟨2566990001086793255704009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3422653334782391007605345 2566990001086793255704009)
      ·
        refine ⟨1925242500815094941778007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2566990001086793255704009 1925242500815094941778007)
        ·
          refine ⟨2887863751222642412667011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925242500815094941778007 2887863751222642412667011)
          ·
            refine ⟨4331795626833963619000517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887863751222642412667011 4331795626833963619000517)
            ·
              refine ⟨812211680031368178562597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4331795626833963619000517 812211680031368178562597)
              ·
                refine ⟨152289690005881533480487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 812211680031368178562597 152289690005881533480487)
                ·
                  rfl

theorem cell19_500484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_500484 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500484 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500484 prefixEnd_500484 := by exact prefixLift 500484
  have htrace : WordTrace (prefixWord ++ tailWord_500484) baseStart_500484 baseEnd_500484 := by
    simpa [prefixWord, tailWord_500484, baseEnd_500484] using wordTrace_append hprefix tailTrace_500484
  have hstable : (prefixWord ++ tailWord_500484).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500484).length < 2 ^ (prefixWord ++ tailWord_500484).sum := by decide
  have hdescent : baseEnd_500484 < baseStart_500484 := by decide
  rcases family_descends (prefixWord ++ tailWord_500484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500522 : List Nat := [3, 1, 4, 3, 8]
def baseStart_500522 : Nat := 118140960795 + 500522 * 2 ^ 59
def prefixEnd_500522 : Nat := 4983230072969 + 3 ^ 40 * 500522 * 2
def baseEnd_500522 : Nat := 5640787141833655727257

theorem tailTrace_500522 : CollatzResearch.WordTrace tailWord_500522 prefixEnd_500522 5640787141833655727257 := by
  unfold tailWord_500522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4563884273175437799277955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12170358061801167464741213 4563884273175437799277955)
  ·
    refine ⟨6845826409763156698916933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4563884273175437799277955 6845826409763156698916933)
    ·
      refine ⟨1283592451830591881046925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6845826409763156698916933 1283592451830591881046925)
      ·
        refine ⟨481347169436471955392597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1283592451830591881046925 481347169436471955392597)
        ·
          refine ⟨5640787141833655727257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 481347169436471955392597 5640787141833655727257)
          ·
            rfl

theorem cell19_500522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 8].length) (baseStart_500522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500522 prefixEnd_500522 := by exact prefixLift 500522
  have htrace : WordTrace (prefixWord ++ tailWord_500522) baseStart_500522 baseEnd_500522 := by
    simpa [prefixWord, tailWord_500522, baseEnd_500522] using wordTrace_append hprefix tailTrace_500522
  have hstable : (prefixWord ++ tailWord_500522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500522).length < 2 ^ (prefixWord ++ tailWord_500522).sum := by decide
  have hdescent : baseEnd_500522 < baseStart_500522 := by decide
  rcases family_descends (prefixWord ++ tailWord_500522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500615 : List Nat := [1, 1, 4, 2, 3, 3, 2, 3]
def baseStart_500615 : Nat := 118140960795 + 500615 * 2 ^ 59
def prefixEnd_500615 : Nat := 4983230072969 + 3 ^ 40 * 500615 * 2
def baseEnd_500615 : Nat := 152329551318912044569019

theorem tailTrace_500615 : CollatzResearch.WordTrace tailWord_500615 prefixEnd_500615 152329551318912044569019 := by
  unfold tailWord_500615
  simp only [CollatzResearch.WordTrace]
  refine ⟨18258929081364828080247299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12172619387576552053498199 18258929081364828080247299)
  ·
    refine ⟨27388393622047242120370949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18258929081364828080247299 27388393622047242120370949)
    ·
      refine ⟨5135323804133857897569553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27388393622047242120370949 5135323804133857897569553)
      ·
        refine ⟨3851492853100393423177165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5135323804133857897569553 3851492853100393423177165)
        ·
          refine ⟨1444309819912647533691437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3851492853100393423177165 1444309819912647533691437)
          ·
            refine ⟨541616182467242825134289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1444309819912647533691437 541616182467242825134289)
            ·
              refine ⟨406212136850432118850717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541616182467242825134289 406212136850432118850717)
              ·
                refine ⟨152329551318912044569019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406212136850432118850717 152329551318912044569019)
                ·
                  rfl

theorem cell19_500615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 3].length) (baseStart_500615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500615 prefixEnd_500615 := by exact prefixLift 500615
  have htrace : WordTrace (prefixWord ++ tailWord_500615) baseStart_500615 baseEnd_500615 := by
    simpa [prefixWord, tailWord_500615, baseEnd_500615] using wordTrace_append hprefix tailTrace_500615
  have hstable : (prefixWord ++ tailWord_500615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500615).length < 2 ^ (prefixWord ++ tailWord_500615).sum := by decide
  have hdescent : baseEnd_500615 < baseStart_500615 := by decide
  rcases family_descends (prefixWord ++ tailWord_500615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500617 : List Nat := [1, 2, 1, 1, 5, 2, 4, 3]
def baseStart_500617 : Nat := 118140960795 + 500617 * 2 ^ 59
def prefixEnd_500617 : Nat := 4983230072969 + 3 ^ 40 * 500617 * 2
def baseEnd_500617 : Nat := 152330159888576632524569

theorem tailTrace_500617 : CollatzResearch.WordTrace tailWord_500617 prefixEnd_500617 152330159888576632524569 := by
  unfold tailWord_500617
  simp only [CollatzResearch.WordTrace]
  refine ⟨18259002027357582421820105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12172668018238388281213403 18259002027357582421820105)
  ·
    refine ⟨13694251520518186816365079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18259002027357582421820105 13694251520518186816365079)
    ·
      refine ⟨20541377280777280224547619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13694251520518186816365079 20541377280777280224547619)
      ·
        refine ⟨30812065921165920336821429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20541377280777280224547619 30812065921165920336821429)
        ·
          refine ⟨2888631180109305031577009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30812065921165920336821429 2888631180109305031577009)
          ·
            refine ⟨2166473385081978773682757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2888631180109305031577009 2166473385081978773682757)
            ·
              refine ⟨406213759702871020065517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2166473385081978773682757 406213759702871020065517)
              ·
                refine ⟨152330159888576632524569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406213759702871020065517 152330159888576632524569)
                ·
                  rfl

theorem cell19_500617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 3].length) (baseStart_500617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500617 prefixEnd_500617 := by exact prefixLift 500617
  have htrace : WordTrace (prefixWord ++ tailWord_500617) baseStart_500617 baseEnd_500617 := by
    simpa [prefixWord, tailWord_500617, baseEnd_500617] using wordTrace_append hprefix tailTrace_500617
  have hstable : (prefixWord ++ tailWord_500617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500617).length < 2 ^ (prefixWord ++ tailWord_500617).sum := by decide
  have hdescent : baseEnd_500617 < baseStart_500617 := by decide
  rcases family_descends (prefixWord ++ tailWord_500617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500634 : List Nat := [3, 1, 1, 4, 4, 1, 5]
def baseStart_500634 : Nat := 118140960795 + 500634 * 2 ^ 59
def prefixEnd_500634 : Nat := 4983230072969 + 3 ^ 40 * 500634 * 2
def baseEnd_500634 : Nat := 50778444243575210048915

theorem tailTrace_500634 : CollatzResearch.WordTrace tailWord_500634 prefixEnd_500634 50778444243575210048915 := by
  unfold tailWord_500634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4564905517073998581297239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12173081378863996216792637 4564905517073998581297239)
  ·
    refine ⟨6847358275610997871945859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4564905517073998581297239 6847358275610997871945859)
    ·
      refine ⟨10271037413416496807918789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6847358275610997871945859 10271037413416496807918789)
      ·
        refine ⟨1925819515015593151484773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10271037413416496807918789 1925819515015593151484773)
        ·
          refine ⟨361091159065423715903395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1925819515015593151484773 361091159065423715903395)
          ·
            refine ⟨541636738598135573855093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361091159065423715903395 541636738598135573855093)
            ·
              refine ⟨50778444243575210048915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 541636738598135573855093 50778444243575210048915)
              ·
                rfl

theorem cell19_500634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 5].length) (baseStart_500634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500634 prefixEnd_500634 := by exact prefixLift 500634
  have htrace : WordTrace (prefixWord ++ tailWord_500634) baseStart_500634 baseEnd_500634 := by
    simpa [prefixWord, tailWord_500634, baseEnd_500634] using wordTrace_append hprefix tailTrace_500634
  have hstable : (prefixWord ++ tailWord_500634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500634).length < 2 ^ (prefixWord ++ tailWord_500634).sum := by decide
  have hdescent : baseEnd_500634 < baseStart_500634 := by decide
  rcases family_descends (prefixWord ++ tailWord_500634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500693 : List Nat := [1, 3, 2, 3, 4, 6]
def baseStart_500693 : Nat := 118140960795 + 500693 * 2 ^ 59
def prefixEnd_500693 : Nat := 4983230072969 + 3 ^ 40 * 500693 * 2
def baseEnd_500693 : Nat := 16928142837314552759497

theorem tailTrace_500693 : CollatzResearch.WordTrace tailWord_500693 prefixEnd_500693 16928142837314552759497 := by
  unfold tailWord_500693
  simp only [CollatzResearch.WordTrace]
  refine ⟨18261773975082247401586733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12174515983388164934391155 18261773975082247401586733)
  ·
    refine ⟨6848165240655842775595025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18261773975082247401586733 6848165240655842775595025)
    ·
      refine ⟨5136123930491882081696269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6848165240655842775595025 5136123930491882081696269)
      ·
        refine ⟨1926046473934455780636101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5136123930491882081696269 1926046473934455780636101)
        ·
          refine ⟨361133713862710458869269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1926046473934455780636101 361133713862710458869269)
          ·
            refine ⟨16928142837314552759497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 361133713862710458869269 16928142837314552759497)
            ·
              rfl

theorem cell19_500693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 6].length) (baseStart_500693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500693 prefixEnd_500693 := by exact prefixLift 500693
  have htrace : WordTrace (prefixWord ++ tailWord_500693) baseStart_500693 baseEnd_500693 := by
    simpa [prefixWord, tailWord_500693, baseEnd_500693] using wordTrace_append hprefix tailTrace_500693
  have hstable : (prefixWord ++ tailWord_500693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500693).length < 2 ^ (prefixWord ++ tailWord_500693).sum := by decide
  have hdescent : baseEnd_500693 < baseStart_500693 := by decide
  rcases family_descends (prefixWord ++ tailWord_500693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500822 : List Nat := [5, 2, 2, 1, 2, 1, 2, 4]
def baseStart_500822 : Nat := 118140960795 + 500822 * 2 ^ 59
def prefixEnd_500822 : Nat := 4983230072969 + 3 ^ 40 * 500822 * 2
def baseEnd_500822 : Nat := 152392538279196897968455

theorem tailTrace_500822 : CollatzResearch.WordTrace tailWord_500822 prefixEnd_500822 152392538279196897968455 := by
  unfold tailWord_500822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1141654936975931402064545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12177652661076601622021813 1141654936975931402064545)
  ·
    refine ⟨856241202731948551548409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1141654936975931402064545 856241202731948551548409)
    ·
      refine ⟨642180902048961413661307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 856241202731948551548409 642180902048961413661307)
      ·
        refine ⟨963271353073442120491961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642180902048961413661307 963271353073442120491961)
        ·
          refine ⟨722453514805081590368971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963271353073442120491961 722453514805081590368971)
          ·
            refine ⟨1083680272207622385553457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722453514805081590368971 1083680272207622385553457)
            ·
              refine ⟨812760204155716789165093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083680272207622385553457 812760204155716789165093)
              ·
                refine ⟨152392538279196897968455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 812760204155716789165093 152392538279196897968455)
                ·
                  rfl

theorem cell19_500822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_500822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500822 prefixEnd_500822 := by exact prefixLift 500822
  have htrace : WordTrace (prefixWord ++ tailWord_500822) baseStart_500822 baseEnd_500822 := by
    simpa [prefixWord, tailWord_500822, baseEnd_500822] using wordTrace_append hprefix tailTrace_500822
  have hstable : (prefixWord ++ tailWord_500822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500822).length < 2 ^ (prefixWord ++ tailWord_500822).sum := by decide
  have hdescent : baseEnd_500822 < baseStart_500822 := by decide
  rcases family_descends (prefixWord ++ tailWord_500822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500862 : List Nat := [4, 2, 4, 1, 8]
def baseStart_500862 : Nat := 118140960795 + 500862 * 2 ^ 59
def prefixEnd_500862 : Nat := 4983230072969 + 3 ^ 40 * 500862 * 2
def baseEnd_500862 : Nat := 5644618876758839151091

theorem tailTrace_500862 : CollatzResearch.WordTrace tailWord_500862 prefixEnd_500862 5644618876758839151091 := by
  unfold tailWord_500862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283492238933748658061105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12178625274313326176325893 2283492238933748658061105)
  ·
    refine ⟨1712619179200311493545829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2283492238933748658061105 1712619179200311493545829)
    ·
      refine ⟨321116096100058405039843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1712619179200311493545829 321116096100058405039843)
      ·
        refine ⟨481674144150087607559765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321116096100058405039843 481674144150087607559765)
        ·
          refine ⟨5644618876758839151091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 481674144150087607559765 5644618876758839151091)
          ·
            rfl

theorem cell19_500862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 8].length) (baseStart_500862 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500862 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500862 prefixEnd_500862 := by exact prefixLift 500862
  have htrace : WordTrace (prefixWord ++ tailWord_500862) baseStart_500862 baseEnd_500862 := by
    simpa [prefixWord, tailWord_500862, baseEnd_500862] using wordTrace_append hprefix tailTrace_500862
  have hstable : (prefixWord ++ tailWord_500862).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500862).length < 2 ^ (prefixWord ++ tailWord_500862).sum := by decide
  have hdescent : baseEnd_500862 < baseStart_500862 := by decide
  rcases family_descends (prefixWord ++ tailWord_500862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500961 : List Nat := [1, 2, 3, 1, 3, 3, 1, 5]
def baseStart_500961 : Nat := 118140960795 + 500961 * 2 ^ 59
def prefixEnd_500961 : Nat := 4983230072969 + 3 ^ 40 * 500961 * 2
def baseEnd_500961 : Nat := 152434833870885760879187

theorem tailTrace_500961 : CollatzResearch.WordTrace tailWord_500961 prefixEnd_500961 152434833870885760879187 := by
  unfold tailWord_500961
  simp only [CollatzResearch.WordTrace]
  refine ⟨18271548738111329172342737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12181032492074219448228491 18271548738111329172342737)
  ·
    refine ⟨13703661553583496879257053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18271548738111329172342737 13703661553583496879257053)
    ·
      refine ⟨5138873082593811329721395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13703661553583496879257053 5138873082593811329721395)
      ·
        refine ⟨7708309623890716994582093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5138873082593811329721395 7708309623890716994582093)
        ·
          refine ⟨2890616108959018872968285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7708309623890716994582093 2890616108959018872968285)
          ·
            refine ⟨1083981040859632077363107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2890616108959018872968285 1083981040859632077363107)
            ·
              refine ⟨1625971561289448116044661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083981040859632077363107 1625971561289448116044661)
              ·
                refine ⟨152434833870885760879187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1625971561289448116044661 152434833870885760879187)
                ·
                  rfl

theorem cell19_500961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_500961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500961 prefixEnd_500961 := by exact prefixLift 500961
  have htrace : WordTrace (prefixWord ++ tailWord_500961) baseStart_500961 baseEnd_500961 := by
    simpa [prefixWord, tailWord_500961, baseEnd_500961] using wordTrace_append hprefix tailTrace_500961
  have hstable : (prefixWord ++ tailWord_500961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500961).length < 2 ^ (prefixWord ++ tailWord_500961).sum := by decide
  have hdescent : baseEnd_500961 < baseStart_500961 := by decide
  rcases family_descends (prefixWord ++ tailWord_500961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500978 : List Nat := [3, 2, 1, 3, 3, 2, 5]
def baseStart_500978 : Nat := 118140960795 + 500978 * 2 ^ 59
def prefixEnd_500978 : Nat := 4983230072969 + 3 ^ 40 * 500978 * 2
def baseEnd_500978 : Nat := 50813335571011586167121

theorem tailTrace_500978 : CollatzResearch.WordTrace tailWord_500978 prefixEnd_500978 50813335571011586167121 := by
  unfold tailWord_500978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568042194762435268927897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12181445852699827383807725 4568042194762435268927897)
  ·
    refine ⟨3426031646071826451695923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4568042194762435268927897 3426031646071826451695923)
    ·
      refine ⟨5139047469107739677543885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3426031646071826451695923 5139047469107739677543885)
      ·
        refine ⟨1927142800915402379078957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5139047469107739677543885 1927142800915402379078957)
        ·
          refine ⟨722678550343275892154609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1927142800915402379078957 722678550343275892154609)
          ·
            refine ⟨542008912757456919115957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722678550343275892154609 542008912757456919115957)
            ·
              refine ⟨50813335571011586167121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 542008912757456919115957 50813335571011586167121)
              ·
                rfl

theorem cell19_500978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_500978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_500978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_500978 prefixEnd_500978 := by exact prefixLift 500978
  have htrace : WordTrace (prefixWord ++ tailWord_500978) baseStart_500978 baseEnd_500978 := by
    simpa [prefixWord, tailWord_500978, baseEnd_500978] using wordTrace_append hprefix tailTrace_500978
  have hstable : (prefixWord ++ tailWord_500978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500978).length < 2 ^ (prefixWord ++ tailWord_500978).sum := by decide
  have hdescent : baseEnd_500978 < baseStart_500978 := by decide
  rcases family_descends (prefixWord ++ tailWord_500978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501018 : List Nat := [3, 1, 1, 3, 3, 1, 2, 5]
def baseStart_501018 : Nat := 118140960795 + 501018 * 2 ^ 59
def prefixEnd_501018 : Nat := 4983230072969 + 3 ^ 40 * 501018 * 2
def baseEnd_501018 : Nat := 152452178106326517612365

theorem tailTrace_501018 : CollatzResearch.WordTrace tailWord_501018 prefixEnd_501018 152452178106326517612365 := by
  unfold tailWord_501018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568406924726206976791927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12182418465936551938111805 4568406924726206976791927)
  ·
    refine ⟨6852610387089310465187891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4568406924726206976791927 6852610387089310465187891)
    ·
      refine ⟨10278915580633965697781837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6852610387089310465187891 10278915580633965697781837)
      ·
        refine ⟨3854593342737737136668189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10278915580633965697781837 3854593342737737136668189)
        ·
          refine ⟨1445472503526651426250571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3854593342737737136668189 1445472503526651426250571)
          ·
            refine ⟨2168208755289977139375857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445472503526651426250571 2168208755289977139375857)
            ·
              refine ⟨1626156566467482854531893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168208755289977139375857 1626156566467482854531893)
              ·
                refine ⟨152452178106326517612365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1626156566467482854531893 152452178106326517612365)
                ·
                  rfl

theorem cell19_501018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_501018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501018 prefixEnd_501018 := by exact prefixLift 501018
  have htrace : WordTrace (prefixWord ++ tailWord_501018) baseStart_501018 baseEnd_501018 := by
    simpa [prefixWord, tailWord_501018, baseEnd_501018] using wordTrace_append hprefix tailTrace_501018
  have hstable : (prefixWord ++ tailWord_501018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501018).length < 2 ^ (prefixWord ++ tailWord_501018).sum := by decide
  have hdescent : baseEnd_501018 < baseStart_501018 := by decide
  rcases family_descends (prefixWord ++ tailWord_501018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501069 : List Nat := [1, 6, 1, 3, 1, 1, 3, 3]
def baseStart_501069 : Nat := 118140960795 + 501069 * 2 ^ 59
def prefixEnd_501069 : Nat := 4983230072969 + 3 ^ 40 * 501069 * 2
def baseEnd_501069 : Nat := 152467696632773510478893

theorem tailTrace_501069 : CollatzResearch.WordTrace tailWord_501069 prefixEnd_501069 152467696632773510478893 := by
  unfold tailWord_501069
  simp only [CollatzResearch.WordTrace]
  refine ⟨18275487821720063617274261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12183658547813375744849507 18275487821720063617274261)
  ·
    refine ⟨856663491643127982059731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18275487821720063617274261 856663491643127982059731)
    ·
      refine ⟨1284995237464691973089597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 856663491643127982059731 1284995237464691973089597)
      ·
        refine ⟨481873214049259489908599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1284995237464691973089597 481873214049259489908599)
        ·
          refine ⟨722809821073889234862899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481873214049259489908599 722809821073889234862899)
          ·
            refine ⟨1084214731610833852294349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722809821073889234862899 1084214731610833852294349)
            ·
              refine ⟨406580524354062694610381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1084214731610833852294349 406580524354062694610381)
              ·
                refine ⟨152467696632773510478893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406580524354062694610381 152467696632773510478893)
                ·
                  rfl

theorem cell19_501069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 3].length) (baseStart_501069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501069 prefixEnd_501069 := by exact prefixLift 501069
  have htrace : WordTrace (prefixWord ++ tailWord_501069) baseStart_501069 baseEnd_501069 := by
    simpa [prefixWord, tailWord_501069, baseEnd_501069] using wordTrace_append hprefix tailTrace_501069
  have hstable : (prefixWord ++ tailWord_501069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501069).length < 2 ^ (prefixWord ++ tailWord_501069).sum := by decide
  have hdescent : baseEnd_501069 < baseStart_501069 := by decide
  rcases family_descends (prefixWord ++ tailWord_501069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
