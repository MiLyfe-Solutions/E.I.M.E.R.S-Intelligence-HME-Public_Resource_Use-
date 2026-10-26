import V185TrunkScan23Chunk0335

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1986516 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1986516 : Nat := 118140960795 + 1986516 * 2 ^ 59
def prefixEnd_1986516 : Nat := 4983230072969 + 3 ^ 40 * 1986516 * 2
def baseEnd_1986516 : Nat := 1020037535847054980714185

theorem tailTrace_1986516 : CollatzResearch.WordTrace tailWord_1986516 prefixEnd_1986516 1020037535847054980714185 := by
  unfold tailWord_1986516
  simp only [CollatzResearch.WordTrace]
  refine ⟨36227095435599638383625701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48302793914132851178167601 36227095435599638383625701)
  ·
    refine ⟨6792580394174932196929819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36227095435599638383625701 6792580394174932196929819)
    ·
      refine ⟨10188870591262398295394729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6792580394174932196929819 10188870591262398295394729)
      ·
        refine ⟨7641652943446798721546047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10188870591262398295394729 7641652943446798721546047)
        ·
          refine ⟨11462479415170198082319071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7641652943446798721546047 11462479415170198082319071)
          ·
            refine ⟨17193719122755297123478607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11462479415170198082319071 17193719122755297123478607)
            ·
              refine ⟨25790578684132945685217911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17193719122755297123478607 25790578684132945685217911)
              ·
                refine ⟨38685868026199418527826867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25790578684132945685217911 38685868026199418527826867)
                ·
                  refine ⟨58028802039299127791740301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38685868026199418527826867 58028802039299127791740301)
                  ·
                    refine ⟨21760800764737172921902613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58028802039299127791740301 21760800764737172921902613)
                    ·
                      refine ⟨1020037535847054980714185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21760800764737172921902613 1020037535847054980714185)
                      ·
                        rfl

theorem cell23_1986516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1986516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986516 prefixEnd_1986516 := by exact prefixLift 1986516
  have htrace : WordTrace (prefixWord ++ tailWord_1986516) baseStart_1986516 baseEnd_1986516 := by
    simpa [prefixWord, tailWord_1986516, baseEnd_1986516] using wordTrace_append hprefix tailTrace_1986516
  have hstable : (prefixWord ++ tailWord_1986516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986516).length < 2 ^ (prefixWord ++ tailWord_1986516).sum := by decide
  have hdescent : baseEnd_1986516 < baseStart_1986516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986543 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 6]
def baseStart_1986543 : Nat := 118140960795 + 1986543 * 2 ^ 59
def prefixEnd_1986543 : Nat := 4983230072969 + 3 ^ 40 * 1986543 * 2
def baseEnd_1986543 : Nat := 113339044424969597230729

theorem tailTrace_1986543 : CollatzResearch.WordTrace tailWord_1986543 prefixEnd_1986543 113339044424969597230729 := by
  unfold tailWord_1986543
  simp only [CollatzResearch.WordTrace]
  refine ⟨72455175642101460378484283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48303450428067640252322855 72455175642101460378484283)
  ·
    refine ⟨108682763463152190567726425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72455175642101460378484283 108682763463152190567726425)
    ·
      refine ⟨81512072597364142925794819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108682763463152190567726425 81512072597364142925794819)
      ·
        refine ⟨122268108896046214388692229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81512072597364142925794819 122268108896046214388692229)
        ·
          refine ⟨22925270418008665197879793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122268108896046214388692229 22925270418008665197879793)
          ·
            refine ⟨17193952813506498898409845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22925270418008665197879793 17193952813506498898409845)
            ·
              refine ⟨1611933076266234271725923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17193952813506498898409845 1611933076266234271725923)
              ·
                refine ⟨2417899614399351407588885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611933076266234271725923 2417899614399351407588885)
                ·
                  refine ⟨113339044424969597230729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2417899614399351407588885 113339044424969597230729)
                  ·
                    rfl

theorem cell23_1986543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 6].length) (baseStart_1986543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986543 prefixEnd_1986543 := by exact prefixLift 1986543
  have htrace : WordTrace (prefixWord ++ tailWord_1986543) baseStart_1986543 baseEnd_1986543 := by
    simpa [prefixWord, tailWord_1986543, baseEnd_1986543] using wordTrace_append hprefix tailTrace_1986543
  have hstable : (prefixWord ++ tailWord_1986543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986543).length < 2 ^ (prefixWord ++ tailWord_1986543).sum := by decide
  have hdescent : baseEnd_1986543 < baseStart_1986543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986563 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 6, 3, 2]
def baseStart_1986563 : Nat := 118140960795 + 1986563 * 2 ^ 59
def prefixEnd_1986563 : Nat := 4983230072969 + 3 ^ 40 * 1986563 * 2
def baseEnd_1986563 : Nat := 1020061669437816296826469

theorem tailTrace_1986563 : CollatzResearch.WordTrace tailWord_1986563 prefixEnd_1986563 1020061669437816296826469 := by
  unfold tailWord_1986563
  simp only [CollatzResearch.WordTrace]
  refine ⟨72455905102029003794212343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48303936734686002529474895 72455905102029003794212343)
  ·
    refine ⟨108683857653043505691318515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72455905102029003794212343 108683857653043505691318515)
    ·
      refine ⟨163025786479565258536977773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108683857653043505691318515 163025786479565258536977773)
      ·
        refine ⟨61134669929836971951366665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163025786479565258536977773 61134669929836971951366665)
        ·
          refine ⟨45851002447377728963524999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61134669929836971951366665 45851002447377728963524999)
          ·
            refine ⟨68776503671066593445287499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45851002447377728963524999 68776503671066593445287499)
            ·
              refine ⟨103164755506599890167931249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68776503671066593445287499 103164755506599890167931249)
              ·
                refine ⟨77373566629949917625948437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103164755506599890167931249 77373566629949917625948437)
                ·
                  refine ⟨3626885935778902388716333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77373566629949917625948437 3626885935778902388716333)
                  ·
                    refine ⟨1360082225917088395768625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3626885935778902388716333 1360082225917088395768625)
                    ·
                      refine ⟨1020061669437816296826469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1360082225917088395768625 1020061669437816296826469)
                      ·
                        rfl

theorem cell23_1986563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 3, 2].length) (baseStart_1986563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986563 prefixEnd_1986563 := by exact prefixLift 1986563
  have htrace : WordTrace (prefixWord ++ tailWord_1986563) baseStart_1986563 baseEnd_1986563 := by
    simpa [prefixWord, tailWord_1986563, baseEnd_1986563] using wordTrace_append hprefix tailTrace_1986563
  have hstable : (prefixWord ++ tailWord_1986563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986563).length < 2 ^ (prefixWord ++ tailWord_1986563).sum := by decide
  have hdescent : baseEnd_1986563 < baseStart_1986563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986610 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_1986610 : Nat := 118140960795 + 1986610 * 2 ^ 59
def prefixEnd_1986610 : Nat := 4983230072969 + 3 ^ 40 * 1986610 * 2
def baseEnd_1986610 : Nat := 1020085803028577612938753

theorem tailTrace_1986610 : CollatzResearch.WordTrace tailWord_1986610 prefixEnd_1986610 1020085803028577612938753 := by
  unfold tailWord_1986610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18114404833214682705293321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48305079555239153880782189 18114404833214682705293321)
  ·
    refine ⟨13585803624911012028969991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18114404833214682705293321 13585803624911012028969991)
    ·
      refine ⟨20378705437366518043454987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13585803624911012028969991 20378705437366518043454987)
      ·
        refine ⟨30568058156049777065182481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20378705437366518043454987 30568058156049777065182481)
        ·
          refine ⟨22926043617037332798886861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30568058156049777065182481 22926043617037332798886861)
          ·
            refine ⟨8597266356388999799582573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22926043617037332798886861 8597266356388999799582573)
            ·
              refine ⟨3223974883645874924843465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8597266356388999799582573 3223974883645874924843465)
              ·
                refine ⟨2417981162734406193632599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223974883645874924843465 2417981162734406193632599)
                ·
                  refine ⟨3626971744101609290448899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417981162734406193632599 3626971744101609290448899)
                  ·
                    refine ⟨5440457616152413935673349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3626971744101609290448899 5440457616152413935673349)
                    ·
                      refine ⟨1020085803028577612938753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5440457616152413935673349 1020085803028577612938753)
                      ·
                        rfl

theorem cell23_1986610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_1986610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986610 prefixEnd_1986610 := by exact prefixLift 1986610
  have htrace : WordTrace (prefixWord ++ tailWord_1986610) baseStart_1986610 baseEnd_1986610 := by
    simpa [prefixWord, tailWord_1986610, baseEnd_1986610] using wordTrace_append hprefix tailTrace_1986610
  have hstable : (prefixWord ++ tailWord_1986610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986610).length < 2 ^ (prefixWord ++ tailWord_1986610).sum := by decide
  have hdescent : baseEnd_1986610 < baseStart_1986610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986637 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1986637 : Nat := 118140960795 + 1986637 * 2 ^ 59
def prefixEnd_1986637 : Nat := 4983230072969 + 3 ^ 40 * 1986637 * 2
def baseEnd_1986637 : Nat := 340033222335416335767043

theorem tailTrace_1986637 : CollatzResearch.WordTrace tailWord_1986637 prefixEnd_1986637 340033222335416335767043 := by
  unfold tailWord_1986637
  simp only [CollatzResearch.WordTrace]
  refine ⟨72458604103760914432406165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48305736069173942954937443 72458604103760914432406165)
  ·
    refine ⟨3396497067363792864019039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72458604103760914432406165 3396497067363792864019039)
    ·
      refine ⟨5094745601045689296028559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3396497067363792864019039 5094745601045689296028559)
      ·
        refine ⟨7642118401568533944042839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5094745601045689296028559 7642118401568533944042839)
        ·
          refine ⟨11463177602352800916064259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7642118401568533944042839 11463177602352800916064259)
          ·
            refine ⟨17194766403529201374096389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11463177602352800916064259 17194766403529201374096389)
            ·
              refine ⟨3224018700661725257643073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17194766403529201374096389 3224018700661725257643073)
              ·
                refine ⟨2418014025496293943232305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3224018700661725257643073 2418014025496293943232305)
                ·
                  refine ⟨1813510519122220457424229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2418014025496293943232305 1813510519122220457424229)
                  ·
                    refine ⟨340033222335416335767043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1813510519122220457424229 340033222335416335767043)
                    ·
                      rfl

theorem cell23_1986637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1986637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986637 prefixEnd_1986637 := by exact prefixLift 1986637
  have htrace : WordTrace (prefixWord ++ tailWord_1986637) baseStart_1986637 baseEnd_1986637 := by
    simpa [prefixWord, tailWord_1986637, baseEnd_1986637] using wordTrace_append hprefix tailTrace_1986637
  have hstable : (prefixWord ++ tailWord_1986637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986637).length < 2 ^ (prefixWord ++ tailWord_1986637).sum := by decide
  have hdescent : baseEnd_1986637 < baseStart_1986637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986654 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1986654 : Nat := 118140960795 + 1986654 * 2 ^ 59
def prefixEnd_1986654 : Nat := 4983230072969 + 3 ^ 40 * 1986654 * 2
def baseEnd_1986654 : Nat := 340036132059125146929517

theorem tailTrace_1986654 : CollatzResearch.WordTrace tailWord_1986654 prefixEnd_1986654 340036132059125146929517 := by
  unfold tailWord_1986654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9057403018087415791971877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48306149429799550890516677 9057403018087415791971877)
  ·
    refine ⟨1698263065891390460994727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9057403018087415791971877 1698263065891390460994727)
    ·
      refine ⟨2547394598837085691492091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1698263065891390460994727 2547394598837085691492091)
      ·
        refine ⟨3821091898255628537238137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547394598837085691492091 3821091898255628537238137)
        ·
          refine ⟨2865818923691721402928603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3821091898255628537238137 2865818923691721402928603)
          ·
            refine ⟨4298728385537582104392905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865818923691721402928603 4298728385537582104392905)
            ·
              refine ⟨3224046289153186578294679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4298728385537582104392905 3224046289153186578294679)
              ·
                refine ⟨4836069433729779867442019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224046289153186578294679 4836069433729779867442019)
                ·
                  refine ⟨7254104150594669801163029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4836069433729779867442019 7254104150594669801163029)
                  ·
                    refine ⟨340036132059125146929517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7254104150594669801163029 340036132059125146929517)
                    ·
                      rfl

theorem cell23_1986654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1986654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986654 prefixEnd_1986654 := by exact prefixLift 1986654
  have htrace : WordTrace (prefixWord ++ tailWord_1986654) baseStart_1986654 baseEnd_1986654 := by
    simpa [prefixWord, tailWord_1986654, baseEnd_1986654] using wordTrace_append hprefix tailTrace_1986654
  have hstable : (prefixWord ++ tailWord_1986654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986654).length < 2 ^ (prefixWord ++ tailWord_1986654).sum := by decide
  have hdescent : baseEnd_1986654 < baseStart_1986654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986693 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_1986693 : Nat := 118140960795 + 1986693 * 2 ^ 59
def prefixEnd_1986693 : Nat := 4983230072969 + 3 ^ 40 * 1986693 * 2
def baseEnd_1986693 : Nat := 340042807307633596066957

theorem tailTrace_1986693 : CollatzResearch.WordTrace tailWord_1986693 prefixEnd_1986693 340042807307633596066957 := by
  unfold tailWord_1986693
  simp only [CollatzResearch.WordTrace]
  refine ⟨72460646591558035996444733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48307097727705357330963155 72460646591558035996444733)
  ·
    refine ⟨27172742471834263498666775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72460646591558035996444733 27172742471834263498666775)
    ·
      refine ⟨40759113707751395248000163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27172742471834263498666775 40759113707751395248000163)
      ·
        refine ⟨61138670561627092872000245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40759113707751395248000163 61138670561627092872000245)
        ·
          refine ⟨5731750365152539956750023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61138670561627092872000245 5731750365152539956750023)
          ·
            refine ⟨8597625547728809935125035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5731750365152539956750023 8597625547728809935125035)
            ·
              refine ⟨12896438321593214902687553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8597625547728809935125035 12896438321593214902687553)
              ·
                refine ⟨9672328741194911177015665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12896438321593214902687553 9672328741194911177015665)
                ·
                  refine ⟨7254246555896183382761749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9672328741194911177015665 7254246555896183382761749)
                  ·
                    refine ⟨340042807307633596066957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7254246555896183382761749 340042807307633596066957)
                    ·
                      rfl

theorem cell23_1986693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_1986693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986693 prefixEnd_1986693 := by exact prefixLift 1986693
  have htrace : WordTrace (prefixWord ++ tailWord_1986693) baseStart_1986693 baseEnd_1986693 := by
    simpa [prefixWord, tailWord_1986693, baseEnd_1986693] using wordTrace_append hprefix tailTrace_1986693
  have hstable : (prefixWord ++ tailWord_1986693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986693).length < 2 ^ (prefixWord ++ tailWord_1986693).sum := by decide
  have hdescent : baseEnd_1986693 < baseStart_1986693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986717 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_1986717 : Nat := 118140960795 + 1986717 * 2 ^ 59
def prefixEnd_1986717 : Nat := 4983230072969 + 3 ^ 40 * 1986717 * 2
def baseEnd_1986717 : Nat := 1020140745458608694300761

theorem tailTrace_1986717 : CollatzResearch.WordTrace tailWord_1986717 prefixEnd_1986717 1020140745458608694300761 := by
  unfold tailWord_1986717
  simp only [CollatzResearch.WordTrace]
  refine ⟨72461521943471088095318405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48307681295647392063545603 72461521943471088095318405)
  ·
    refine ⟨13586535364400829017872201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72461521943471088095318405 13586535364400829017872201)
    ·
      refine ⟨10189901523300621763404151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13586535364400829017872201 10189901523300621763404151)
      ·
        refine ⟨15284852284950932645106227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10189901523300621763404151 15284852284950932645106227)
        ·
          refine ⟨22927278427426398967659341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15284852284950932645106227 22927278427426398967659341)
          ·
            refine ⟨8597729410284899612872253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22927278427426398967659341 8597729410284899612872253)
            ·
              refine ⟨3224148528856837354827095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8597729410284899612872253 3224148528856837354827095)
              ·
                refine ⟨4836222793285256032240643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224148528856837354827095 4836222793285256032240643)
                ·
                  refine ⟨7254334189927884048360965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4836222793285256032240643 7254334189927884048360965)
                  ·
                    refine ⟨1360187660611478259067681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7254334189927884048360965 1360187660611478259067681)
                    ·
                      refine ⟨1020140745458608694300761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1360187660611478259067681 1020140745458608694300761)
                      ·
                        rfl

theorem cell23_1986717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_1986717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986717 prefixEnd_1986717 := by exact prefixLift 1986717
  have htrace : WordTrace (prefixWord ++ tailWord_1986717) baseStart_1986717 baseEnd_1986717 := by
    simpa [prefixWord, tailWord_1986717, baseEnd_1986717] using wordTrace_append hprefix tailTrace_1986717
  have hstable : (prefixWord ++ tailWord_1986717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986717).length < 2 ^ (prefixWord ++ tailWord_1986717).sum := by decide
  have hdescent : baseEnd_1986717 < baseStart_1986717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986760 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 2, 5, 2]
def baseStart_1986760 : Nat := 118140960795 + 1986760 * 2 ^ 59
def prefixEnd_1986760 : Nat := 4983230072969 + 3 ^ 40 * 1986760 * 2
def baseEnd_1986760 : Nat := 1020162825126752026063063

theorem tailTrace_1986760 : CollatzResearch.WordTrace tailWord_1986760 prefixEnd_1986760 1020162825126752026063063 := by
  unfold tailWord_1986760
  simp only [CollatzResearch.WordTrace]
  refine ⟨36231545141157653219566867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48308726854876870959422489 36231545141157653219566867)
  ·
    refine ⟨54347317711736479829350301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36231545141157653219566867 54347317711736479829350301)
    ·
      refine ⟨20380244141901179936006363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54347317711736479829350301 20380244141901179936006363)
      ·
        refine ⟨30570366212851769904009545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20380244141901179936006363 30570366212851769904009545)
        ·
          refine ⟨22927774659638827428007159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30570366212851769904009545 22927774659638827428007159)
          ·
            refine ⟨34391661989458241142010739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22927774659638827428007159 34391661989458241142010739)
            ·
              refine ⟨51587492984187361713016109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34391661989458241142010739 51587492984187361713016109)
              ·
                refine ⟨19345309869070260642381041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51587492984187361713016109 19345309869070260642381041)
                ·
                  refine ⟨14508982401802695481785781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19345309869070260642381041 14508982401802695481785781)
                  ·
                    refine ⟨1360217100169002701417417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14508982401802695481785781 1360217100169002701417417)
                    ·
                      refine ⟨1020162825126752026063063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1360217100169002701417417 1020162825126752026063063)
                      ·
                        rfl

theorem cell23_1986760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_1986760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986760 prefixEnd_1986760 := by exact prefixLift 1986760
  have htrace : WordTrace (prefixWord ++ tailWord_1986760) baseStart_1986760 baseEnd_1986760 := by
    simpa [prefixWord, tailWord_1986760, baseEnd_1986760] using wordTrace_append hprefix tailTrace_1986760
  have hstable : (prefixWord ++ tailWord_1986760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986760).length < 2 ^ (prefixWord ++ tailWord_1986760).sum := by decide
  have hdescent : baseEnd_1986760 < baseStart_1986760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986763 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 5]
def baseStart_1986763 : Nat := 118140960795 + 1986763 * 2 ^ 59
def prefixEnd_1986763 : Nat := 4983230072969 + 3 ^ 40 * 1986763 * 2
def baseEnd_1986763 : Nat := 1020164365568715514325549

theorem tailTrace_1986763 : CollatzResearch.WordTrace tailWord_1986763 prefixEnd_1986763 1020164365568715514325549 := by
  unfold tailWord_1986763
  simp only [CollatzResearch.WordTrace]
  refine ⟨72463199701304437951492943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48308799800869625300995295 72463199701304437951492943)
  ·
    refine ⟨108694799551956656927239415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72463199701304437951492943 108694799551956656927239415)
    ·
      refine ⟨163042199327934985390859123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108694799551956656927239415 163042199327934985390859123)
      ·
        refine ⟨244563298991902478086288685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163042199327934985390859123 244563298991902478086288685)
        ·
          refine ⟨91711237121963429282358257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244563298991902478086288685 91711237121963429282358257)
          ·
            refine ⟨68783427841472571961768693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91711237121963429282358257 68783427841472571961768693)
            ·
              refine ⟨6448446360138053621415815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68783427841472571961768693 6448446360138053621415815)
              ·
                refine ⟨9672669540207080432123723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6448446360138053621415815 9672669540207080432123723)
                ·
                  refine ⟨14509004310310620648185585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9672669540207080432123723 14509004310310620648185585)
                  ·
                    refine ⟨10881753232732965486139189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14509004310310620648185585 10881753232732965486139189)
                    ·
                      refine ⟨1020164365568715514325549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10881753232732965486139189 1020164365568715514325549)
                      ·
                        rfl

theorem cell23_1986763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 5].length) (baseStart_1986763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986763 prefixEnd_1986763 := by exact prefixLift 1986763
  have htrace : WordTrace (prefixWord ++ tailWord_1986763) baseStart_1986763 baseEnd_1986763 := by
    simpa [prefixWord, tailWord_1986763, baseEnd_1986763] using wordTrace_append hprefix tailTrace_1986763
  have hstable : (prefixWord ++ tailWord_1986763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986763).length < 2 ^ (prefixWord ++ tailWord_1986763).sum := by decide
  have hdescent : baseEnd_1986763 < baseStart_1986763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986803 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 6]
def baseStart_1986803 : Nat := 118140960795 + 1986803 * 2 ^ 59
def prefixEnd_1986803 : Nat := 4983230072969 + 3 ^ 40 * 1986803 * 2
def baseEnd_1986803 : Nat := 1020184904794895357825365

theorem tailTrace_1986803 : CollatzResearch.WordTrace tailWord_1986803 prefixEnd_1986803 1020184904794895357825365 := by
  unfold tailWord_1986803
  simp only [CollatzResearch.WordTrace]
  refine ⟨72464658621159524782949063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48309772414106349855299375 72464658621159524782949063)
  ·
    refine ⟨108696987931739287174423595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72464658621159524782949063 108696987931739287174423595)
    ·
      refine ⟨163045481897608930761635393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108696987931739287174423595 163045481897608930761635393)
      ·
        refine ⟨122284111423206698071226545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163045481897608930761635393 122284111423206698071226545)
        ·
          refine ⟨91713083567405023553419909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122284111423206698071226545 91713083567405023553419909)
          ·
            refine ⟨17196203168888441916266233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91713083567405023553419909 17196203168888441916266233)
            ·
              refine ⟨12897152376666331437199675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17196203168888441916266233 12897152376666331437199675)
              ·
                refine ⟨19345728564999497155799513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12897152376666331437199675 19345728564999497155799513)
                ·
                  refine ⟨14509296423749622866849635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19345728564999497155799513 14509296423749622866849635)
                  ·
                    refine ⟨21763944635624434300274453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14509296423749622866849635 21763944635624434300274453)
                    ·
                      refine ⟨1020184904794895357825365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21763944635624434300274453 1020184904794895357825365)
                      ·
                        rfl

theorem cell23_1986803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_1986803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986803 prefixEnd_1986803 := by exact prefixLift 1986803
  have htrace : WordTrace (prefixWord ++ tailWord_1986803) baseStart_1986803 baseEnd_1986803 := by
    simpa [prefixWord, tailWord_1986803, baseEnd_1986803] using wordTrace_append hprefix tailTrace_1986803
  have hstable : (prefixWord ++ tailWord_1986803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986803).length < 2 ^ (prefixWord ++ tailWord_1986803).sum := by decide
  have hdescent : baseEnd_1986803 < baseStart_1986803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986813 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 8]
def baseStart_1986813 : Nat := 118140960795 + 1986813 * 2 ^ 59
def prefixEnd_1986813 : Nat := 4983230072969 + 3 ^ 40 * 1986813 * 2
def baseEnd_1986813 : Nat := 113354448844604479855591

theorem tailTrace_1986813 : CollatzResearch.WordTrace tailWord_1986813 prefixEnd_1986813 113354448844604479855591 := by
  unfold tailWord_1986813
  simp only [CollatzResearch.WordTrace]
  refine ⟨72465023351123296490813093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48310015567415530993875395 72465023351123296490813093)
  ·
    refine ⟨13587191878335618092027455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72465023351123296490813093 13587191878335618092027455)
    ·
      refine ⟨20380787817503427138041183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13587191878335618092027455 20380787817503427138041183)
      ·
        refine ⟨30571181726255140707061775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20380787817503427138041183 30571181726255140707061775)
        ·
          refine ⟨45856772589382711060592663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30571181726255140707061775 45856772589382711060592663)
          ·
            refine ⟨68785158884074066590888995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45856772589382711060592663 68785158884074066590888995)
            ·
              refine ⟨103177738326111099886333493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68785158884074066590888995 103177738326111099886333493)
              ·
                refine ⟨9672912968072915614343765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103177738326111099886333493 9672912968072915614343765)
                ·
                  refine ⟨113354448844604479855591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9672912968072915614343765 113354448844604479855591)
                  ·
                    rfl

theorem cell23_1986813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_1986813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986813 prefixEnd_1986813 := by exact prefixLift 1986813
  have htrace : WordTrace (prefixWord ++ tailWord_1986813) baseStart_1986813 baseEnd_1986813 := by
    simpa [prefixWord, tailWord_1986813, baseEnd_1986813] using wordTrace_append hprefix tailTrace_1986813
  have hstable : (prefixWord ++ tailWord_1986813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986813).length < 2 ^ (prefixWord ++ tailWord_1986813).sum := by decide
  have hdescent : baseEnd_1986813 < baseStart_1986813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986830 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_1986830 : Nat := 118140960795 + 1986830 * 2 ^ 59
def prefixEnd_1986830 : Nat := 4983230072969 + 3 ^ 40 * 1986830 * 2
def baseEnd_1986830 : Nat := 113355418752507416909749

theorem tailTrace_1986830 : CollatzResearch.WordTrace tailWord_1986830 prefixEnd_1986830 113355418752507416909749 := by
  unfold tailWord_1986830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9058205424007713549272743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48310428928041138929454629 9058205424007713549272743)
  ·
    refine ⟨13587308136011570323909115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9058205424007713549272743 13587308136011570323909115)
    ·
      refine ⟨20380962204017355485863673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13587308136011570323909115 20380962204017355485863673)
      ·
        refine ⟨15285721653013016614397755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20380962204017355485863673 15285721653013016614397755)
        ·
          refine ⟨22928582479519524921596633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15285721653013016614397755 22928582479519524921596633)
          ·
            refine ⟨17196436859639643691197475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22928582479519524921596633 17196436859639643691197475)
            ·
              refine ⟨25794655289459465536796213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17196436859639643691197475 25794655289459465536796213)
              ·
                refine ⟨2418248933386824894074645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25794655289459465536796213 2418248933386824894074645)
                ·
                  refine ⟨113355418752507416909749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2418248933386824894074645 113355418752507416909749)
                  ·
                    rfl

theorem cell23_1986830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_1986830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986830 prefixEnd_1986830 := by exact prefixLift 1986830
  have htrace : WordTrace (prefixWord ++ tailWord_1986830) baseStart_1986830 baseEnd_1986830 := by
    simpa [prefixWord, tailWord_1986830, baseEnd_1986830] using wordTrace_append hprefix tailTrace_1986830
  have hstable : (prefixWord ++ tailWord_1986830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986830).length < 2 ^ (prefixWord ++ tailWord_1986830).sum := by decide
  have hdescent : baseEnd_1986830 < baseStart_1986830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986867 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 4, 3, 2]
def baseStart_1986867 : Nat := 118140960795 + 1986867 * 2 ^ 59
def prefixEnd_1986867 : Nat := 4983230072969 + 3 ^ 40 * 1986867 * 2
def baseEnd_1986867 : Nat := 1020217767556783107425071

theorem tailTrace_1986867 : CollatzResearch.WordTrace tailWord_1986867 prefixEnd_1986867 1020217767556783107425071 := by
  unfold tailWord_1986867
  simp only [CollatzResearch.WordTrace]
  refine ⟨72466992892927663713278855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48311328595285109142185903 72466992892927663713278855)
  ·
    refine ⟨108700489339391495569918283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72466992892927663713278855 108700489339391495569918283)
    ·
      refine ⟨163050734009087243354877425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108700489339391495569918283 163050734009087243354877425)
      ·
        refine ⟨122288050506815432516158069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163050734009087243354877425 122288050506815432516158069)
        ·
          refine ⟨11464504735013946798389819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122288050506815432516158069 11464504735013946798389819)
          ·
            refine ⟨17196757102520920197584729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11464504735013946798389819 17196757102520920197584729)
            ·
              refine ⟨12897567826890690148188547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17196757102520920197584729 12897567826890690148188547)
              ·
                refine ⟨19346351740336035222282821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12897567826890690148188547 19346351740336035222282821)
                ·
                  refine ⟨3627440951313006604178029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19346351740336035222282821 3627440951313006604178029)
                  ·
                    refine ⟨1360290356742377476566761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3627440951313006604178029 1360290356742377476566761)
                    ·
                      refine ⟨1020217767556783107425071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1360290356742377476566761 1020217767556783107425071)
                      ·
                        rfl

theorem cell23_1986867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 3, 2].length) (baseStart_1986867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986867 prefixEnd_1986867 := by exact prefixLift 1986867
  have htrace : WordTrace (prefixWord ++ tailWord_1986867) baseStart_1986867 baseEnd_1986867 := by
    simpa [prefixWord, tailWord_1986867, baseEnd_1986867] using wordTrace_append hprefix tailTrace_1986867
  have hstable : (prefixWord ++ tailWord_1986867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986867).length < 2 ^ (prefixWord ++ tailWord_1986867).sum := by decide
  have hdescent : baseEnd_1986867 < baseStart_1986867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986874 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3]
def baseStart_1986874 : Nat := 118140960795 + 1986874 * 2 ^ 59
def prefixEnd_1986874 : Nat := 4983230072969 + 3 ^ 40 * 1986874 * 2
def baseEnd_1986874 : Nat := 1020221361921364580037539

theorem tailTrace_1986874 : CollatzResearch.WordTrace tailWord_1986874 prefixEnd_1986874 1020221361921364580037539 := by
  unfold tailWord_1986874
  simp only [CollatzResearch.WordTrace]
  refine ⟨18116812050975575977195919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48311498802601535939189117 18116812050975575977195919)
  ·
    refine ⟨27175218076463363965793879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18116812050975575977195919 27175218076463363965793879)
    ·
      refine ⟨40762827114695045948690819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27175218076463363965793879 40762827114695045948690819)
      ·
        refine ⟨61144240672042568923036229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40762827114695045948690819 61144240672042568923036229)
        ·
          refine ⟨11464545126007981673069293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61144240672042568923036229 11464545126007981673069293)
          ·
            refine ⟨4299204422252993127400985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11464545126007981673069293 4299204422252993127400985)
            ·
              refine ⟨3224403316689744845550739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4299204422252993127400985 3224403316689744845550739)
              ·
                refine ⟨4836604975034617268326109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224403316689744845550739 4836604975034617268326109)
                ·
                  refine ⟨1813726865637981475622291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4836604975034617268326109 1813726865637981475622291)
                  ·
                    refine ⟨2720590298456972213433437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1813726865637981475622291 2720590298456972213433437)
                    ·
                      refine ⟨1020221361921364580037539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2720590298456972213433437 1020221361921364580037539)
                      ·
                        rfl

theorem cell23_1986874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_1986874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986874 prefixEnd_1986874 := by exact prefixLift 1986874
  have htrace : WordTrace (prefixWord ++ tailWord_1986874) baseStart_1986874 baseEnd_1986874 := by
    simpa [prefixWord, tailWord_1986874, baseEnd_1986874] using wordTrace_append hprefix tailTrace_1986874
  have hstable : (prefixWord ++ tailWord_1986874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986874).length < 2 ^ (prefixWord ++ tailWord_1986874).sum := by decide
  have hdescent : baseEnd_1986874 < baseStart_1986874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986880 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 4]
def baseStart_1986880 : Nat := 118140960795 + 1986880 * 2 ^ 59
def prefixEnd_1986880 : Nat := 4983230072969 + 3 ^ 40 * 1986880 * 2
def baseEnd_1986880 : Nat := 1020224442805291556562511

theorem tailTrace_1986880 : CollatzResearch.WordTrace tailWord_1986880 prefixEnd_1986880 1020224442805291556562511 := by
  unfold tailWord_1986880
  simp only [CollatzResearch.WordTrace]
  refine ⟨36233733520940283466751047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48311644694587044622334729 36233733520940283466751047)
  ·
    refine ⟨54350600281410425200126571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36233733520940283466751047 54350600281410425200126571)
    ·
      refine ⟨81525900422115637800189857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54350600281410425200126571 81525900422115637800189857)
      ·
        refine ⟨61144425316586728350142393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81525900422115637800189857 61144425316586728350142393)
        ·
          refine ⟨45858318987440046262606795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61144425316586728350142393 45858318987440046262606795)
          ·
            refine ⟨68787478481160069393910193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45858318987440046262606795 68787478481160069393910193)
            ·
              refine ⟨51590608860870052045432645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68787478481160069393910193 51590608860870052045432645)
              ·
                refine ⟨9673239161413134758518621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51590608860870052045432645 9673239161413134758518621)
                ·
                  refine ⟨3627464685529925534444483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9673239161413134758518621 3627464685529925534444483)
                  ·
                    refine ⟨5441197028294888301666725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3627464685529925534444483 5441197028294888301666725)
                    ·
                      refine ⟨1020224442805291556562511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5441197028294888301666725 1020224442805291556562511)
                      ·
                        rfl

theorem cell23_1986880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_1986880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986880 prefixEnd_1986880 := by exact prefixLift 1986880
  have htrace : WordTrace (prefixWord ++ tailWord_1986880) baseStart_1986880 baseEnd_1986880 := by
    simpa [prefixWord, tailWord_1986880, baseEnd_1986880] using wordTrace_append hprefix tailTrace_1986880
  have hstable : (prefixWord ++ tailWord_1986880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986880).length < 2 ^ (prefixWord ++ tailWord_1986880).sum := by decide
  have hdescent : baseEnd_1986880 < baseStart_1986880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986897 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 4]
def baseStart_1986897 : Nat := 118140960795 + 1986897 * 2 ^ 59
def prefixEnd_1986897 : Nat := 4983230072969 + 3 ^ 40 * 1986897 * 2
def baseEnd_1986897 : Nat := 1020233171976417990049933

theorem tailTrace_1986897 : CollatzResearch.WordTrace tailWord_1986897 prefixEnd_1986897 1020233171976417990049933 := by
  unfold tailWord_1986897
  simp only [CollatzResearch.WordTrace]
  refine ⟨72468087082818978836870945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48312058055212652557913963 72468087082818978836870945)
  ·
    refine ⟨54351065312114234127653209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72468087082818978836870945 54351065312114234127653209)
    ·
      refine ⟨40763298984085675595739907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54351065312114234127653209 40763298984085675595739907)
      ·
        refine ⟨61144948476128513393609861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40763298984085675595739907 61144948476128513393609861)
        ·
          refine ⟨11464677839274096261301849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61144948476128513393609861 11464677839274096261301849)
          ·
            refine ⟨8598508379455572195976387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11464677839274096261301849 8598508379455572195976387)
            ·
              refine ⟨12897762569183358293964581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8598508379455572195976387 12897762569183358293964581)
              ·
                refine ⟨2418330481721879680118359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12897762569183358293964581 2418330481721879680118359)
                ·
                  refine ⟨3627495722582819520177539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418330481721879680118359 3627495722582819520177539)
                  ·
                    refine ⟨5441243583874229280266309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3627495722582819520177539 5441243583874229280266309)
                    ·
                      refine ⟨1020233171976417990049933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5441243583874229280266309 1020233171976417990049933)
                      ·
                        rfl

theorem cell23_1986897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_1986897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986897 prefixEnd_1986897 := by exact prefixLift 1986897
  have htrace : WordTrace (prefixWord ++ tailWord_1986897) baseStart_1986897 baseEnd_1986897 := by
    simpa [prefixWord, tailWord_1986897, baseEnd_1986897] using wordTrace_append hprefix tailTrace_1986897
  have hstable : (prefixWord ++ tailWord_1986897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986897).length < 2 ^ (prefixWord ++ tailWord_1986897).sum := by decide
  have hdescent : baseEnd_1986897 < baseStart_1986897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986914 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1986914 : Nat := 118140960795 + 1986914 * 2 ^ 59
def prefixEnd_1986914 : Nat := 4983230072969 + 3 ^ 40 * 1986914 * 2
def baseEnd_1986914 : Nat := 1020241901147544423537355

theorem tailTrace_1986914 : CollatzResearch.WordTrace tailWord_1986914 prefixEnd_1986914 1020241901147544423537355 := by
  unfold tailWord_1986914
  simp only [CollatzResearch.WordTrace]
  refine ⟨18117176780939347685059949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48312471415838260493493197 18117176780939347685059949)
  ·
    refine ⟨6793941292852255381897481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18117176780939347685059949 6793941292852255381897481)
    ·
      refine ⟨5095455969639191536423111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6793941292852255381897481 5095455969639191536423111)
      ·
        refine ⟨7643183954458787304634667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5095455969639191536423111 7643183954458787304634667)
        ·
          refine ⟨11464775931688180956952001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7643183954458787304634667 11464775931688180956952001)
          ·
            refine ⟨8598581948766135717714001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11464775931688180956952001 8598581948766135717714001)
            ·
              refine ⟨6448936461574601788285501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8598581948766135717714001 6448936461574601788285501)
              ·
                refine ⟨2418351173090475670607063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6448936461574601788285501 2418351173090475670607063)
                ·
                  refine ⟨3627526759635713505910595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418351173090475670607063 3627526759635713505910595)
                  ·
                    refine ⟨5441290139453570258865893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3627526759635713505910595 5441290139453570258865893)
                    ·
                      refine ⟨1020241901147544423537355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5441290139453570258865893 1020241901147544423537355)
                      ·
                        rfl

theorem cell23_1986914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1986914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986914 prefixEnd_1986914 := by exact prefixLift 1986914
  have htrace : WordTrace (prefixWord ++ tailWord_1986914) baseStart_1986914 baseEnd_1986914 := by
    simpa [prefixWord, tailWord_1986914, baseEnd_1986914] using wordTrace_append hprefix tailTrace_1986914
  have hstable : (prefixWord ++ tailWord_1986914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986914).length < 2 ^ (prefixWord ++ tailWord_1986914).sum := by decide
  have hdescent : baseEnd_1986914 < baseStart_1986914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986917 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 5]
def baseStart_1986917 : Nat := 118140960795 + 1986917 * 2 ^ 59
def prefixEnd_1986917 : Nat := 4983230072969 + 3 ^ 40 * 1986917 * 2
def baseEnd_1986917 : Nat := 1020243441589507911799841

theorem tailTrace_1986917 : CollatzResearch.WordTrace tailWord_1986917 prefixEnd_1986917 1020243441589507911799841 := by
  unfold tailWord_1986917
  simp only [CollatzResearch.WordTrace]
  refine ⟨72468816542746522252599005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48312544361831014835066003 72468816542746522252599005)
  ·
    refine ⟨27175806203529945844724627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72468816542746522252599005 27175806203529945844724627)
    ·
      refine ⟨40763709305294918767086941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27175806203529945844724627 40763709305294918767086941)
      ·
        refine ⟨15286390989485594537657603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40763709305294918767086941 15286390989485594537657603)
        ·
          refine ⟨22929586484228391806486405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15286390989485594537657603 22929586484228391806486405)
          ·
            refine ⟨4299297465792823463716201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22929586484228391806486405 4299297465792823463716201)
            ·
              refine ⟨3224473099344617597787151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4299297465792823463716201 3224473099344617597787151)
              ·
                refine ⟨4836709649016926396680727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224473099344617597787151 4836709649016926396680727)
                ·
                  refine ⟨7255064473525389595021091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4836709649016926396680727 7255064473525389595021091)
                  ·
                    refine ⟨10882596710288084392531637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7255064473525389595021091 10882596710288084392531637)
                    ·
                      refine ⟨1020243441589507911799841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10882596710288084392531637 1020243441589507911799841)
                      ·
                        rfl

theorem cell23_1986917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_1986917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986917 prefixEnd_1986917 := by exact prefixLift 1986917
  have htrace : WordTrace (prefixWord ++ tailWord_1986917) baseStart_1986917 baseEnd_1986917 := by
    simpa [prefixWord, tailWord_1986917, baseEnd_1986917] using wordTrace_append hprefix tailTrace_1986917
  have hstable : (prefixWord ++ tailWord_1986917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986917).length < 2 ^ (prefixWord ++ tailWord_1986917).sum := by decide
  have hdescent : baseEnd_1986917 < baseStart_1986917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986920 : List Nat := [2, 1, 4, 2, 2, 1, 11]
def baseStart_1986920 : Nat := 118140960795 + 1986920 * 2 ^ 59
def prefixEnd_1986920 : Nat := 4983230072969 + 3 ^ 40 * 1986920 * 2
def baseEnd_1986920 : Nat := 12595617062116930864967

theorem tailTrace_1986920 : CollatzResearch.WordTrace tailWord_1986920 prefixEnd_1986920 12595617062116930864967 := by
  unfold tailWord_1986920
  simp only [CollatzResearch.WordTrace]
  refine ⟨36234462980867826882479107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48312617307823769176638809 36234462980867826882479107)
  ·
    refine ⟨54351694471301740323718661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36234462980867826882479107 54351694471301740323718661)
    ·
      refine ⟨10190942713369076310697249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54351694471301740323718661 10190942713369076310697249)
      ·
        refine ⟨7643207035026807233022937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10190942713369076310697249 7643207035026807233022937)
        ·
          refine ⟨5732405276270105424767203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7643207035026807233022937 5732405276270105424767203)
          ·
            refine ⟨8598607914405158137150805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5732405276270105424767203 8598607914405158137150805)
            ·
              refine ⟨12595617062116930864967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8598607914405158137150805 12595617062116930864967)
              ·
                rfl

theorem cell23_1986920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 11].length) (baseStart_1986920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986920 prefixEnd_1986920 := by exact prefixLift 1986920
  have htrace : WordTrace (prefixWord ++ tailWord_1986920) baseStart_1986920 baseEnd_1986920 := by
    simpa [prefixWord, tailWord_1986920, baseEnd_1986920] using wordTrace_append hprefix tailTrace_1986920
  have hstable : (prefixWord ++ tailWord_1986920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986920).length < 2 ^ (prefixWord ++ tailWord_1986920).sum := by decide
  have hdescent : baseEnd_1986920 < baseStart_1986920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986941 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_1986941 : Nat := 118140960795 + 1986941 * 2 ^ 59
def prefixEnd_1986941 : Nat := 4983230072969 + 3 ^ 40 * 1986941 * 2
def baseEnd_1986941 : Nat := 340085255041738605966577

theorem tailTrace_1986941 : CollatzResearch.WordTrace tailWord_1986941 prefixEnd_1986941 340085255041738605966577 := by
  unfold tailWord_1986941
  simp only [CollatzResearch.WordTrace]
  refine ⟨72469691894659574351472677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48313127929773049567648451 72469691894659574351472677)
  ·
    refine ⟨13588067230248670190901127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72469691894659574351472677 13588067230248670190901127)
    ·
      refine ⟨20382100845373005286351691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13588067230248670190901127 20382100845373005286351691)
      ·
        refine ⟨30573151268059507929527537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20382100845373005286351691 30573151268059507929527537)
        ·
          refine ⟨22929863451044630947145653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30573151268059507929527537 22929863451044630947145653)
          ·
            refine ⟨2149674698535434151294905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22929863451044630947145653 2149674698535434151294905)
            ·
              refine ⟨1612256023901575613471179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2149674698535434151294905 1612256023901575613471179)
              ·
                refine ⟨2418384035852363420206769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612256023901575613471179 2418384035852363420206769)
                ·
                  refine ⟨1813788026889272565155077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2418384035852363420206769 1813788026889272565155077)
                  ·
                    refine ⟨340085255041738605966577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1813788026889272565155077 340085255041738605966577)
                    ·
                      rfl

theorem cell23_1986941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_1986941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986941 prefixEnd_1986941 := by exact prefixLift 1986941
  have htrace : WordTrace (prefixWord ++ tailWord_1986941) baseStart_1986941 baseEnd_1986941 := by
    simpa [prefixWord, tailWord_1986941, baseEnd_1986941] using wordTrace_append hprefix tailTrace_1986941
  have hstable : (prefixWord ++ tailWord_1986941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986941).length < 2 ^ (prefixWord ++ tailWord_1986941).sum := by decide
  have hdescent : baseEnd_1986941 < baseStart_1986941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987054 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_1987054 : Nat := 118140960795 + 1987054 * 2 ^ 59
def prefixEnd_1987054 : Nat := 4983230072969 + 3 ^ 40 * 1987054 * 2
def baseEnd_1987054 : Nat := 1020313788439173875786711

theorem tailTrace_1987054 : CollatzResearch.WordTrace tailWord_1987054 prefixEnd_1987054 1020313788439173875786711 := by
  unfold tailWord_1987054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9059226667906274331292027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48315875562166796433557477 9059226667906274331292027)
  ·
    refine ⟨13588840001859411496938041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9059226667906274331292027 13588840001859411496938041)
    ·
      refine ⟨10191630001394558622703531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13588840001859411496938041 10191630001394558622703531)
      ·
        refine ⟨15287445002091837934055297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10191630001394558622703531 15287445002091837934055297)
        ·
          refine ⟨11465583751568878450541473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15287445002091837934055297 11465583751568878450541473)
          ·
            refine ⟨8599187813676658837906105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11465583751568878450541473 8599187813676658837906105)
            ·
              refine ⟨6449390860257494128429579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8599187813676658837906105 6449390860257494128429579)
              ·
                refine ⟨9674086290386241192644369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449390860257494128429579 9674086290386241192644369)
                ·
                  refine ⟨7255564717789680894483277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9674086290386241192644369 7255564717789680894483277)
                  ·
                    refine ⟨2720836769171130335431229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7255564717789680894483277 2720836769171130335431229)
                    ·
                      refine ⟨1020313788439173875786711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2720836769171130335431229 1020313788439173875786711)
                      ·
                        rfl

theorem cell23_1987054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_1987054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987054 prefixEnd_1987054 := by exact prefixLift 1987054
  have htrace : WordTrace (prefixWord ++ tailWord_1987054) baseStart_1987054 baseEnd_1987054 := by
    simpa [prefixWord, tailWord_1987054, baseEnd_1987054] using wordTrace_append hprefix tailTrace_1987054
  have hstable : (prefixWord ++ tailWord_1987054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987054).length < 2 ^ (prefixWord ++ tailWord_1987054).sum := by decide
  have hdescent : baseEnd_1987054 < baseStart_1987054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987077 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_1987077 : Nat := 118140960795 + 1987077 * 2 ^ 59
def prefixEnd_1987077 : Nat := 4983230072969 + 3 ^ 40 * 1987077 * 2
def baseEnd_1987077 : Nat := 1020325598494227285799105

theorem tailTrace_1987077 : CollatzResearch.WordTrace tailWord_1987077 prefixEnd_1987077 1020325598494227285799105 := by
  unfold tailWord_1987077
  simp only [CollatzResearch.WordTrace]
  refine ⟨72474652222166869578423485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48316434814777913052282323 72474652222166869578423485)
  ·
    refine ⟨27177994583312576091908807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72474652222166869578423485 27177994583312576091908807)
    ·
      refine ⟨40766991874968864137863211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27177994583312576091908807 40766991874968864137863211)
      ·
        refine ⟨61150487812453296206794817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40766991874968864137863211 61150487812453296206794817)
        ·
          refine ⟨45862865859339972155096113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61150487812453296206794817 45862865859339972155096113)
          ·
            refine ⟨34397149394504979116322085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45862865859339972155096113 34397149394504979116322085)
            ·
              refine ⟨6449465511469683584310391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34397149394504979116322085 6449465511469683584310391)
              ·
                refine ⟨9674198267204525376465587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449465511469683584310391 9674198267204525376465587)
                ·
                  refine ⟨14511297400806788064698381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9674198267204525376465587 14511297400806788064698381)
                  ·
                    refine ⟨5441736525302545524261893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14511297400806788064698381 5441736525302545524261893)
                    ·
                      refine ⟨1020325598494227285799105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5441736525302545524261893 1020325598494227285799105)
                      ·
                        rfl

theorem cell23_1987077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_1987077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987077 prefixEnd_1987077 := by exact prefixLift 1987077
  have htrace : WordTrace (prefixWord ++ tailWord_1987077) baseStart_1987077 baseEnd_1987077 := by
    simpa [prefixWord, tailWord_1987077, baseEnd_1987077] using wordTrace_append hprefix tailTrace_1987077
  have hstable : (prefixWord ++ tailWord_1987077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987077).length < 2 ^ (prefixWord ++ tailWord_1987077).sum := by decide
  have hdescent : baseEnd_1987077 < baseStart_1987077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987087 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 7, 4]
def baseStart_1987087 : Nat := 118140960795 + 1987087 * 2 ^ 59
def prefixEnd_1987087 : Nat := 4983230072969 + 3 ^ 40 * 1987087 * 2
def baseEnd_1987087 : Nat := 340110244433590748891353

theorem tailTrace_1987087 : CollatzResearch.WordTrace tailWord_1987087 prefixEnd_1987087 340110244433590748891353 := by
  unfold tailWord_1987087
  simp only [CollatzResearch.WordTrace]
  refine ⟨72475016952130641286287515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48316677968087094190858343 72475016952130641286287515)
  ·
    refine ⟨108712525428195961929431273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72475016952130641286287515 108712525428195961929431273)
    ·
      refine ⟨81534394071146971447073455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108712525428195961929431273 81534394071146971447073455)
      ·
        refine ⟨122301591106720457170610183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81534394071146971447073455 122301591106720457170610183)
        ·
          refine ⟨183452386660080685755915275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122301591106720457170610183 183452386660080685755915275)
          ·
            refine ⟨275178579990121028633872913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183452386660080685755915275 275178579990121028633872913)
            ·
              refine ⟨206383934992590771475404685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275178579990121028633872913 206383934992590771475404685)
              ·
                refine ⟨77393975622221539303276757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206383934992590771475404685 77393975622221539303276757)
                ·
                  refine ⟨1813921303645817327420549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 77393975622221539303276757 1813921303645817327420549)
                  ·
                    refine ⟨340110244433590748891353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1813921303645817327420549 340110244433590748891353)
                    ·
                      rfl

theorem cell23_1987087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 4].length) (baseStart_1987087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987087 prefixEnd_1987087 := by exact prefixLift 1987087
  have htrace : WordTrace (prefixWord ++ tailWord_1987087) baseStart_1987087 baseEnd_1987087 := by
    simpa [prefixWord, tailWord_1987087, baseEnd_1987087] using wordTrace_append hprefix tailTrace_1987087
  have hstable : (prefixWord ++ tailWord_1987087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987087).length < 2 ^ (prefixWord ++ tailWord_1987087).sum := by decide
  have hdescent : baseEnd_1987087 < baseStart_1987087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987187 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 5]
def baseStart_1987187 : Nat := 118140960795 + 1987187 * 2 ^ 59
def prefixEnd_1987187 : Nat := 4983230072969 + 3 ^ 40 * 1987187 * 2
def baseEnd_1987187 : Nat := 1020382081366221855423599

theorem tailTrace_1987187 : CollatzResearch.WordTrace tailWord_1987187 prefixEnd_1987187 1020382081366221855423599 := by
  unfold tailWord_1987187
  simp only [CollatzResearch.WordTrace]
  refine ⟨72478664251768358364927815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48319109501178905576618543 72478664251768358364927815)
  ·
    refine ⟨108717996377652537547391723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72478664251768358364927815 108717996377652537547391723)
    ·
      refine ⟨163076994566478806321087585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108717996377652537547391723 163076994566478806321087585)
      ·
        refine ⟨122307745924859104740815689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163076994566478806321087585 122307745924859104740815689)
        ·
          refine ⟨91730809443644328555611767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122307745924859104740815689 91730809443644328555611767)
          ·
            refine ⟨137596214165466492833417651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91730809443644328555611767 137596214165466492833417651)
            ·
              refine ⟨206394321248199739250126477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137596214165466492833417651 206394321248199739250126477)
              ·
                refine ⟨77397870468074902218797429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206394321248199739250126477 77397870468074902218797429)
                ·
                  refine ⟨7256050356382022083012259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77397870468074902218797429 7256050356382022083012259)
                  ·
                    refine ⟨10884075534573033124518389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7256050356382022083012259 10884075534573033124518389)
                    ·
                      refine ⟨1020382081366221855423599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10884075534573033124518389 1020382081366221855423599)
                      ·
                        rfl

theorem cell23_1987187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_1987187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987187 prefixEnd_1987187 := by exact prefixLift 1987187
  have htrace : WordTrace (prefixWord ++ tailWord_1987187) baseStart_1987187 baseEnd_1987187 := by
    simpa [prefixWord, tailWord_1987187, baseEnd_1987187] using wordTrace_append hprefix tailTrace_1987187
  have hstable : (prefixWord ++ tailWord_1987187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987187).length < 2 ^ (prefixWord ++ tailWord_1987187).sum := by decide
  have hdescent : baseEnd_1987187 < baseStart_1987187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987201 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1987201 : Nat := 118140960795 + 1987201 * 2 ^ 59
def prefixEnd_1987201 : Nat := 4983230072969 + 3 ^ 40 * 1987201 * 2
def baseEnd_1987201 : Nat := 1020389270095384800648535

theorem tailTrace_1987201 : CollatzResearch.WordTrace tailWord_1987201 prefixEnd_1987201 1020389270095384800648535 := by
  unfold tailWord_1987201
  simp only [CollatzResearch.WordTrace]
  refine ⟨72479174873717638755937457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48319449915811759170624971 72479174873717638755937457)
  ·
    refine ⟨54359381155288229066953093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72479174873717638755937457 54359381155288229066953093)
    ·
      refine ⟨10192383966616542950053705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54359381155288229066953093 10192383966616542950053705)
      ·
        refine ⟨7644287974962407212540279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10192383966616542950053705 7644287974962407212540279)
        ·
          refine ⟨11466431962443610818810419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7644287974962407212540279 11466431962443610818810419)
          ·
            refine ⟨17199647943665416228215629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11466431962443610818810419 17199647943665416228215629)
            ·
              refine ⟨6449867978874531085580861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17199647943665416228215629 6449867978874531085580861)
              ·
                refine ⟨2418700492077949157092823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6449867978874531085580861 2418700492077949157092823)
                ·
                  refine ⟨3628050738116923735639235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418700492077949157092823 3628050738116923735639235)
                  ·
                    refine ⟨5442076107175385603458853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3628050738116923735639235 5442076107175385603458853)
                    ·
                      refine ⟨1020389270095384800648535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5442076107175385603458853 1020389270095384800648535)
                      ·
                        rfl

theorem cell23_1987201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1987201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987201 prefixEnd_1987201 := by exact prefixLift 1987201
  have htrace : WordTrace (prefixWord ++ tailWord_1987201) baseStart_1987201 baseEnd_1987201 := by
    simpa [prefixWord, tailWord_1987201, baseEnd_1987201] using wordTrace_append hprefix tailTrace_1987201
  have hstable : (prefixWord ++ tailWord_1987201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987201).length < 2 ^ (prefixWord ++ tailWord_1987201).sum := by decide
  have hdescent : baseEnd_1987201 < baseStart_1987201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987202 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 6]
def baseStart_1987202 : Nat := 118140960795 + 1987202 * 2 ^ 59
def prefixEnd_1987202 : Nat := 4983230072969 + 3 ^ 40 * 1987202 * 2
def baseEnd_1987202 : Nat := 113376642619559921859559

theorem tailTrace_1987202 : CollatzResearch.WordTrace tailWord_1987202 prefixEnd_1987202 113376642619559921859559 := by
  unfold tailWord_1987202
  simp only [CollatzResearch.WordTrace]
  refine ⟨18119802836678503981680965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48319474231142677284482573 18119802836678503981680965)
  ·
    refine ⟨3397463031877219496565181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18119802836678503981680965 3397463031877219496565181)
    ·
      refine ⟨1274048636953957311211943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3397463031877219496565181 1274048636953957311211943)
      ·
        refine ⟨1911072955430935966817915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274048636953957311211943 1911072955430935966817915)
        ·
          refine ⟨2866609433146403950226873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911072955430935966817915 2866609433146403950226873)
          ·
            refine ⟨2149957074859802962670155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2866609433146403950226873 2149957074859802962670155)
            ·
              refine ⟨3224935612289704444005233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149957074859802962670155 3224935612289704444005233)
              ·
                refine ⟨2418701709217278333003925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3224935612289704444005233 2418701709217278333003925)
                ·
                  refine ⟨113376642619559921859559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2418701709217278333003925 113376642619559921859559)
                  ·
                    rfl

theorem cell23_1987202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_1987202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987202 prefixEnd_1987202 := by exact prefixLift 1987202
  have htrace : WordTrace (prefixWord ++ tailWord_1987202) baseStart_1987202 baseEnd_1987202 := by
    simpa [prefixWord, tailWord_1987202, baseEnd_1987202] using wordTrace_append hprefix tailTrace_1987202
  have hstable : (prefixWord ++ tailWord_1987202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987202).length < 2 ^ (prefixWord ++ tailWord_1987202).sum := by decide
  have hdescent : baseEnd_1987202 < baseStart_1987202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987207 : List Nat := [1, 1, 4, 2, 1, 2, 12]
def baseStart_1987207 : Nat := 118140960795 + 1987207 * 2 ^ 59
def prefixEnd_1987207 : Nat := 4983230072969 + 3 ^ 40 * 1987207 * 2
def baseEnd_1987207 : Nat := 12597436431843355273747

theorem tailTrace_1987207 : CollatzResearch.WordTrace tailWord_1987207 prefixEnd_1987207 12597436431843355273747 := by
  unfold tailWord_1987207
  simp only [CollatzResearch.WordTrace]
  refine ⟨72479393711695901780655875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48319595807797267853770583 72479393711695901780655875)
  ·
    refine ⟨108719090567543852670983813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72479393711695901780655875 108719090567543852670983813)
    ·
      refine ⟨20384829481414472375809465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108719090567543852670983813 20384829481414472375809465)
      ·
        refine ⟨15288622111060854281857099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20384829481414472375809465 15288622111060854281857099)
        ·
          refine ⟨22932933166591281422785649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15288622111060854281857099 22932933166591281422785649)
          ·
            refine ⟨17199699874943461067089237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22932933166591281422785649 17199699874943461067089237)
            ·
              refine ⟨12597436431843355273747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 17199699874943461067089237 12597436431843355273747)
              ·
                rfl

theorem cell23_1987207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 12].length) (baseStart_1987207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987207 prefixEnd_1987207 := by exact prefixLift 1987207
  have htrace : WordTrace (prefixWord ++ tailWord_1987207) baseStart_1987207 baseEnd_1987207 := by
    simpa [prefixWord, tailWord_1987207, baseEnd_1987207] using wordTrace_append hprefix tailTrace_1987207
  have hstable : (prefixWord ++ tailWord_1987207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987207).length < 2 ^ (prefixWord ++ tailWord_1987207).sum := by decide
  have hdescent : baseEnd_1987207 < baseStart_1987207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987214 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1987214 : Nat := 118140960795 + 1987214 * 2 ^ 59
def prefixEnd_1987214 : Nat := 4983230072969 + 3 ^ 40 * 1987214 * 2
def baseEnd_1987214 : Nat := 1020395945343893249785975

theorem tailTrace_1987214 : CollatzResearch.WordTrace tailWord_1987214 prefixEnd_1987214 1020395945343893249785975 := by
  unfold tailWord_1987214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9059956127833817747020087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48319766015113694650773797 9059956127833817747020087)
  ·
    refine ⟨13589934191750726620530131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9059956127833817747020087 13589934191750726620530131)
    ·
      refine ⟨20384901287626089930795197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13589934191750726620530131 20384901287626089930795197)
      ·
        refine ⟨7644337982859783724048199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20384901287626089930795197 7644337982859783724048199)
        ·
          refine ⟨11466506974289675586072299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7644337982859783724048199 11466506974289675586072299)
          ·
            refine ⟨17199760461434513379108449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11466506974289675586072299 17199760461434513379108449)
            ·
              refine ⟨12899820346075885034331337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17199760461434513379108449 12899820346075885034331337)
              ·
                refine ⟨9674865259556913775748503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12899820346075885034331337 9674865259556913775748503)
                ·
                  refine ⟨14512297889335370663622755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9674865259556913775748503 14512297889335370663622755)
                  ·
                    refine ⟨21768446834003055995434133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14512297889335370663622755 21768446834003055995434133)
                    ·
                      refine ⟨1020395945343893249785975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21768446834003055995434133 1020395945343893249785975)
                      ·
                        rfl

theorem cell23_1987214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1987214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987214 prefixEnd_1987214 := by exact prefixLift 1987214
  have htrace : WordTrace (prefixWord ++ tailWord_1987214) baseStart_1987214 baseEnd_1987214 := by
    simpa [prefixWord, tailWord_1987214, baseEnd_1987214] using wordTrace_append hprefix tailTrace_1987214
  have hstable : (prefixWord ++ tailWord_1987214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987214).length < 2 ^ (prefixWord ++ tailWord_1987214).sum := by decide
  have hdescent : baseEnd_1987214 < baseStart_1987214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987251 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 4, 1, 3]
def baseStart_1987251 : Nat := 118140960795 + 1987251 * 2 ^ 59
def prefixEnd_1987251 : Nat := 4983230072969 + 3 ^ 40 * 1987251 * 2
def baseEnd_1987251 : Nat := 1020414944128109605023305

theorem tailTrace_1987251 : CollatzResearch.WordTrace tailWord_1987251 prefixEnd_1987251 1020414944128109605023305 := by
  unfold tailWord_1987251
  simp only [CollatzResearch.WordTrace]
  refine ⟨72480998523536497295257607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48320665682357664863505071 72480998523536497295257607)
  ·
    refine ⟨108721497785304745942886411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72480998523536497295257607 108721497785304745942886411)
    ·
      refine ⟨163082246677957118914329617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108721497785304745942886411 163082246677957118914329617)
      ·
        refine ⟨122311685008467839185747213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163082246677957118914329617 122311685008467839185747213)
        ·
          refine ⟨45866881878175439694655205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122311685008467839185747213 45866881878175439694655205)
          ·
            refine ⟨8600040352157894942747851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45866881878175439694655205 8600040352157894942747851)
            ·
              refine ⟨12900060528236842414121777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8600040352157894942747851 12900060528236842414121777)
              ·
                refine ⟨9675045396177631810591333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12900060528236842414121777 9675045396177631810591333)
                ·
                  refine ⟨1814071011783305964485875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9675045396177631810591333 1814071011783305964485875)
                  ·
                    refine ⟨2721106517674958946728813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1814071011783305964485875 2721106517674958946728813)
                    ·
                      refine ⟨1020414944128109605023305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2721106517674958946728813 1020414944128109605023305)
                      ·
                        rfl

theorem cell23_1987251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 1, 3].length) (baseStart_1987251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987251 prefixEnd_1987251 := by exact prefixLift 1987251
  have htrace : WordTrace (prefixWord ++ tailWord_1987251) baseStart_1987251 baseEnd_1987251 := by
    simpa [prefixWord, tailWord_1987251, baseEnd_1987251] using wordTrace_append hprefix tailTrace_1987251
  have hstable : (prefixWord ++ tailWord_1987251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987251).length < 2 ^ (prefixWord ++ tailWord_1987251).sum := by decide
  have hdescent : baseEnd_1987251 < baseStart_1987251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987268 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1987268 : Nat := 118140960795 + 1987268 * 2 ^ 59
def prefixEnd_1987268 : Nat := 4983230072969 + 3 ^ 40 * 1987268 * 2
def baseEnd_1987268 : Nat := 1020423673299236038510727

theorem tailTrace_1987268 : CollatzResearch.WordTrace tailWord_1987268 prefixEnd_1987268 1020423673299236038510727 := by
  unfold tailWord_1987268
  simp only [CollatzResearch.WordTrace]
  refine ⟨36240809282237454599313229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48321079042983272799084305 36240809282237454599313229)
  ·
    refine ⟨13590303480839045474742461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36240809282237454599313229 13590303480839045474742461)
    ·
      refine ⟨5096363805314642053028423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13590303480839045474742461 5096363805314642053028423)
      ·
        refine ⟨7644545707971963079542635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5096363805314642053028423 7644545707971963079542635)
        ·
          refine ⟨11466818561957944619313953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7644545707971963079542635 11466818561957944619313953)
          ·
            refine ⟨8600113921468458464485465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11466818561957944619313953 8600113921468458464485465)
            ·
              refine ⟨6450085441101343848364099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8600113921468458464485465 6450085441101343848364099)
              ·
                refine ⟨9675128161652015772546149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6450085441101343848364099 9675128161652015772546149)
                ·
                  refine ⟨1814086530309752957352403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9675128161652015772546149 1814086530309752957352403)
                  ·
                    refine ⟨2721129795464629436028605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1814086530309752957352403 2721129795464629436028605)
                    ·
                      refine ⟨1020423673299236038510727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2721129795464629436028605 1020423673299236038510727)
                      ·
                        rfl

theorem cell23_1987268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1987268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987268 prefixEnd_1987268 := by exact prefixLift 1987268
  have htrace : WordTrace (prefixWord ++ tailWord_1987268) baseStart_1987268 baseEnd_1987268 := by
    simpa [prefixWord, tailWord_1987268, baseEnd_1987268] using wordTrace_append hprefix tailTrace_1987268
  have hstable : (prefixWord ++ tailWord_1987268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987268).length < 2 ^ (prefixWord ++ tailWord_1987268).sum := by decide
  have hdescent : baseEnd_1987268 < baseStart_1987268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987295 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 1, 3, 2]
def baseStart_1987295 : Nat := 118140960795 + 1987295 * 2 ^ 59
def prefixEnd_1987295 : Nat := 4983230072969 + 3 ^ 40 * 1987295 * 2
def baseEnd_1987295 : Nat := 1020437537276907432873103

theorem tailTrace_1987295 : CollatzResearch.WordTrace tailWord_1987295 prefixEnd_1987295 1020437537276907432873103 := by
  unfold tailWord_1987295
  simp only [CollatzResearch.WordTrace]
  refine ⟨72482603335377092809859339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48321735556918061873239559 72482603335377092809859339)
  ·
    refine ⟨108723905003065639214789009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72482603335377092809859339 108723905003065639214789009)
    ·
      refine ⟨81542928752299229411091757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108723905003065639214789009 81542928752299229411091757)
      ·
        refine ⟨30578598282112211029159409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81542928752299229411091757 30578598282112211029159409)
        ·
          refine ⟨22933948711584158271869557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30578598282112211029159409 22933948711584158271869557)
          ·
            refine ⟨2150057691711014837987771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22933948711584158271869557 2150057691711014837987771)
            ·
              refine ⟨3225086537566522256981657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150057691711014837987771 3225086537566522256981657)
              ·
                refine ⟨2418814903174891692736243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225086537566522256981657 2418814903174891692736243)
                ·
                  refine ⟨3628222354762337539104365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418814903174891692736243 3628222354762337539104365)
                  ·
                    refine ⟨1360583383035876577164137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3628222354762337539104365 1360583383035876577164137)
                    ·
                      refine ⟨1020437537276907432873103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1360583383035876577164137 1020437537276907432873103)
                      ·
                        rfl

theorem cell23_1987295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_1987295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987295 prefixEnd_1987295 := by exact prefixLift 1987295
  have htrace : WordTrace (prefixWord ++ tailWord_1987295) baseStart_1987295 baseEnd_1987295 := by
    simpa [prefixWord, tailWord_1987295, baseEnd_1987295] using wordTrace_append hprefix tailTrace_1987295
  have hstable : (prefixWord ++ tailWord_1987295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987295).length < 2 ^ (prefixWord ++ tailWord_1987295).sum := by decide
  have hdescent : baseEnd_1987295 < baseStart_1987295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987325 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 2, 2, 2]
def baseStart_1987325 : Nat := 118140960795 + 1987325 * 2 ^ 59
def prefixEnd_1987325 : Nat := 4983230072969 + 3 ^ 40 * 1987325 * 2
def baseEnd_1987325 : Nat := 1020452941696542315497965

theorem tailTrace_1987325 : CollatzResearch.WordTrace tailWord_1987325 prefixEnd_1987325 1020452941696542315497965 := by
  unfold tailWord_1987325
  simp only [CollatzResearch.WordTrace]
  refine ⟨72483697525268407933451429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48322465016845605288967619 72483697525268407933451429)
  ·
    refine ⟨13590693285987826487522143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72483697525268407933451429 13590693285987826487522143)
    ·
      refine ⟨20386039928981739731283215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13590693285987826487522143 20386039928981739731283215)
      ·
        refine ⟨30579059893472609596924823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20386039928981739731283215 30579059893472609596924823)
        ·
          refine ⟨45868589840208914395387235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30579059893472609596924823 45868589840208914395387235)
          ·
            refine ⟨68802884760313371593080853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45868589840208914395387235 68802884760313371593080853)
            ·
              refine ⟨3225135223139689293425665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68802884760313371593080853 3225135223139689293425665)
              ·
                refine ⟨2418851417354766970069249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225135223139689293425665 2418851417354766970069249)
                ·
                  refine ⟨1814138563016075227551937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2418851417354766970069249 1814138563016075227551937)
                  ·
                    refine ⟨1360603922262056420663953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1814138563016075227551937 1360603922262056420663953)
                    ·
                      refine ⟨1020452941696542315497965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1360603922262056420663953 1020452941696542315497965)
                      ·
                        rfl

theorem cell23_1987325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_1987325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987325 prefixEnd_1987325 := by exact prefixLift 1987325
  have htrace : WordTrace (prefixWord ++ tailWord_1987325) baseStart_1987325 baseEnd_1987325 := by
    simpa [prefixWord, tailWord_1987325, baseEnd_1987325] using wordTrace_append hprefix tailTrace_1987325
  have hstable : (prefixWord ++ tailWord_1987325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987325).length < 2 ^ (prefixWord ++ tailWord_1987325).sum := by decide
  have hdescent : baseEnd_1987325 < baseStart_1987325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987401 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 1, 4, 3]
def baseStart_1987401 : Nat := 118140960795 + 1987401 * 2 ^ 59
def prefixEnd_1987401 : Nat := 4983230072969 + 3 ^ 40 * 1987401 * 2
def baseEnd_1987401 : Nat := 1020491966226284018147615

theorem tailTrace_1987401 : CollatzResearch.WordTrace tailWord_1987401 prefixEnd_1987401 1020491966226284018147615 := by
  unfold tailWord_1987401
  simp only [CollatzResearch.WordTrace]
  refine ⟨72486469472993072913218057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48324312981995381942145371 72486469472993072913218057)
  ·
    refine ⟨54364852104744804684913543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72486469472993072913218057 54364852104744804684913543)
    ·
      refine ⟨81547278157117207027370315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54364852104744804684913543 81547278157117207027370315)
      ·
        refine ⟨122320917235675810541055473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81547278157117207027370315 122320917235675810541055473)
        ·
          refine ⟨91740687926756857905791605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122320917235675810541055473 91740687926756857905791605)
          ·
            refine ⟨8600689493133455428667963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91740687926756857905791605 8600689493133455428667963)
            ·
              refine ⟨12901034239700183143001945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8600689493133455428667963 12901034239700183143001945)
              ·
                refine ⟨9675775679775137357251459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12901034239700183143001945 9675775679775137357251459)
                ·
                  refine ⟨14513663519662706035877189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9675775679775137357251459 14513663519662706035877189)
                  ·
                    refine ⟨2721311909936757381726973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14513663519662706035877189 2721311909936757381726973)
                    ·
                      refine ⟨1020491966226284018147615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2721311909936757381726973 1020491966226284018147615)
                      ·
                        rfl

theorem cell23_1987401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4, 3].length) (baseStart_1987401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987401 prefixEnd_1987401 := by exact prefixLift 1987401
  have htrace : WordTrace (prefixWord ++ tailWord_1987401) baseStart_1987401 baseEnd_1987401 := by
    simpa [prefixWord, tailWord_1987401, baseEnd_1987401] using wordTrace_append hprefix tailTrace_1987401
  have hstable : (prefixWord ++ tailWord_1987401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987401).length < 2 ^ (prefixWord ++ tailWord_1987401).sum := by decide
  have hdescent : baseEnd_1987401 < baseStart_1987401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987448 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 3, 1, 3]
def baseStart_1987448 : Nat := 118140960795 + 1987448 * 2 ^ 59
def prefixEnd_1987448 : Nat := 4983230072969 + 3 ^ 40 * 1987448 * 2
def baseEnd_1987448 : Nat := 1020516099817045334259899

theorem tailTrace_1987448 : CollatzResearch.WordTrace tailWord_1987448 prefixEnd_1987448 1020516099817045334259899 := by
  unfold tailWord_1987448
  simp only [CollatzResearch.WordTrace]
  refine ⟨36244091851911399970089499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48325455802548533293452665 36244091851911399970089499)
  ·
    refine ⟨54366137777867099955134249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36244091851911399970089499 54366137777867099955134249)
    ·
      refine ⟨40774603333400324966350687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54366137777867099955134249 40774603333400324966350687)
      ·
        refine ⟨61161905000100487449526031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40774603333400324966350687 61161905000100487449526031)
        ·
          refine ⟨91742857500150731174289047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61161905000100487449526031 91742857500150731174289047)
          ·
            refine ⟨137614286250226096761433571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91742857500150731174289047 137614286250226096761433571)
            ·
              refine ⟨206421429375339145142150357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137614286250226096761433571 206421429375339145142150357)
              ·
                refine ⟨4838002250984511214269149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206421429375339145142150357 4838002250984511214269149)
                ·
                  refine ⟨1814250844119191705350931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4838002250984511214269149 1814250844119191705350931)
                  ·
                    refine ⟨2721376266178787558026397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1814250844119191705350931 2721376266178787558026397)
                    ·
                      refine ⟨1020516099817045334259899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2721376266178787558026397 1020516099817045334259899)
                      ·
                        rfl

theorem cell23_1987448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_1987448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987448 prefixEnd_1987448 := by exact prefixLift 1987448
  have htrace : WordTrace (prefixWord ++ tailWord_1987448) baseStart_1987448 baseEnd_1987448 := by
    simpa [prefixWord, tailWord_1987448, baseEnd_1987448] using wordTrace_append hprefix tailTrace_1987448
  have hstable : (prefixWord ++ tailWord_1987448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987448).length < 2 ^ (prefixWord ++ tailWord_1987448).sum := by decide
  have hdescent : baseEnd_1987448 < baseStart_1987448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987468 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 1, 5]
def baseStart_1987468 : Nat := 118140960795 + 1987468 * 2 ^ 59
def prefixEnd_1987468 : Nat := 4983230072969 + 3 ^ 40 * 1987468 * 2
def baseEnd_1987468 : Nat := 340175456476711752003269

theorem tailTrace_1987468 : CollatzResearch.WordTrace tailWord_1987468 prefixEnd_1987468 340175456476711752003269 := by
  unfold tailWord_1987468
  simp only [CollatzResearch.WordTrace]
  refine ⟨36244456581875171677953529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48325942109166895570604705 36244456581875171677953529)
  ·
    refine ⟨27183342436406378758465147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36244456581875171677953529 27183342436406378758465147)
    ·
      refine ⟨40775013654609568137697721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27183342436406378758465147 40775013654609568137697721)
      ·
        refine ⟨30581260240957176103273291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40775013654609568137697721 30581260240957176103273291)
        ·
          refine ⟨45871890361435764154909937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30581260240957176103273291 45871890361435764154909937)
          ·
            refine ⟨34403917771076823116182453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45871890361435764154909937 34403917771076823116182453)
            ·
              refine ⟨3225367291038452167142105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34403917771076823116182453 3225367291038452167142105)
              ·
                refine ⟨2419025468278839125356579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225367291038452167142105 2419025468278839125356579)
                ·
                  refine ⟨3628538202418258688034869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419025468278839125356579 3628538202418258688034869)
                  ·
                    refine ⟨340175456476711752003269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3628538202418258688034869 340175456476711752003269)
                    ·
                      rfl

theorem cell23_1987468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_1987468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987468 prefixEnd_1987468 := by exact prefixLift 1987468
  have htrace : WordTrace (prefixWord ++ tailWord_1987468) baseStart_1987468 baseEnd_1987468 := by
    simpa [prefixWord, tailWord_1987468, baseEnd_1987468] using wordTrace_append hprefix tailTrace_1987468
  have hstable : (prefixWord ++ tailWord_1987468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987468).length < 2 ^ (prefixWord ++ tailWord_1987468).sum := by decide
  have hdescent : baseEnd_1987468 < baseStart_1987468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987485 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1987485 : Nat := 118140960795 + 1987485 * 2 ^ 59
def prefixEnd_1987485 : Nat := 4983230072969 + 3 ^ 40 * 1987485 * 2
def baseEnd_1987485 : Nat := 340178366200420563165743

theorem tailTrace_1987485 : CollatzResearch.WordTrace tailWord_1987485 prefixEnd_1987485 340178366200420563165743 := by
  unfold tailWord_1987485
  simp only [CollatzResearch.WordTrace]
  refine ⟨72489533204688755259275909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48326355469792503506183939 72489533204688755259275909)
  ·
    refine ⟨13591787475879141611114233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72489533204688755259275909 13591787475879141611114233)
    ·
      refine ⟨10193840606909356208335675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13591787475879141611114233 10193840606909356208335675)
      ·
        refine ⟨15290760910364034312503513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10193840606909356208335675 15290760910364034312503513)
        ·
          refine ⟨11468070682773025734377635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15290760910364034312503513 11468070682773025734377635)
          ·
            refine ⟨17202106024159538601566453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468070682773025734377635 17202106024159538601566453)
            ·
              refine ⟨1612697439764956743896855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17202106024159538601566453 1612697439764956743896855)
              ·
                refine ⟨2419046159647435115845283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612697439764956743896855 2419046159647435115845283)
                ·
                  refine ⟨3628569239471152673767925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419046159647435115845283 3628569239471152673767925)
                  ·
                    refine ⟨340178366200420563165743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3628569239471152673767925 340178366200420563165743)
                    ·
                      rfl

theorem cell23_1987485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1987485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987485 prefixEnd_1987485 := by exact prefixLift 1987485
  have htrace : WordTrace (prefixWord ++ tailWord_1987485) baseStart_1987485 baseEnd_1987485 := by
    simpa [prefixWord, tailWord_1987485, baseEnd_1987485] using wordTrace_append hprefix tailTrace_1987485
  have hstable : (prefixWord ++ tailWord_1987485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987485).length < 2 ^ (prefixWord ++ tailWord_1987485).sum := by decide
  have hdescent : baseEnd_1987485 < baseStart_1987485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987488 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 4]
def baseStart_1987488 : Nat := 118140960795 + 1987488 * 2 ^ 59
def prefixEnd_1987488 : Nat := 4983230072969 + 3 ^ 40 * 1987488 * 2
def baseEnd_1987488 : Nat := 1020536639043225177759715

theorem tailTrace_1987488 : CollatzResearch.WordTrace tailWord_1987488 prefixEnd_1987488 1020536639043225177759715 := by
  unfold tailWord_1987488
  simp only [CollatzResearch.WordTrace]
  refine ⟨36244821311838943385817559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48326428415785257847756745 36244821311838943385817559)
  ·
    refine ⟨54367231967758415078726339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36244821311838943385817559 54367231967758415078726339)
    ·
      refine ⟨81550847951637622618089509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54367231967758415078726339 81550847951637622618089509)
      ·
        refine ⟨15290783990932054240891783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81550847951637622618089509 15290783990932054240891783)
        ·
          refine ⟨22936175986398081361337675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15290783990932054240891783 22936175986398081361337675)
          ·
            refine ⟨34404263979597122042006513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22936175986398081361337675 34404263979597122042006513)
            ·
              refine ⟨25803197984697841531504885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34404263979597122042006513 25803197984697841531504885)
              ·
                refine ⟨2419049811065422643578583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25803197984697841531504885 2419049811065422643578583)
                ·
                  refine ⟨3628574716598133965367875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419049811065422643578583 3628574716598133965367875)
                  ·
                    refine ⟨5442862074897200948051813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3628574716598133965367875 5442862074897200948051813)
                    ·
                      refine ⟨1020536639043225177759715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5442862074897200948051813 1020536639043225177759715)
                      ·
                        rfl

theorem cell23_1987488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_1987488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987488 prefixEnd_1987488 := by exact prefixLift 1987488
  have htrace : WordTrace (prefixWord ++ tailWord_1987488) baseStart_1987488 baseEnd_1987488 := by
    simpa [prefixWord, tailWord_1987488, baseEnd_1987488] using wordTrace_append hprefix tailTrace_1987488
  have hstable : (prefixWord ++ tailWord_1987488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987488).length < 2 ^ (prefixWord ++ tailWord_1987488).sum := by decide
  have hdescent : baseEnd_1987488 < baseStart_1987488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987511 : List Nat := [1, 1, 3, 1, 3, 1, 5, 8]
def baseStart_1987511 : Nat := 118140960795 + 1987511 * 2 ^ 59
def prefixEnd_1987511 : Nat := 4983230072969 + 3 ^ 40 * 1987511 * 2
def baseEnd_1987511 : Nat := 37798090707343651398967

theorem tailTrace_1987511 : CollatzResearch.WordTrace tailWord_1987511 prefixEnd_1987511 37798090707343651398967 := by
  unfold tailWord_1987511
  simp only [CollatzResearch.WordTrace]
  refine ⟨72490481502594561699722387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48326987668396374466481591 72490481502594561699722387)
  ·
    refine ⟨108735722253891842549583581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72490481502594561699722387 108735722253891842549583581)
    ·
      refine ⟨40775895845209440956093843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108735722253891842549583581 40775895845209440956093843)
      ·
        refine ⟨61163843767814161434140765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40775895845209440956093843 61163843767814161434140765)
        ·
          refine ⟨22936441412930310537802787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61163843767814161434140765 22936441412930310537802787)
          ·
            refine ⟨34404662119395465806704181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22936441412930310537802787 34404662119395465806704181)
            ·
              refine ⟨3225437073693324919378517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34404662119395465806704181 3225437073693324919378517)
              ·
                refine ⟨37798090707343651398967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3225437073693324919378517 37798090707343651398967)
                ·
                  rfl

theorem cell23_1987511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 8].length) (baseStart_1987511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987511 prefixEnd_1987511 := by exact prefixLift 1987511
  have htrace : WordTrace (prefixWord ++ tailWord_1987511) baseStart_1987511 baseEnd_1987511 := by
    simpa [prefixWord, tailWord_1987511, baseEnd_1987511] using wordTrace_append hprefix tailTrace_1987511
  have hstable : (prefixWord ++ tailWord_1987511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987511).length < 2 ^ (prefixWord ++ tailWord_1987511).sum := by decide
  have hdescent : baseEnd_1987511 < baseStart_1987511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987555 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1987555 : Nat := 118140960795 + 1987555 * 2 ^ 59
def prefixEnd_1987555 : Nat := 4983230072969 + 3 ^ 40 * 1987555 * 2
def baseEnd_1987555 : Nat := 1020571042247076415621907

theorem tailTrace_1987555 : CollatzResearch.WordTrace tailWord_1987555 prefixEnd_1987555 1020571042247076415621907 := by
  unfold tailWord_1987555
  simp only [CollatzResearch.WordTrace]
  refine ⟨72492086314435157214324119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48328057542956771476216079 72492086314435157214324119)
  ·
    refine ⟨108738129471652735821486179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72492086314435157214324119 108738129471652735821486179)
    ·
      refine ⟨163107194207479103732229269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108738129471652735821486179 163107194207479103732229269)
      ·
        refine ⟨7645649728475582987448247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163107194207479103732229269 7645649728475582987448247)
        ·
          refine ⟨11468474592713374481172371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7645649728475582987448247 11468474592713374481172371)
          ·
            refine ⟨17202711889070061721758557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468474592713374481172371 17202711889070061721758557)
            ·
              refine ⟨6451016958401273145659459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17202711889070061721758557 6451016958401273145659459)
              ·
                refine ⟨9676525437601909718489189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6451016958401273145659459 9676525437601909718489189)
                ·
                  refine ⟨1814348519550358072216723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9676525437601909718489189 1814348519550358072216723)
                  ·
                    refine ⟨2721522779325537108325085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1814348519550358072216723 2721522779325537108325085)
                    ·
                      refine ⟨1020571042247076415621907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2721522779325537108325085 1020571042247076415621907)
                      ·
                        rfl

theorem cell23_1987555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1987555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987555 prefixEnd_1987555 := by exact prefixLift 1987555
  have htrace : WordTrace (prefixWord ++ tailWord_1987555) baseStart_1987555 baseEnd_1987555 := by
    simpa [prefixWord, tailWord_1987555, baseEnd_1987555] using wordTrace_append hprefix tailTrace_1987555
  have hstable : (prefixWord ++ tailWord_1987555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987555).length < 2 ^ (prefixWord ++ tailWord_1987555).sum := by decide
  have hdescent : baseEnd_1987555 < baseStart_1987555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987598 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1987598 : Nat := 118140960795 + 1987598 * 2 ^ 59
def prefixEnd_1987598 : Nat := 4983230072969 + 3 ^ 40 * 1987598 * 2
def baseEnd_1987598 : Nat := 1020593121915219747384209

theorem tailTrace_1987598 : CollatzResearch.WordTrace tailWord_1987598 prefixEnd_1987598 1020593121915219747384209 := by
  unfold tailWord_1987598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9061706831659921944767431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48329103102186250372092965 9061706831659921944767431)
  ·
    refine ⟨13592560247489882917151147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9061706831659921944767431 13592560247489882917151147)
    ·
      refine ⟨20388840371234824375726721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13592560247489882917151147 20388840371234824375726721)
      ·
        refine ⟨15291630278426118281795041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20388840371234824375726721 15291630278426118281795041)
        ·
          refine ⟨11468722708819588711346281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15291630278426118281795041 11468722708819588711346281)
          ·
            refine ⟨8601542031614691533509711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11468722708819588711346281 8601542031614691533509711)
            ·
              refine ⟨12902313047422037300264567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601542031614691533509711 12902313047422037300264567)
              ·
                refine ⟨19353469571133055950396851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12902313047422037300264567 19353469571133055950396851)
                ·
                  refine ⟨29030204356699583925595277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19353469571133055950396851 29030204356699583925595277)
                  ·
                    refine ⟨10886326633762343972098229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29030204356699583925595277 10886326633762343972098229)
                    ·
                      refine ⟨1020593121915219747384209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10886326633762343972098229 1020593121915219747384209)
                      ·
                        rfl

theorem cell23_1987598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1987598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987598 prefixEnd_1987598 := by exact prefixLift 1987598
  have htrace : WordTrace (prefixWord ++ tailWord_1987598) baseStart_1987598 baseEnd_1987598 := by
    simpa [prefixWord, tailWord_1987598, baseEnd_1987598] using wordTrace_append hprefix tailTrace_1987598
  have hstable : (prefixWord ++ tailWord_1987598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987598).length < 2 ^ (prefixWord ++ tailWord_1987598).sum := by decide
  have hdescent : baseEnd_1987598 < baseStart_1987598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987601 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 9]
def baseStart_1987601 : Nat := 118140960795 + 1987601 * 2 ^ 59
def prefixEnd_1987601 : Nat := 4983230072969 + 3 ^ 40 * 1987601 * 2
def baseEnd_1987601 : Nat := 113399406928575915071855

theorem tailTrace_1987601 : CollatzResearch.WordTrace tailWord_1987601 prefixEnd_1987601 113399406928575915071855 := by
  unfold tailWord_1987601
  simp only [CollatzResearch.WordTrace]
  refine ⟨72493764072268507070498657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48329176048179004713665771 72493764072268507070498657)
  ·
    refine ⟨54370323054201380302873993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72493764072268507070498657 54370323054201380302873993)
    ·
      refine ⟨40777742290651035227155495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54370323054201380302873993 40777742290651035227155495)
      ·
        refine ⟨61166613435976552840733243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40777742290651035227155495 61166613435976552840733243)
        ·
          refine ⟨91749920153964829261099865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61166613435976552840733243 91749920153964829261099865)
          ·
            refine ⟨68812440115473621945824899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91749920153964829261099865 68812440115473621945824899)
            ·
              refine ⟨103218660173210432918737349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68812440115473621945824899 103218660173210432918737349)
              ·
                refine ⟨19353498782476956172263253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103218660173210432918737349 19353498782476956172263253)
                ·
                  refine ⟨113399406928575915071855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19353498782476956172263253 113399406928575915071855)
                  ·
                    rfl

theorem cell23_1987601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 9].length) (baseStart_1987601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987601 prefixEnd_1987601 := by exact prefixLift 1987601
  have htrace : WordTrace (prefixWord ++ tailWord_1987601) baseStart_1987601 baseEnd_1987601 := by
    simpa [prefixWord, tailWord_1987601, baseEnd_1987601] using wordTrace_append hprefix tailTrace_1987601
  have hstable : (prefixWord ++ tailWord_1987601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987601).length < 2 ^ (prefixWord ++ tailWord_1987601).sum := by decide
  have hdescent : baseEnd_1987601 < baseStart_1987601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987628 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 3]
def baseStart_1987628 : Nat := 118140960795 + 1987628 * 2 ^ 59
def prefixEnd_1987628 : Nat := 4983230072969 + 3 ^ 40 * 1987628 * 2
def baseEnd_1987628 : Nat := 1020608526334854630009071

theorem tailTrace_1987628 : CollatzResearch.WordTrace tailWord_1987628 prefixEnd_1987628 1020608526334854630009071 := by
  unfold tailWord_1987628
  simp only [CollatzResearch.WordTrace]
  refine ⟨36247374421585345340865769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48329832562113793787821025 36247374421585345340865769)
  ·
    refine ⟨27185530816189009005649327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36247374421585345340865769 27185530816189009005649327)
    ·
      refine ⟨40778296224283513508473991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27185530816189009005649327 40778296224283513508473991)
      ·
        refine ⟨61167444336425270262710987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40778296224283513508473991 61167444336425270262710987)
        ·
          refine ⟨91751166504637905394066481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61167444336425270262710987 91751166504637905394066481)
          ·
            refine ⟨68813374878478429045549861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91751166504637905394066481 68813374878478429045549861)
            ·
              refine ⟨12902507789714705446040599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68813374878478429045549861 12902507789714705446040599)
              ·
                refine ⟨19353761684572058169060899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12902507789714705446040599 19353761684572058169060899)
                ·
                  refine ⟨29030642526858087253591349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19353761684572058169060899 29030642526858087253591349)
                  ·
                    refine ⟨2721622736892945680024189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29030642526858087253591349 2721622736892945680024189)
                    ·
                      refine ⟨1020608526334854630009071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2721622736892945680024189 1020608526334854630009071)
                      ·
                        rfl

theorem cell23_1987628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_1987628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987628 prefixEnd_1987628 := by exact prefixLift 1987628
  have htrace : WordTrace (prefixWord ++ tailWord_1987628) baseStart_1987628 baseEnd_1987628 := by
    simpa [prefixWord, tailWord_1987628, baseEnd_1987628] using wordTrace_append hprefix tailTrace_1987628
  have hstable : (prefixWord ++ tailWord_1987628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987628).length < 2 ^ (prefixWord ++ tailWord_1987628).sum := by decide
  have hdescent : baseEnd_1987628 < baseStart_1987628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987658 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_1987658 : Nat := 118140960795 + 1987658 * 2 ^ 59
def prefixEnd_1987658 : Nat := 4983230072969 + 3 ^ 40 * 1987658 * 2
def baseEnd_1987658 : Nat := 1020623930754489512633933

theorem tailTrace_1987658 : CollatzResearch.WordTrace tailWord_1987658 prefixEnd_1987658 1020623930754489512633933 := by
  unfold tailWord_1987658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18123960758265501451330907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48330562022041337203549085 18123960758265501451330907)
  ·
    refine ⟨27185941137398252176996361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18123960758265501451330907 27185941137398252176996361)
    ·
      refine ⟨20389455853048689132747271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27185941137398252176996361 20389455853048689132747271)
      ·
        refine ⟨30584183779573033699120907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20389455853048689132747271 30584183779573033699120907)
        ·
          refine ⟨45876275669359550548681361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30584183779573033699120907 45876275669359550548681361)
          ·
            refine ⟨34407206752019662911511021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45876275669359550548681361 34407206752019662911511021)
            ·
              refine ⟨12902702532007373591816633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34407206752019662911511021 12902702532007373591816633)
              ·
                refine ⟨9677026899005530193862475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12902702532007373591816633 9677026899005530193862475)
                ·
                  refine ⟨14515540348508295290793713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9677026899005530193862475 14515540348508295290793713)
                  ·
                    refine ⟨10886655261381221468095285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14515540348508295290793713 10886655261381221468095285)
                    ·
                      refine ⟨1020623930754489512633933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10886655261381221468095285 1020623930754489512633933)
                      ·
                        rfl

theorem cell23_1987658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_1987658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987658 prefixEnd_1987658 := by exact prefixLift 1987658
  have htrace : WordTrace (prefixWord ++ tailWord_1987658) baseStart_1987658 baseEnd_1987658 := by
    simpa [prefixWord, tailWord_1987658, baseEnd_1987658] using wordTrace_append hprefix tailTrace_1987658
  have hstable : (prefixWord ++ tailWord_1987658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987658).length < 2 ^ (prefixWord ++ tailWord_1987658).sum := by decide
  have hdescent : baseEnd_1987658 < baseStart_1987658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987695 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 3, 4]
def baseStart_1987695 : Nat := 118140960795 + 1987695 * 2 ^ 59
def prefixEnd_1987695 : Nat := 4983230072969 + 3 ^ 40 * 1987695 * 2
def baseEnd_1987695 : Nat := 340214309846235289290421

theorem tailTrace_1987695 : CollatzResearch.WordTrace tailWord_1987695 prefixEnd_1987695 340214309846235289290421 := by
  unfold tailWord_1987695
  simp only [CollatzResearch.WordTrace]
  refine ⟨72497192533927961124420539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48331461689285307416280359 72497192533927961124420539)
  ·
    refine ⟨108745788800891941686630809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72497192533927961124420539 108745788800891941686630809)
    ·
      refine ⟨81559341600668956264973107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108745788800891941686630809 81559341600668956264973107)
      ·
        refine ⟨122339012401003434397459661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81559341600668956264973107 122339012401003434397459661)
        ·
          refine ⟨45877129650376287899047373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122339012401003434397459661 45877129650376287899047373)
          ·
            refine ⟨17203923618891107962142765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45877129650376287899047373 17203923618891107962142765)
            ·
              refine ⟨6451471357084165485803537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17203923618891107962142765 6451471357084165485803537)
              ·
                refine ⟨4838603517813124114352653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6451471357084165485803537 4838603517813124114352653)
                ·
                  refine ⟨1814476319179921542882245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4838603517813124114352653 1814476319179921542882245)
                  ·
                    refine ⟨340214309846235289290421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1814476319179921542882245 340214309846235289290421)
                    ·
                      rfl

theorem cell23_1987695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 4].length) (baseStart_1987695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987695 prefixEnd_1987695 := by exact prefixLift 1987695
  have htrace : WordTrace (prefixWord ++ tailWord_1987695) baseStart_1987695 baseEnd_1987695 := by
    simpa [prefixWord, tailWord_1987695, baseEnd_1987695] using wordTrace_append hprefix tailTrace_1987695
  have hstable : (prefixWord ++ tailWord_1987695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987695).length < 2 ^ (prefixWord ++ tailWord_1987695).sum := by decide
  have hdescent : baseEnd_1987695 < baseStart_1987695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987702 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_1987702 : Nat := 118140960795 + 1987702 * 2 ^ 59
def prefixEnd_1987702 : Nat := 4983230072969 + 3 ^ 40 * 1987702 * 2
def baseEnd_1987702 : Nat := 1020646523903287340483731

theorem tailTrace_1987702 : CollatzResearch.WordTrace tailWord_1987702 prefixEnd_1987702 1020646523903287340483731 := by
  unfold tailWord_1987702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4531090490306412582495335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48331631896601734213283573 4531090490306412582495335)
  ·
    refine ⟨6796635735459618873743003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4531090490306412582495335 6796635735459618873743003)
    ·
      refine ⟨10194953603189428310614505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6796635735459618873743003 10194953603189428310614505)
      ·
        refine ⟨7646215202392071232960879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10194953603189428310614505 7646215202392071232960879)
        ·
          refine ⟨11469322803588106849441319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7646215202392071232960879 11469322803588106849441319)
          ·
            refine ⟨17203984205382160274161979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11469322803588106849441319 17203984205382160274161979)
            ·
              refine ⟨25805976308073240411242969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17203984205382160274161979 25805976308073240411242969)
              ·
                refine ⟨19354482231054930308432227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25805976308073240411242969 19354482231054930308432227)
                ·
                  refine ⟨29031723346582395462648341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19354482231054930308432227 29031723346582395462648341)
                  ·
                    refine ⟨1360862031871049787311641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29031723346582395462648341 1360862031871049787311641)
                    ·
                      refine ⟨1020646523903287340483731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1360862031871049787311641 1020646523903287340483731)
                      ·
                        rfl

theorem cell23_1987702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_1987702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987702 prefixEnd_1987702 := by exact prefixLift 1987702
  have htrace : WordTrace (prefixWord ++ tailWord_1987702) baseStart_1987702 baseEnd_1987702 := by
    simpa [prefixWord, tailWord_1987702, baseEnd_1987702] using wordTrace_append hprefix tailTrace_1987702
  have hstable : (prefixWord ++ tailWord_1987702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987702).length < 2 ^ (prefixWord ++ tailWord_1987702).sum := by decide
  have hdescent : baseEnd_1987702 < baseStart_1987702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987708 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 8]
def baseStart_1987708 : Nat := 118140960795 + 1987708 * 2 ^ 59
def prefixEnd_1987708 : Nat := 4983230072969 + 3 ^ 40 * 1987708 * 2
def baseEnd_1987708 : Nat := 113405511643023813000967

theorem tailTrace_1987708 : CollatzResearch.WordTrace tailWord_1987708 prefixEnd_1987708 113405511643023813000967 := by
  unfold tailWord_1987708
  simp only [CollatzResearch.WordTrace]
  refine ⟨36248833341440432172321889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48331777788587242896429185 36248833341440432172321889)
  ·
    refine ⟨27186625006080324129241417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36248833341440432172321889 27186625006080324129241417)
    ·
      refine ⟨20389968754560243096931063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27186625006080324129241417 20389968754560243096931063)
      ·
        refine ⟨30584953131840364645396595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20389968754560243096931063 30584953131840364645396595)
        ·
          refine ⟨45877429697760546968094893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30584953131840364645396595 45877429697760546968094893)
          ·
            refine ⟨17204036136660205113035585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45877429697760546968094893 17204036136660205113035585)
            ·
              refine ⟨12903027102495153834776689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17204036136660205113035585 12903027102495153834776689)
              ·
                refine ⟨9677270326871365376082517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12903027102495153834776689 9677270326871365376082517)
                ·
                  refine ⟨113405511643023813000967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9677270326871365376082517 113405511643023813000967)
                  ·
                    rfl

theorem cell23_1987708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_1987708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987708 prefixEnd_1987708 := by exact prefixLift 1987708
  have htrace : WordTrace (prefixWord ++ tailWord_1987708) baseStart_1987708 baseEnd_1987708 := by
    simpa [prefixWord, tailWord_1987708, baseEnd_1987708] using wordTrace_append hprefix tailTrace_1987708
  have hstable : (prefixWord ++ tailWord_1987708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987708).length < 2 ^ (prefixWord ++ tailWord_1987708).sum := by decide
  have hdescent : baseEnd_1987708 < baseStart_1987708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987712 : List Nat := [2, 1, 1, 2, 1, 3, 3, 5, 1, 4]
def baseStart_1987712 : Nat := 118140960795 + 1987712 * 2 ^ 59
def prefixEnd_1987712 : Nat := 4983230072969 + 3 ^ 40 * 1987712 * 2
def baseEnd_1987712 : Nat := 340217219569944100452895

theorem tailTrace_1987712 : CollatzResearch.WordTrace tailWord_1987712 prefixEnd_1987712 340217219569944100452895 := by
  unfold tailWord_1987712
  simp only [CollatzResearch.WordTrace]
  refine ⟨36248906287433186513894695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48331875049910915351859593 36248906287433186513894695)
  ·
    refine ⟨54373359431149779770842043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36248906287433186513894695 54373359431149779770842043)
    ·
      refine ⟨81560039146724669656263065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54373359431149779770842043 81560039146724669656263065)
      ·
        refine ⟨61170029360043502242197299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81560039146724669656263065 61170029360043502242197299)
        ·
          refine ⟨91755044040065253363295949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61170029360043502242197299 91755044040065253363295949)
          ·
            refine ⟨34408141515024470011235981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91755044040065253363295949 34408141515024470011235981)
            ·
              refine ⟨12903053068134176254213493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34408141515024470011235981 12903053068134176254213493)
              ·
                refine ⟨1209661225137579023832515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12903053068134176254213493 1209661225137579023832515)
                ·
                  refine ⟨1814491837706368535748773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209661225137579023832515 1814491837706368535748773)
                  ·
                    refine ⟨340217219569944100452895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1814491837706368535748773 340217219569944100452895)
                    ·
                      rfl

theorem cell23_1987712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 1, 4].length) (baseStart_1987712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987712 prefixEnd_1987712 := by exact prefixLift 1987712
  have htrace : WordTrace (prefixWord ++ tailWord_1987712) baseStart_1987712 baseEnd_1987712 := by
    simpa [prefixWord, tailWord_1987712, baseEnd_1987712] using wordTrace_append hprefix tailTrace_1987712
  have hstable : (prefixWord ++ tailWord_1987712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987712).length < 2 ^ (prefixWord ++ tailWord_1987712).sum := by decide
  have hdescent : baseEnd_1987712 < baseStart_1987712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987762 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2]
def baseStart_1987762 : Nat := 118140960795 + 1987762 * 2 ^ 59
def prefixEnd_1987762 : Nat := 4983230072969 + 3 ^ 40 * 1987762 * 2
def baseEnd_1987762 : Nat := 1020677332742557105733455

theorem tailTrace_1987762 : CollatzResearch.WordTrace tailWord_1987762 prefixEnd_1987762 1020677332742557105733455 := by
  unfold tailWord_1987762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18124909056171307891777385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48333090816456821044739693 18124909056171307891777385)
  ·
    refine ⟨13593681792128480918833039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18124909056171307891777385 13593681792128480918833039)
    ·
      refine ⟨20390522688192721378249559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13593681792128480918833039 20390522688192721378249559)
      ·
        refine ⟨30585784032289082067374339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20390522688192721378249559 30585784032289082067374339)
        ·
          refine ⟨45878676048433623101061509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30585784032289082067374339 45878676048433623101061509)
          ·
            refine ⟨8602251759081304331449033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45878676048433623101061509 8602251759081304331449033)
            ·
              refine ⟨6451688819310978248586775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8602251759081304331449033 6451688819310978248586775)
              ·
                refine ⟨9677533228966467372880163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6451688819310978248586775 9677533228966467372880163)
                ·
                  refine ⟨14516299843449701059320245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9677533228966467372880163 14516299843449701059320245)
                  ·
                    refine ⟨1360903110323409474311273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14516299843449701059320245 1360903110323409474311273)
                    ·
                      refine ⟨1020677332742557105733455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1360903110323409474311273 1020677332742557105733455)
                      ·
                        rfl

theorem cell23_1987762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_1987762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987762 prefixEnd_1987762 := by exact prefixLift 1987762
  have htrace : WordTrace (prefixWord ++ tailWord_1987762) baseStart_1987762 baseEnd_1987762 := by
    simpa [prefixWord, tailWord_1987762, baseEnd_1987762] using wordTrace_append hprefix tailTrace_1987762
  have hstable : (prefixWord ++ tailWord_1987762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987762).length < 2 ^ (prefixWord ++ tailWord_1987762).sum := by decide
  have hdescent : baseEnd_1987762 < baseStart_1987762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987772 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 1, 5]
def baseStart_1987772 : Nat := 118140960795 + 1987772 * 2 ^ 59
def prefixEnd_1987772 : Nat := 4983230072969 + 3 ^ 40 * 1987772 * 2
def baseEnd_1987772 : Nat := 340227489183034022202803

theorem tailTrace_1987772 : CollatzResearch.WordTrace tailWord_1987772 prefixEnd_1987772 340227489183034022202803 := by
  unfold tailWord_1987772
  simp only [CollatzResearch.WordTrace]
  refine ⟨36250000477324501637486785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48333333969766002183315713 36250000477324501637486785)
  ·
    refine ⟨27187500357993376228115089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36250000477324501637486785 27187500357993376228115089)
    ·
      refine ⟨20390625268495032171086317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27187500357993376228115089 20390625268495032171086317)
      ·
        refine ⟨7646484475685637064157369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20390625268495032171086317 7646484475685637064157369)
        ·
          refine ⟨5734863356764227798118027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7646484475685637064157369 5734863356764227798118027)
          ·
            refine ⟨8602295035146341697177041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734863356764227798118027 8602295035146341697177041)
            ·
              refine ⟨6451721276359756272882781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8602295035146341697177041 6451721276359756272882781)
              ·
                refine ⟨2419395478634908602331043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6451721276359756272882781 2419395478634908602331043)
                ·
                  refine ⟨3629093217952362903496565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419395478634908602331043 3629093217952362903496565)
                  ·
                    refine ⟨340227489183034022202803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3629093217952362903496565 340227489183034022202803)
                    ·
                      rfl

theorem cell23_1987772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_1987772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987772 prefixEnd_1987772 := by exact prefixLift 1987772
  have htrace : WordTrace (prefixWord ++ tailWord_1987772) baseStart_1987772 baseEnd_1987772 := by
    simpa [prefixWord, tailWord_1987772, baseEnd_1987772] using wordTrace_append hprefix tailTrace_1987772
  have hstable : (prefixWord ++ tailWord_1987772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987772).length < 2 ^ (prefixWord ++ tailWord_1987772).sum := by decide
  have hdescent : baseEnd_1987772 < baseStart_1987772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987795 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 3]
def baseStart_1987795 : Nat := 118140960795 + 1987795 * 2 ^ 59
def prefixEnd_1987795 : Nat := 4983230072969 + 3 ^ 40 * 1987795 * 2
def baseEnd_1987795 : Nat := 1020694277604155476620803

theorem tailTrace_1987795 : CollatzResearch.WordTrace tailWord_1987795 prefixEnd_1987795 1020694277604155476620803 := by
  unfold tailWord_1987795
  simp only [CollatzResearch.WordTrace]
  refine ⟨72500839833565678203060839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48333893222377118802040559 72500839833565678203060839)
  ·
    refine ⟨108751259750348517304591259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72500839833565678203060839 108751259750348517304591259)
    ·
      refine ⟨163126889625522775956886889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108751259750348517304591259 163126889625522775956886889)
      ·
        refine ⟨122345167219142081967665167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163126889625522775956886889 122345167219142081967665167)
        ·
          refine ⟨183517750828713122951497751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122345167219142081967665167 183517750828713122951497751)
          ·
            refine ⟨275276626243069684427246627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183517750828713122951497751 275276626243069684427246627)
            ·
              refine ⟨412914939364604526640869941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275276626243069684427246627 412914939364604526640869941)
              ·
                refine ⟨38710775565431674372581557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 412914939364604526640869941 38710775565431674372581557)
                ·
                  refine ⟨3629135209259219472429521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38710775565431674372581557 3629135209259219472429521)
                  ·
                    refine ⟨2721851406944414604322141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3629135209259219472429521 2721851406944414604322141)
                    ·
                      refine ⟨1020694277604155476620803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2721851406944414604322141 1020694277604155476620803)
                      ·
                        rfl

theorem cell23_1987795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 3].length) (baseStart_1987795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987795 prefixEnd_1987795 := by exact prefixLift 1987795
  have htrace : WordTrace (prefixWord ++ tailWord_1987795) baseStart_1987795 baseEnd_1987795 := by
    simpa [prefixWord, tailWord_1987795, baseEnd_1987795] using wordTrace_append hprefix tailTrace_1987795
  have hstable : (prefixWord ++ tailWord_1987795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987795).length < 2 ^ (prefixWord ++ tailWord_1987795).sum := by decide
  have hdescent : baseEnd_1987795 < baseStart_1987795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987809 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_1987809 : Nat := 118140960795 + 1987809 * 2 ^ 59
def prefixEnd_1987809 : Nat := 4983230072969 + 3 ^ 40 * 1987809 * 2
def baseEnd_1987809 : Nat := 1020701466333318421845739

theorem tailTrace_1987809 : CollatzResearch.WordTrace tailWord_1987809 prefixEnd_1987809 1020701466333318421845739 := by
  unfold tailWord_1987809
  simp only [CollatzResearch.WordTrace]
  refine ⟨72501350455514958594070481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48334233637009972396046987 72501350455514958594070481)
  ·
    refine ⟨54376012841636218945552861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72501350455514958594070481 54376012841636218945552861)
    ·
      refine ⟨20391004815613582104582323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54376012841636218945552861 20391004815613582104582323)
      ·
        refine ⟨30586507223420373156873485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20391004815613582104582323 30586507223420373156873485)
        ·
          refine ⟨11469940208782639933827557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30586507223420373156873485 11469940208782639933827557)
          ·
            refine ⟨2150613789146744987592667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11469940208782639933827557 2150613789146744987592667)
            ·
              refine ⟨3225920683720117481389001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150613789146744987592667 3225920683720117481389001)
              ·
                refine ⟨2419440512790088111041751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225920683720117481389001 2419440512790088111041751)
                ·
                  refine ⟨3629160769185132166562627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419440512790088111041751 3629160769185132166562627)
                  ·
                    refine ⟨5443741153777698249843941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3629160769185132166562627 5443741153777698249843941)
                    ·
                      refine ⟨1020701466333318421845739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5443741153777698249843941 1020701466333318421845739)
                      ·
                        rfl

theorem cell23_1987809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_1987809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987809 prefixEnd_1987809 := by exact prefixLift 1987809
  have htrace : WordTrace (prefixWord ++ tailWord_1987809) baseStart_1987809 baseEnd_1987809 := by
    simpa [prefixWord, tailWord_1987809, baseEnd_1987809] using wordTrace_append hprefix tailTrace_1987809
  have hstable : (prefixWord ++ tailWord_1987809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987809).length < 2 ^ (prefixWord ++ tailWord_1987809).sum := by decide
  have hdescent : baseEnd_1987809 < baseStart_1987809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987826 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 1, 1, 4]
def baseStart_1987826 : Nat := 118140960795 + 1987826 * 2 ^ 59
def prefixEnd_1987826 : Nat := 4983230072969 + 3 ^ 40 * 1987826 * 2
def baseEnd_1987826 : Nat := 1020710195504444855333161

theorem tailTrace_1987826 : CollatzResearch.WordTrace tailWord_1987826 prefixEnd_1987826 1020710195504444855333161 := by
  unfold tailWord_1987826
  simp only [CollatzResearch.WordTrace]
  refine ⟨18125492624113342624359833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48334646997635580331626221 18125492624113342624359833)
  ·
    refine ⟨13594119468085006968269875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18125492624113342624359833 13594119468085006968269875)
    ·
      refine ⟨20391179202127510452404813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13594119468085006968269875 20391179202127510452404813)
      ·
        refine ⟨7646692200797816419651805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20391179202127510452404813 7646692200797816419651805)
        ·
          refine ⟨2867509575299181157369427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7646692200797816419651805 2867509575299181157369427)
          ·
            refine ⟨4301264362948771736054141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867509575299181157369427 4301264362948771736054141)
            ·
              refine ⟨1612974136105789401020303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4301264362948771736054141 1612974136105789401020303)
              ·
                refine ⟨2419461204158684101530455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612974136105789401020303 2419461204158684101530455)
                ·
                  refine ⟨3629191806238026152295683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419461204158684101530455 3629191806238026152295683)
                  ·
                    refine ⟨5443787709357039228443525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3629191806238026152295683 5443787709357039228443525)
                    ·
                      refine ⟨1020710195504444855333161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5443787709357039228443525 1020710195504444855333161)
                      ·
                        rfl

theorem cell23_1987826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_1987826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987826 prefixEnd_1987826 := by exact prefixLift 1987826
  have htrace : WordTrace (prefixWord ++ tailWord_1987826) baseStart_1987826 baseEnd_1987826 := by
    simpa [prefixWord, tailWord_1987826, baseEnd_1987826] using wordTrace_append hprefix tailTrace_1987826
  have hstable : (prefixWord ++ tailWord_1987826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987826).length < 2 ^ (prefixWord ++ tailWord_1987826).sum := by decide
  have hdescent : baseEnd_1987826 < baseStart_1987826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987843 : List Nat := [1, 1, 1, 3, 2, 4, 4, 2, 1, 2, 2]
def baseStart_1987843 : Nat := 118140960795 + 1987843 * 2 ^ 59
def prefixEnd_1987843 : Nat := 4983230072969 + 3 ^ 40 * 1987843 * 2
def baseEnd_1987843 : Nat := 1020718924675571288820583

theorem tailTrace_1987843 : CollatzResearch.WordTrace tailWord_1987843 prefixEnd_1987843 1020718924675571288820583 := by
  unfold tailWord_1987843
  simp only [CollatzResearch.WordTrace]
  refine ⟨72502590537391782400808183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48335060358261188267205455 72502590537391782400808183)
  ·
    refine ⟨108753885806087673601212275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72502590537391782400808183 108753885806087673601212275)
    ·
      refine ⟨163130828709131510401818413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108753885806087673601212275 163130828709131510401818413)
      ·
        refine ⟨61174060765924316400681905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163130828709131510401818413 61174060765924316400681905)
        ·
          refine ⟨45880545574443237300511429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61174060765924316400681905 45880545574443237300511429)
          ·
            refine ⟨8602602295208106993845893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45880545574443237300511429 8602602295208106993845893)
            ·
              refine ⟨1612987930351520061346105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8602602295208106993845893 1612987930351520061346105)
              ·
                refine ⟨1209740947763640046009579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612987930351520061346105 1209740947763640046009579)
                ·
                  refine ⟨1814611421645460069014369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209740947763640046009579 1814611421645460069014369)
                  ·
                    refine ⟨1360958566234095051760777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1814611421645460069014369 1360958566234095051760777)
                    ·
                      refine ⟨1020718924675571288820583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1360958566234095051760777 1020718924675571288820583)
                      ·
                        rfl

theorem cell23_1987843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 1, 2, 2].length) (baseStart_1987843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987843 prefixEnd_1987843 := by exact prefixLift 1987843
  have htrace : WordTrace (prefixWord ++ tailWord_1987843) baseStart_1987843 baseEnd_1987843 := by
    simpa [prefixWord, tailWord_1987843, baseEnd_1987843] using wordTrace_append hprefix tailTrace_1987843
  have hstable : (prefixWord ++ tailWord_1987843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987843).length < 2 ^ (prefixWord ++ tailWord_1987843).sum := by decide
  have hdescent : baseEnd_1987843 < baseStart_1987843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987892 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_1987892 : Nat := 118140960795 + 1987892 * 2 ^ 59
def prefixEnd_1987892 : Nat := 4983230072969 + 3 ^ 40 * 1987892 * 2
def baseEnd_1987892 : Nat := 340248028409213865702619

theorem tailTrace_1987892 : CollatzResearch.WordTrace tailWord_1987892 prefixEnd_1987892 340248028409213865702619 := by
  unfold tailWord_1987892
  simp only [CollatzResearch.WordTrace]
  refine ⟨36252188857107131884670965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48336251809476175846227953 36252188857107131884670965)
  ·
    refine ⟨3398642705353793614187903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36252188857107131884670965 3398642705353793614187903)
    ·
      refine ⟨5097964058030690421281855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3398642705353793614187903 5097964058030690421281855)
      ·
        refine ⟨7646946087046035631922783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5097964058030690421281855 7646946087046035631922783)
        ·
          refine ⟨11470419130569053447884175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7646946087046035631922783 11470419130569053447884175)
          ·
            refine ⟨17205628695853580171826263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11470419130569053447884175 17205628695853580171826263)
            ·
              refine ⟨25808443043780370257739395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17205628695853580171826263 25808443043780370257739395)
              ·
                refine ⟨38712664565670555386609093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25808443043780370257739395 38712664565670555386609093)
                ·
                  refine ⟨7258624606063229134989205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38712664565670555386609093 7258624606063229134989205)
                  ·
                    refine ⟨340248028409213865702619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7258624606063229134989205 340248028409213865702619)
                    ·
                      rfl

theorem cell23_1987892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_1987892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987892 prefixEnd_1987892 := by exact prefixLift 1987892
  have htrace : WordTrace (prefixWord ++ tailWord_1987892) baseStart_1987892 baseEnd_1987892 := by
    simpa [prefixWord, tailWord_1987892, baseEnd_1987892] using wordTrace_append hprefix tailTrace_1987892
  have hstable : (prefixWord ++ tailWord_1987892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987892).length < 2 ^ (prefixWord ++ tailWord_1987892).sum := by decide
  have hdescent : baseEnd_1987892 < baseStart_1987892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987910 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1987910 : Nat := 118140960795 + 1987910 * 2 ^ 59
def prefixEnd_1987910 : Nat := 4983230072969 + 3 ^ 40 * 1987910 * 2
def baseEnd_1987910 : Nat := 1020753327879422526682775

theorem tailTrace_1987910 : CollatzResearch.WordTrace tailWord_1987910 prefixEnd_1987910 1020753327879422526682775 := by
  unfold tailWord_1987910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265782319629657901359287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48336689485432701895664789 2265782319629657901359287)
  ·
    refine ⟨3398673479444486852038931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2265782319629657901359287 3398673479444486852038931)
    ·
      refine ⟨5098010219166730278058397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3398673479444486852038931 5098010219166730278058397)
      ·
        refine ⟨1911753832187523854271899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5098010219166730278058397 1911753832187523854271899)
        ·
          refine ⟨2867630748281285781407849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911753832187523854271899 2867630748281285781407849)
          ·
            refine ⟨2150723061210964336055887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2867630748281285781407849 2150723061210964336055887)
            ·
              refine ⟨3226084591816446504083831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150723061210964336055887 3226084591816446504083831)
              ·
                refine ⟨4839126887724669756125747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226084591816446504083831 4839126887724669756125747)
                ·
                  refine ⟨7258690331587004634188621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839126887724669756125747 7258690331587004634188621)
                  ·
                    refine ⟨2722008874345126737820733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7258690331587004634188621 2722008874345126737820733)
                    ·
                      refine ⟨1020753327879422526682775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2722008874345126737820733 1020753327879422526682775)
                      ·
                        rfl

theorem cell23_1987910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1987910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987910 prefixEnd_1987910 := by exact prefixLift 1987910
  have htrace : WordTrace (prefixWord ++ tailWord_1987910) baseStart_1987910 baseEnd_1987910 := by
    simpa [prefixWord, tailWord_1987910, baseEnd_1987910] using wordTrace_append hprefix tailTrace_1987910
  have hstable : (prefixWord ++ tailWord_1987910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987910).length < 2 ^ (prefixWord ++ tailWord_1987910).sum := by decide
  have hdescent : baseEnd_1987910 < baseStart_1987910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987916 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 1, 4, 2]
def baseStart_1987916 : Nat := 118140960795 + 1987916 * 2 ^ 59
def prefixEnd_1987916 : Nat := 4983230072969 + 3 ^ 40 * 1987916 * 2
def baseEnd_1987916 : Nat := 1020756408763349503207747

theorem tailTrace_1987916 : CollatzResearch.WordTrace tailWord_1987916 prefixEnd_1987916 1020756408763349503207747 := by
  unfold tailWord_1987916
  simp only [CollatzResearch.WordTrace]
  refine ⟨36252626533063657934107801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48336835377418210578810401 36252626533063657934107801)
  ·
    refine ⟨27189469899797743450580851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36252626533063657934107801 27189469899797743450580851)
    ·
      refine ⟨40784204849696615175871277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27189469899797743450580851 40784204849696615175871277)
      ·
        refine ⟨15294076818636230690951729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40784204849696615175871277 15294076818636230690951729)
        ·
          refine ⟨11470557613977173018213797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15294076818636230690951729 11470557613977173018213797)
          ·
            refine ⟨2150729552620719940915087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11470557613977173018213797 2150729552620719940915087)
            ·
              refine ⟨3226094328931079911372631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150729552620719940915087 3226094328931079911372631)
              ·
                refine ⟨4839141493396619867058947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226094328931079911372631 4839141493396619867058947)
                ·
                  refine ⟨7258712240094929800588421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839141493396619867058947 7258712240094929800588421)
                  ·
                    refine ⟨1361008545017799337610329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7258712240094929800588421 1361008545017799337610329)
                    ·
                      refine ⟨1020756408763349503207747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361008545017799337610329 1020756408763349503207747)
                      ·
                        rfl

theorem cell23_1987916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_1987916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987916 prefixEnd_1987916 := by exact prefixLift 1987916
  have htrace : WordTrace (prefixWord ++ tailWord_1987916) baseStart_1987916 baseEnd_1987916 := by
    simpa [prefixWord, tailWord_1987916, baseEnd_1987916] using wordTrace_append hprefix tailTrace_1987916
  have hstable : (prefixWord ++ tailWord_1987916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987916).length < 2 ^ (prefixWord ++ tailWord_1987916).sum := by decide
  have hdescent : baseEnd_1987916 < baseStart_1987916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987939 : List Nat := [1, 1, 1, 5, 2, 2, 3, 3, 5]
def baseStart_1987939 : Nat := 118140960795 + 1987939 * 2 ^ 59
def prefixEnd_1987939 : Nat := 4983230072969 + 3 ^ 40 * 1987939 * 2
def baseEnd_1987939 : Nat := 113418690979822545913349

theorem tailTrace_1987939 : CollatzResearch.WordTrace tailWord_1987939 prefixEnd_1987939 113418690979822545913349 := by
  unfold tailWord_1987939
  simp only [CollatzResearch.WordTrace]
  refine ⟨72506091945043990796302871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48337394630029327197535247 72506091945043990796302871)
  ·
    refine ⟨108759137917565986194454307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72506091945043990796302871 108759137917565986194454307)
    ·
      refine ⟨163138706876348979291681461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108759137917565986194454307 163138706876348979291681461)
      ·
        refine ⟨15294253769657716808595137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163138706876348979291681461 15294253769657716808595137)
        ·
          refine ⟨11470690327243287606446353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15294253769657716808595137 11470690327243287606446353)
          ·
            refine ⟨8603017745432465704834765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11470690327243287606446353 8603017745432465704834765)
            ·
              refine ⟨3226131654537174639313037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8603017745432465704834765 3226131654537174639313037)
              ·
                refine ⟨1209799370451440489742389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3226131654537174639313037 1209799370451440489742389)
                ·
                  refine ⟨113418690979822545913349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1209799370451440489742389 113418690979822545913349)
                  ·
                    rfl

theorem cell23_1987939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 5].length) (baseStart_1987939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987939 prefixEnd_1987939 := by exact prefixLift 1987939
  have htrace : WordTrace (prefixWord ++ tailWord_1987939) baseStart_1987939 baseEnd_1987939 := by
    simpa [prefixWord, tailWord_1987939, baseEnd_1987939] using wordTrace_append hprefix tailTrace_1987939
  have hstable : (prefixWord ++ tailWord_1987939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987939).length < 2 ^ (prefixWord ++ tailWord_1987939).sum := by decide
  have hdescent : baseEnd_1987939 < baseStart_1987939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987952 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 2, 5]
def baseStart_1987952 : Nat := 118140960795 + 1987952 * 2 ^ 59
def prefixEnd_1987952 : Nat := 4983230072969 + 3 ^ 40 * 1987952 * 2
def baseEnd_1987952 : Nat := 340258298022303787452527

theorem tailTrace_1987952 : CollatzResearch.WordTrace tailWord_1987952 prefixEnd_1987952 340258298022303787452527 := by
  unfold tailWord_1987952
  simp only [CollatzResearch.WordTrace]
  refine ⟨36253283046998447008263055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48337710729331262677684073 36253283046998447008263055)
  ·
    refine ⟨54379924570497670512394583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36253283046998447008263055 54379924570497670512394583)
    ·
      refine ⟨81569886855746505768591875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54379924570497670512394583 81569886855746505768591875)
      ·
        refine ⟨122354830283619758652887813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81569886855746505768591875 122354830283619758652887813)
        ·
          refine ⟨22941530678178704747416465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122354830283619758652887813 22941530678178704747416465)
          ·
            refine ⟨17206148008634028560562349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22941530678178704747416465 17206148008634028560562349)
            ·
              refine ⟨6452305503237760710210881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17206148008634028560562349 6452305503237760710210881)
              ·
                refine ⟨4839229127428320532658161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6452305503237760710210881 4839229127428320532658161)
                ·
                  refine ⟨3629421845571240399493621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4839229127428320532658161 3629421845571240399493621)
                  ·
                    refine ⟨340258298022303787452527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3629421845571240399493621 340258298022303787452527)
                    ·
                      rfl

theorem cell23_1987952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_1987952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1987952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1987952 prefixEnd_1987952 := by exact prefixLift 1987952
  have htrace : WordTrace (prefixWord ++ tailWord_1987952) baseStart_1987952 baseEnd_1987952 := by
    simpa [prefixWord, tailWord_1987952, baseEnd_1987952] using wordTrace_append hprefix tailTrace_1987952
  have hstable : (prefixWord ++ tailWord_1987952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987952).length < 2 ^ (prefixWord ++ tailWord_1987952).sum := by decide
  have hdescent : baseEnd_1987952 < baseStart_1987952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988012 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 6]
def baseStart_1988012 : Nat := 118140960795 + 1988012 * 2 ^ 59
def prefixEnd_1988012 : Nat := 4983230072969 + 3 ^ 40 * 1988012 * 2
def baseEnd_1988012 : Nat := 113422855878464569734145

theorem tailTrace_1988012 : CollatzResearch.WordTrace tailWord_1988012 prefixEnd_1988012 113422855878464569734145 := by
  unfold tailWord_1988012
  simp only [CollatzResearch.WordTrace]
  refine ⟨36254377236889762131855145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48339169649186349509140193 36254377236889762131855145)
  ·
    refine ⟨27190782927667321598891359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36254377236889762131855145 27190782927667321598891359)
    ·
      refine ⟨40786174391500982398337039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27190782927667321598891359 40786174391500982398337039)
      ·
        refine ⟨61179261587251473597505559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40786174391500982398337039 61179261587251473597505559)
        ·
          refine ⟨91768892380877210396258339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61179261587251473597505559 91768892380877210396258339)
          ·
            refine ⟨137653338571315815594387509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91768892380877210396258339 137653338571315815594387509)
            ·
              refine ⟨12905000491060857711973829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137653338571315815594387509 12905000491060857711973829)
              ·
                refine ⟨2419687592073910820995093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12905000491060857711973829 2419687592073910820995093)
                ·
                  refine ⟨113422855878464569734145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2419687592073910820995093 113422855878464569734145)
                  ·
                    rfl

theorem cell23_1988012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_1988012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988012 prefixEnd_1988012 := by exact prefixLift 1988012
  have htrace : WordTrace (prefixWord ++ tailWord_1988012) baseStart_1988012 baseEnd_1988012 := by
    simpa [prefixWord, tailWord_1988012, baseEnd_1988012] using wordTrace_append hprefix tailTrace_1988012
  have hstable : (prefixWord ++ tailWord_1988012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988012).length < 2 ^ (prefixWord ++ tailWord_1988012).sum := by decide
  have hdescent : baseEnd_1988012 < baseStart_1988012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988107 : List Nat := [1, 1, 1, 1, 9, 1, 1, 3, 1, 1, 3]
def baseStart_1988107 : Nat := 118140960795 + 1988107 * 2 ^ 59
def prefixEnd_1988107 : Nat := 4983230072969 + 3 ^ 40 * 1988107 * 2
def baseEnd_1988107 : Nat := 1020854483568358255919369

theorem tailTrace_1988107 : CollatzResearch.WordTrace tailWord_1988107 prefixEnd_1988107 1020854483568358255919369 := by
  unfold tailWord_1988107
  simp only [CollatzResearch.WordTrace]
  refine ⟨72512219408435355488418575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48341479605623570325612383 72512219408435355488418575)
  ·
    refine ⟨108768329112653033232627863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72512219408435355488418575 108768329112653033232627863)
    ·
      refine ⟨163152493668979549848941795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108768329112653033232627863 163152493668979549848941795)
      ·
        refine ⟨244728740503469324773412693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163152493668979549848941795 244728740503469324773412693)
        ·
          refine ⟨1433957463887515574844215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 244728740503469324773412693 1433957463887515574844215)
          ·
            refine ⟨2150936195831273362266323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433957463887515574844215 2150936195831273362266323)
            ·
              refine ⟨3226404293746910043399485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150936195831273362266323 3226404293746910043399485)
              ·
                refine ⟨1209901610155091266274807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3226404293746910043399485 1209901610155091266274807)
                ·
                  refine ⟨1814852415232636899412211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209901610155091266274807 1814852415232636899412211)
                  ·
                    refine ⟨2722278622848955349118317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1814852415232636899412211 2722278622848955349118317)
                    ·
                      refine ⟨1020854483568358255919369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2722278622848955349118317 1020854483568358255919369)
                      ·
                        rfl

theorem cell23_1988107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 1, 1, 3].length) (baseStart_1988107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988107 prefixEnd_1988107 := by exact prefixLift 1988107
  have htrace : WordTrace (prefixWord ++ tailWord_1988107) baseStart_1988107 baseEnd_1988107 := by
    simpa [prefixWord, tailWord_1988107, baseEnd_1988107] using wordTrace_append hprefix tailTrace_1988107
  have hstable : (prefixWord ++ tailWord_1988107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988107).length < 2 ^ (prefixWord ++ tailWord_1988107).sum := by decide
  have hdescent : baseEnd_1988107 < baseStart_1988107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988130 : List Nat := [3, 3, 1, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_1988130 : Nat := 118140960795 + 1988130 * 2 ^ 59
def prefixEnd_1988130 : Nat := 4983230072969 + 3 ^ 40 * 1988130 * 2
def baseEnd_1988130 : Nat := 1020866293623411665931763

theorem tailTrace_1988130 : CollatzResearch.WordTrace tailWord_1988130 prefixEnd_1988130 1020866293623411665931763 := by
  unfold tailWord_1988130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18128264571838007604126461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48342038858234686944337229 18128264571838007604126461)
  ·
    refine ⟨6798099214439252851547423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18128264571838007604126461 6798099214439252851547423)
    ·
      refine ⟨10197148821658879277321135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6798099214439252851547423 10197148821658879277321135)
      ·
        refine ⟨15295723232488318915981703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10197148821658879277321135 15295723232488318915981703)
        ·
          refine ⟨22943584848732478373972555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15295723232488318915981703 22943584848732478373972555)
          ·
            refine ⟨34415377273098717560958833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22943584848732478373972555 34415377273098717560958833)
            ·
              refine ⟨25811532954824038170719125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34415377273098717560958833 25811532954824038170719125)
              ·
                refine ⟨1209915607257376789252459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25811532954824038170719125 1209915607257376789252459)
                ·
                  refine ⟨1814873410886065183878689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209915607257376789252459 1814873410886065183878689)
                  ·
                    refine ⟨1361155058164548887909017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1814873410886065183878689 1361155058164548887909017)
                    ·
                      refine ⟨1020866293623411665931763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361155058164548887909017 1020866293623411665931763)
                      ·
                        rfl

theorem cell23_1988130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_1988130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988130 prefixEnd_1988130 := by exact prefixLift 1988130
  have htrace : WordTrace (prefixWord ++ tailWord_1988130) baseStart_1988130 baseEnd_1988130 := by
    simpa [prefixWord, tailWord_1988130, baseEnd_1988130] using wordTrace_append hprefix tailTrace_1988130
  have hstable : (prefixWord ++ tailWord_1988130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988130).length < 2 ^ (prefixWord ++ tailWord_1988130).sum := by decide
  have hdescent : baseEnd_1988130 < baseStart_1988130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988136 : List Nat := [2, 1, 5, 2, 2, 1, 2, 8]
def baseStart_1988136 : Nat := 118140960795 + 1988136 * 2 ^ 59
def prefixEnd_1988136 : Nat := 4983230072969 + 3 ^ 40 * 1988136 * 2
def baseEnd_1988136 : Nat := 37809976833605134905805

theorem tailTrace_1988136 : CollatzResearch.WordTrace tailWord_1988136 prefixEnd_1988136 37809976833605134905805 := by
  unfold tailWord_1988136
  simp only [CollatzResearch.WordTrace]
  refine ⟨36256638562665146720612131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48342184750220195627482841 36256638562665146720612131)
  ·
    refine ⟨54384957843997720080918197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36256638562665146720612131 54384957843997720080918197)
    ·
      refine ⟨5098589797874786257586081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54384957843997720080918197 5098589797874786257586081)
      ·
        refine ⟨3823942348406089693189561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5098589797874786257586081 3823942348406089693189561)
        ·
          refine ⟨2867956761304567269892171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3823942348406089693189561 2867956761304567269892171)
          ·
            refine ⟨4301935141956850904838257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867956761304567269892171 4301935141956850904838257)
            ·
              refine ⟨3226451356467638178628693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4301935141956850904838257 3226451356467638178628693)
              ·
                refine ⟨37809976833605134905805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3226451356467638178628693 37809976833605134905805)
                ·
                  rfl

theorem cell23_1988136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 8].length) (baseStart_1988136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988136 prefixEnd_1988136 := by exact prefixLift 1988136
  have htrace : WordTrace (prefixWord ++ tailWord_1988136) baseStart_1988136 baseEnd_1988136 := by
    simpa [prefixWord, tailWord_1988136, baseEnd_1988136] using wordTrace_append hprefix tailTrace_1988136
  have hstable : (prefixWord ++ tailWord_1988136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988136).length < 2 ^ (prefixWord ++ tailWord_1988136).sum := by decide
  have hdescent : baseEnd_1988136 < baseStart_1988136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988139 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 1, 9, 2]
def baseStart_1988139 : Nat := 118140960795 + 1988139 * 2 ^ 59
def prefixEnd_1988139 : Nat := 4983230072969 + 3 ^ 40 * 1988139 * 2
def baseEnd_1988139 : Nat := 1020870914949302130719221

theorem tailTrace_1988139 : CollatzResearch.WordTrace tailWord_1988139 prefixEnd_1988139 1020870914949302130719221 := by
  unfold tailWord_1988139
  simp only [CollatzResearch.WordTrace]
  refine ⟨72513386544319424953583471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48342257696212949969055647 72513386544319424953583471)
  ·
    refine ⟨108770079816479137430375207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72513386544319424953583471 108770079816479137430375207)
    ·
      refine ⟨163155119724718706145562811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108770079816479137430375207 163155119724718706145562811)
      ·
        refine ⟨244732679587078059218344217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163155119724718706145562811 244732679587078059218344217)
        ·
          refine ⟨183549509690308544413758163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244732679587078059218344217 183549509690308544413758163)
          ·
            refine ⟨275324264535462816620637245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183549509690308544413758163 275324264535462816620637245)
            ·
              refine ⟨103246599200798556232738967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275324264535462816620637245 103246599200798556232738967)
              ·
                refine ⟨154869898801197834349108451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103246599200798556232738967 154869898801197834349108451)
                ·
                  refine ⟨232304848201796751523662677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154869898801197834349108451 232304848201796751523662677)
                  ·
                    refine ⟨1361161219932402840958961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 232304848201796751523662677 1361161219932402840958961)
                    ·
                      refine ⟨1020870914949302130719221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361161219932402840958961 1020870914949302130719221)
                      ·
                        rfl

theorem cell23_1988139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 9, 2].length) (baseStart_1988139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988139 prefixEnd_1988139 := by exact prefixLift 1988139
  have htrace : WordTrace (prefixWord ++ tailWord_1988139) baseStart_1988139 baseEnd_1988139 := by
    simpa [prefixWord, tailWord_1988139, baseEnd_1988139] using wordTrace_append hprefix tailTrace_1988139
  have hstable : (prefixWord ++ tailWord_1988139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988139).length < 2 ^ (prefixWord ++ tailWord_1988139).sum := by decide
  have hdescent : baseEnd_1988139 < baseStart_1988139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988199 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1988199 : Nat := 118140960795 + 1988199 * 2 ^ 59
def prefixEnd_1988199 : Nat := 4983230072969 + 3 ^ 40 * 1988199 * 2
def baseEnd_1988199 : Nat := 1020901723788571895968945

theorem tailTrace_1988199 : CollatzResearch.WordTrace tailWord_1988199 prefixEnd_1988199 1020901723788571895968945 := by
  unfold tailWord_1988199
  simp only [CollatzResearch.WordTrace]
  refine ⟨72515574924102055200767651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48343716616068036800511767 72515574924102055200767651)
  ·
    refine ⟨108773362386153082801151477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72515574924102055200767651 108773362386153082801151477)
    ·
      refine ⟨10197502723701851512607951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108773362386153082801151477 10197502723701851512607951)
      ·
        refine ⟨15296254085552777268911927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10197502723701851512607951 15296254085552777268911927)
        ·
          refine ⟨22944381128329165903367891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15296254085552777268911927 22944381128329165903367891)
          ·
            refine ⟨34416571692493748855051837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22944381128329165903367891 34416571692493748855051837)
            ·
              refine ⟨12906214384685155820644439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34416571692493748855051837 12906214384685155820644439)
              ·
                refine ⟨19359321577027733730966659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12906214384685155820644439 19359321577027733730966659)
                ·
                  refine ⟨29038982365541600596449989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19359321577027733730966659 29038982365541600596449989)
                  ·
                    refine ⟨5444809193539050111834373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29038982365541600596449989 5444809193539050111834373)
                    ·
                      refine ⟨1020901723788571895968945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5444809193539050111834373 1020901723788571895968945)
                      ·
                        rfl

theorem cell23_1988199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1988199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988199 prefixEnd_1988199 := by exact prefixLift 1988199
  have htrace : WordTrace (prefixWord ++ tailWord_1988199) baseStart_1988199 baseEnd_1988199 := by
    simpa [prefixWord, tailWord_1988199, baseEnd_1988199] using wordTrace_append hprefix tailTrace_1988199
  have hstable : (prefixWord ++ tailWord_1988199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988199).length < 2 ^ (prefixWord ++ tailWord_1988199).sum := by decide
  have hdescent : baseEnd_1988199 < baseStart_1988199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988219 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 3]
def baseStart_1988219 : Nat := 118140960795 + 1988219 * 2 ^ 59
def prefixEnd_1988219 : Nat := 4983230072969 + 3 ^ 40 * 1988219 * 2
def baseEnd_1988219 : Nat := 1020911993401661817718853

theorem tailTrace_1988219 : CollatzResearch.WordTrace tailWord_1988219 prefixEnd_1988219 1020911993401661817718853 := by
  unfold tailWord_1988219
  simp only [CollatzResearch.WordTrace]
  refine ⟨72516304384029598616495711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48344202922686399077663807 72516304384029598616495711)
  ·
    refine ⟨108774456576044397924743567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72516304384029598616495711 108774456576044397924743567)
    ·
      refine ⟨163161684864066596887115351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108774456576044397924743567 163161684864066596887115351)
      ·
        refine ⟨244742527296099895330673027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163161684864066596887115351 244742527296099895330673027)
        ·
          refine ⟨367113790944149842996009541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244742527296099895330673027 367113790944149842996009541)
          ·
            refine ⟨68833835802028095561751789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367113790944149842996009541 68833835802028095561751789)
            ·
              refine ⟨25812688425760535835656921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68833835802028095561751789 25812688425760535835656921)
              ·
                refine ⟨19359516319320401876742691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25812688425760535835656921 19359516319320401876742691)
                ·
                  refine ⟨29039274478980602815114037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19359516319320401876742691 29039274478980602815114037)
                  ·
                    refine ⟨2722431982404431513916941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29039274478980602815114037 2722431982404431513916941)
                    ·
                      refine ⟨1020911993401661817718853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2722431982404431513916941 1020911993401661817718853)
                      ·
                        rfl

theorem cell23_1988219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 3].length) (baseStart_1988219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988219 prefixEnd_1988219 := by exact prefixLift 1988219
  have htrace : WordTrace (prefixWord ++ tailWord_1988219) baseStart_1988219 baseEnd_1988219 := by
    simpa [prefixWord, tailWord_1988219, baseEnd_1988219] using wordTrace_append hprefix tailTrace_1988219
  have hstable : (prefixWord ++ tailWord_1988219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988219).length < 2 ^ (prefixWord ++ tailWord_1988219).sum := by decide
  have hdescent : baseEnd_1988219 < baseStart_1988219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988254 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_1988254 : Nat := 118140960795 + 1988254 * 2 ^ 59
def prefixEnd_1988254 : Nat := 4983230072969 + 3 ^ 40 * 1988254 * 2
def baseEnd_1988254 : Nat := 1020929965224569180781193

theorem tailTrace_1988254 : CollatzResearch.WordTrace tailWord_1988254 prefixEnd_1988254 1020929965224569180781193 := by
  unfold tailWord_1988254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9064697617362849949252477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48345053959268533062679877 9064697617362849949252477)
  ·
    refine ⟨3399261606511068730969679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9064697617362849949252477 3399261606511068730969679)
    ·
      refine ⟨5098892409766603096454519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3399261606511068730969679 5098892409766603096454519)
      ·
        refine ⟨7648338614649904644681779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5098892409766603096454519 7648338614649904644681779)
        ·
          refine ⟨11472507921974856967022669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7648338614649904644681779 11472507921974856967022669)
          ·
            refine ⟨4302190470740571362633501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11472507921974856967022669 4302190470740571362633501)
            ·
              refine ⟨1613321426527714260987563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4302190470740571362633501 1613321426527714260987563)
              ·
                refine ⟨2419982139791571391481345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613321426527714260987563 2419982139791571391481345)
                ·
                  refine ⟨1814986604843678543611009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2419982139791571391481345 1814986604843678543611009)
                  ·
                    refine ⟨1361239953632758907708257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1814986604843678543611009 1361239953632758907708257)
                    ·
                      refine ⟨1020929965224569180781193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361239953632758907708257 1020929965224569180781193)
                      ·
                        rfl

theorem cell23_1988254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_1988254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988254 prefixEnd_1988254 := by exact prefixLift 1988254
  have htrace : WordTrace (prefixWord ++ tailWord_1988254) baseStart_1988254 baseEnd_1988254 := by
    simpa [prefixWord, tailWord_1988254, baseEnd_1988254] using wordTrace_append hprefix tailTrace_1988254
  have hstable : (prefixWord ++ tailWord_1988254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988254).length < 2 ^ (prefixWord ++ tailWord_1988254).sum := by decide
  have hdescent : baseEnd_1988254 < baseStart_1988254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988259 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 4]
def baseStart_1988259 : Nat := 118140960795 + 1988259 * 2 ^ 59
def prefixEnd_1988259 : Nat := 4983230072969 + 3 ^ 40 * 1988259 * 2
def baseEnd_1988259 : Nat := 1020932532627841661218669

theorem tailTrace_1988259 : CollatzResearch.WordTrace tailWord_1988259 prefixEnd_1988259 1020932532627841661218669 := by
  unfold tailWord_1988259
  simp only [CollatzResearch.WordTrace]
  refine ⟨72517763303884685447951831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48345175535923123631967887 72517763303884685447951831)
  ·
    refine ⟨108776644955827028171927747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72517763303884685447951831 108776644955827028171927747)
    ·
      refine ⟨163164967433740542257891621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108776644955827028171927747 163164967433740542257891621)
      ·
        refine ⟨30593431393826351673354679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163164967433740542257891621 30593431393826351673354679)
        ·
          refine ⟨45890147090739527510032019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30593431393826351673354679 45890147090739527510032019)
          ·
            refine ⟨68835220636109291265048029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45890147090739527510032019 68835220636109291265048029)
            ·
              refine ⟨25813207738540984224393011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68835220636109291265048029 25813207738540984224393011)
              ·
                refine ⟨38719811607811476336589517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25813207738540984224393011 38719811607811476336589517)
                ·
                  refine ⟨14519929352929303626221069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38719811607811476336589517 14519929352929303626221069)
                  ·
                    refine ⟨5444973507348488859832901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14519929352929303626221069 5444973507348488859832901)
                    ·
                      refine ⟨1020932532627841661218669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5444973507348488859832901 1020932532627841661218669)
                      ·
                        rfl

theorem cell23_1988259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_1988259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988259 prefixEnd_1988259 := by exact prefixLift 1988259
  have htrace : WordTrace (prefixWord ++ tailWord_1988259) baseStart_1988259 baseEnd_1988259 := by
    simpa [prefixWord, tailWord_1988259, baseEnd_1988259] using wordTrace_append hprefix tailTrace_1988259
  have hstable : (prefixWord ++ tailWord_1988259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988259).length < 2 ^ (prefixWord ++ tailWord_1988259).sum := by decide
  have hdescent : baseEnd_1988259 < baseStart_1988259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988277 : List Nat := [1, 3, 3, 3, 3, 1, 1, 3, 5]
def baseStart_1988277 : Nat := 118140960795 + 1988277 * 2 ^ 59
def prefixEnd_1988277 : Nat := 4983230072969 + 3 ^ 40 * 1988277 * 2
def baseEnd_1988277 : Nat := 113437975031069176754843

theorem tailTrace_1988277 : CollatzResearch.WordTrace tailWord_1988277 prefixEnd_1988277 113437975031069176754843 := by
  unfold tailWord_1988277
  simp only [CollatzResearch.WordTrace]
  refine ⟨72518419817819474522107085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48345613211879649681404723 72518419817819474522107085)
  ·
    refine ⟨27194407431682302945790157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72518419817819474522107085 27194407431682302945790157)
    ·
      refine ⟨10197902786880863604671309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27194407431682302945790157 10197902786880863604671309)
      ·
        refine ⟨3824213545080323851751741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10197902786880863604671309 3824213545080323851751741)
        ·
          refine ⟨1434080079405121444406903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3824213545080323851751741 1434080079405121444406903)
          ·
            refine ⟨2151120119107682166610355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434080079405121444406903 2151120119107682166610355)
            ·
              refine ⟨3226680178661523249915533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151120119107682166610355 3226680178661523249915533)
              ·
                refine ⟨1210005066998071218718325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3226680178661523249915533 1210005066998071218718325)
                ·
                  refine ⟨113437975031069176754843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1210005066998071218718325 113437975031069176754843)
                  ·
                    rfl

theorem cell23_1988277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_1988277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988277 prefixEnd_1988277 := by exact prefixLift 1988277
  have htrace : WordTrace (prefixWord ++ tailWord_1988277) baseStart_1988277 baseEnd_1988277 := by
    simpa [prefixWord, tailWord_1988277, baseEnd_1988277] using wordTrace_append hprefix tailTrace_1988277
  have hstable : (prefixWord ++ tailWord_1988277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988277).length < 2 ^ (prefixWord ++ tailWord_1988277).sum := by decide
  have hdescent : baseEnd_1988277 < baseStart_1988277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988294 : List Nat := [6, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_1988294 : Nat := 118140960795 + 1988294 * 2 ^ 59
def prefixEnd_1988294 : Nat := 4983230072969 + 3 ^ 40 * 1988294 * 2
def baseEnd_1988294 : Nat := 113438944938972113809001

theorem tailTrace_1988294 : CollatzResearch.WordTrace tailWord_1988294 prefixEnd_1988294 113438944938972113809001 := by
  unfold tailWord_1988294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266219995586183950796123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48346026572505257616983957 2266219995586183950796123)
  ·
    refine ⟨3399329993379275926194185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2266219995586183950796123 3399329993379275926194185)
    ·
      refine ⟨2549497495034456944645639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3399329993379275926194185 2549497495034456944645639)
      ·
        refine ⟨3824246242551685416968459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2549497495034456944645639 3824246242551685416968459)
        ·
          refine ⟨5736369363827528125452689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3824246242551685416968459 5736369363827528125452689)
          ·
            refine ⟨4302277022870646094089517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5736369363827528125452689 4302277022870646094089517)
            ·
              refine ⟨1613353883576492285283569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4302277022870646094089517 1613353883576492285283569)
              ·
                refine ⟨1210015412682369213962677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1613353883576492285283569 1210015412682369213962677)
                ·
                  refine ⟨113438944938972113809001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1210015412682369213962677 113438944938972113809001)
                  ·
                    rfl

theorem cell23_1988294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_1988294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988294 prefixEnd_1988294 := by exact prefixLift 1988294
  have htrace : WordTrace (prefixWord ++ tailWord_1988294) baseStart_1988294 baseEnd_1988294 := by
    simpa [prefixWord, tailWord_1988294, baseEnd_1988294] using wordTrace_append hprefix tailTrace_1988294
  have hstable : (prefixWord ++ tailWord_1988294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988294).length < 2 ^ (prefixWord ++ tailWord_1988294).sum := by decide
  have hdescent : baseEnd_1988294 < baseStart_1988294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988303 : List Nat := [1, 1, 2, 1, 1, 3, 1, 8, 1, 4]
def baseStart_1988303 : Nat := 118140960795 + 1988303 * 2 ^ 59
def prefixEnd_1988303 : Nat := 4983230072969 + 3 ^ 40 * 1988303 * 2
def baseEnd_1988303 : Nat := 340318375258879829689489

theorem tailTrace_1988303 : CollatzResearch.WordTrace tailWord_1988303 prefixEnd_1988303 340318375258879829689489 := by
  unfold tailWord_1988303
  simp only [CollatzResearch.WordTrace]
  refine ⟨72519368115725280962553563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48346245410483520641702375 72519368115725280962553563)
  ·
    refine ⟨108779052173587921443830345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72519368115725280962553563 108779052173587921443830345)
    ·
      refine ⟨81584289130190941082872759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108779052173587921443830345 81584289130190941082872759)
      ·
        refine ⟨122376433695286411624309139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81584289130190941082872759 122376433695286411624309139)
        ·
          refine ⟨183564650542929617436463709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122376433695286411624309139 183564650542929617436463709)
          ·
            refine ⟨68836743953598606538673891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183564650542929617436463709 68836743953598606538673891)
            ·
              refine ⟨103255115930397909808010837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68836743953598606538673891 103255115930397909808010837)
              ·
                refine ⟨1210020889809350505562627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 103255115930397909808010837 1210020889809350505562627)
                ·
                  refine ⟨1815031334714025758343941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210020889809350505562627 1815031334714025758343941)
                  ·
                    refine ⟨340318375258879829689489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1815031334714025758343941 340318375258879829689489)
                    ·
                      rfl

theorem cell23_1988303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 1, 4].length) (baseStart_1988303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988303 prefixEnd_1988303 := by exact prefixLift 1988303
  have htrace : WordTrace (prefixWord ++ tailWord_1988303) baseStart_1988303 baseEnd_1988303 := by
    simpa [prefixWord, tailWord_1988303, baseEnd_1988303] using wordTrace_append hprefix tailTrace_1988303
  have hstable : (prefixWord ++ tailWord_1988303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988303).length < 2 ^ (prefixWord ++ tailWord_1988303).sum := by decide
  have hdescent : baseEnd_1988303 < baseStart_1988303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988350 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_1988350 : Nat := 118140960795 + 1988350 * 2 ^ 59
def prefixEnd_1988350 : Nat := 4983230072969 + 3 ^ 40 * 1988350 * 2
def baseEnd_1988350 : Nat := 113442139929711200575639

theorem tailTrace_1988350 : CollatzResearch.WordTrace tailWord_1988350 prefixEnd_1988350 113442139929711200575639 := by
  unfold tailWord_1988350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9065135293319375998689313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48347388231036671993009669 9065135293319375998689313)
  ·
    refine ⟨6798851469989531999016985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9065135293319375998689313 6798851469989531999016985)
    ·
      refine ⟨5099138602492148999262739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6798851469989531999016985 5099138602492148999262739)
      ·
        refine ⟨7648707903738223498894109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5099138602492148999262739 7648707903738223498894109)
        ·
          refine ⟨2868265463901833812085291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7648707903738223498894109 2868265463901833812085291)
          ·
            refine ⟨4302398195852750718127937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868265463901833812085291 4302398195852750718127937)
            ·
              refine ⟨3226798646889563038595953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4302398195852750718127937 3226798646889563038595953)
              ·
                refine ⟨2420098985167172278946965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3226798646889563038595953 2420098985167172278946965)
                ·
                  refine ⟨113442139929711200575639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2420098985167172278946965 113442139929711200575639)
                  ·
                    rfl

theorem cell23_1988350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_1988350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988350 prefixEnd_1988350 := by exact prefixLift 1988350
  have htrace : WordTrace (prefixWord ++ tailWord_1988350) baseStart_1988350 baseEnd_1988350 := by
    simpa [prefixWord, tailWord_1988350, baseEnd_1988350] using wordTrace_append hprefix tailTrace_1988350
  have hstable : (prefixWord ++ tailWord_1988350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988350).length < 2 ^ (prefixWord ++ tailWord_1988350).sum := by decide
  have hdescent : baseEnd_1988350 < baseStart_1988350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988376 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 1, 6]
def baseStart_1988376 : Nat := 118140960795 + 1988376 * 2 ^ 59
def prefixEnd_1988376 : Nat := 4983230072969 + 3 ^ 40 * 1988376 * 2
def baseEnd_1988376 : Nat := 340330869954805901151877

theorem tailTrace_1988376 : CollatzResearch.WordTrace tailWord_1988376 prefixEnd_1988376 340330869954805901151877 := by
  unfold tailWord_1988376
  simp only [CollatzResearch.WordTrace]
  refine ⟨36261015322230407214980491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48348020429640542953307321 36261015322230407214980491)
  ·
    refine ⟨54391522983345610822470737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36261015322230407214980491 54391522983345610822470737)
    ·
      refine ⟨40793642237509208116853053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54391522983345610822470737 40793642237509208116853053)
      ·
        refine ⟨15297615839065953043819895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40793642237509208116853053 15297615839065953043819895)
        ·
          refine ⟨22946423758598929565729843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15297615839065953043819895 22946423758598929565729843)
          ·
            refine ⟨34419635637898394348594765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22946423758598929565729843 34419635637898394348594765)
            ·
              refine ⟨12907363364211897880723037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34419635637898394348594765 12907363364211897880723037)
              ·
                refine ⟨4840261261579461705271139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12907363364211897880723037 4840261261579461705271139)
                ·
                  refine ⟨7260391892369192557906709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4840261261579461705271139 7260391892369192557906709)
                  ·
                    refine ⟨340330869954805901151877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7260391892369192557906709 340330869954805901151877)
                    ·
                      rfl

theorem cell23_1988376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_1988376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988376 prefixEnd_1988376 := by exact prefixLift 1988376
  have htrace : WordTrace (prefixWord ++ tailWord_1988376) baseStart_1988376 baseEnd_1988376 := by
    simpa [prefixWord, tailWord_1988376, baseEnd_1988376] using wordTrace_append hprefix tailTrace_1988376
  have hstable : (prefixWord ++ tailWord_1988376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988376).length < 2 ^ (prefixWord ++ tailWord_1988376).sum := by decide
  have hdescent : baseEnd_1988376 < baseStart_1988376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988383 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 4]
def baseStart_1988383 : Nat := 118140960795 + 1988383 * 2 ^ 59
def prefixEnd_1988383 : Nat := 4983230072969 + 3 ^ 40 * 1988383 * 2
def baseEnd_1988383 : Nat := 1020996204228999176068099

theorem tailTrace_1988383 : CollatzResearch.WordTrace tailWord_1988383 prefixEnd_1988383 1020996204228999176068099 := by
  unfold tailWord_1988383
  simp only [CollatzResearch.WordTrace]
  refine ⟨72522285955435454625465803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48348190636956969750310535 72522285955435454625465803)
  ·
    refine ⟨108783428933153181938198705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72522285955435454625465803 108783428933153181938198705)
    ·
      refine ⟨81587571699864886453649029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108783428933153181938198705 81587571699864886453649029)
      ·
        refine ⟨15297669693724666210059193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81587571699864886453649029 15297669693724666210059193)
        ·
          refine ⟨11473252270293499657544395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15297669693724666210059193 11473252270293499657544395)
          ·
            refine ⟨17209878405440249486316593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11473252270293499657544395 17209878405440249486316593)
            ·
              refine ⟨12907408804080187114737445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17209878405440249486316593 12907408804080187114737445)
              ·
                refine ⟨2420139150765035084013271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12907408804080187114737445 2420139150765035084013271)
                ·
                  refine ⟨3630208726147552626019907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420139150765035084013271 3630208726147552626019907)
                  ·
                    refine ⟨5445313089221328939029861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3630208726147552626019907 5445313089221328939029861)
                    ·
                      refine ⟨1020996204228999176068099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5445313089221328939029861 1020996204228999176068099)
                      ·
                        rfl

theorem cell23_1988383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_1988383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988383 prefixEnd_1988383 := by exact prefixLift 1988383
  have htrace : WordTrace (prefixWord ++ tailWord_1988383) baseStart_1988383 baseEnd_1988383 := by
    simpa [prefixWord, tailWord_1988383, baseEnd_1988383] using wordTrace_append hprefix tailTrace_1988383
  have hstable : (prefixWord ++ tailWord_1988383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988383).length < 2 ^ (prefixWord ++ tailWord_1988383).sum := by decide
  have hdescent : baseEnd_1988383 < baseStart_1988383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988410 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 2, 4]
def baseStart_1988410 : Nat := 118140960795 + 1988410 * 2 ^ 59
def prefixEnd_1988410 : Nat := 4983230072969 + 3 ^ 40 * 1988410 * 2
def baseEnd_1988410 : Nat := 340336689402223523476825

theorem tailTrace_1988410 : CollatzResearch.WordTrace tailWord_1988410 prefixEnd_1988410 340336689402223523476825 := by
  unfold tailWord_1988410
  simp only [CollatzResearch.WordTrace]
  refine ⟨18130817681584409559174671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48348847150891758824465789 18130817681584409559174671)
  ·
    refine ⟨27196226522376614338762007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18130817681584409559174671 27196226522376614338762007)
    ·
      refine ⟨40794339783564921508143011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27196226522376614338762007 40794339783564921508143011)
      ·
        refine ⟨61191509675347382262214517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40794339783564921508143011 61191509675347382262214517)
        ·
          refine ⟨5736704032063817087082611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61191509675347382262214517 5736704032063817087082611)
          ·
            refine ⟨8605056048095725630623917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5736704032063817087082611 8605056048095725630623917)
            ·
              refine ⟨3226896018035897111483969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8605056048095725630623917 3226896018035897111483969)
              ·
                refine ⟨2420172013526922833612977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3226896018035897111483969 2420172013526922833612977)
                ·
                  refine ⟨1815129010145192125209733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2420172013526922833612977 1815129010145192125209733)
                  ·
                    refine ⟨340336689402223523476825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1815129010145192125209733 340336689402223523476825)
                    ·
                      rfl

theorem cell23_1988410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_1988410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988410 prefixEnd_1988410 := by exact prefixLift 1988410
  have htrace : WordTrace (prefixWord ++ tailWord_1988410) baseStart_1988410 baseEnd_1988410 := by
    simpa [prefixWord, tailWord_1988410, baseEnd_1988410] using wordTrace_append hprefix tailTrace_1988410
  have hstable : (prefixWord ++ tailWord_1988410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988410).length < 2 ^ (prefixWord ++ tailWord_1988410).sum := by decide
  have hdescent : baseEnd_1988410 < baseStart_1988410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988416 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 3]
def baseStart_1988416 : Nat := 118140960795 + 1988416 * 2 ^ 59
def prefixEnd_1988416 : Nat := 4983230072969 + 3 ^ 40 * 1988416 * 2
def baseEnd_1988416 : Nat := 1021013149090597546955447

theorem tailTrace_1988416 : CollatzResearch.WordTrace tailWord_1988416 prefixEnd_1988416 1021013149090597546955447 := by
  unfold tailWord_1988416
  simp only [CollatzResearch.WordTrace]
  refine ⟨36261744782157950630708551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48348993042877267507611401 36261744782157950630708551)
  ·
    refine ⟨54392617173236925946062827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36261744782157950630708551 54392617173236925946062827)
    ·
      refine ⟨81588925759855388919094241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54392617173236925946062827 81588925759855388919094241)
      ·
        refine ⟨61191694319891541689320681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81588925759855388919094241 61191694319891541689320681)
        ·
          refine ⟨45893770739918656266990511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61191694319891541689320681 45893770739918656266990511)
          ·
            refine ⟨68840656109877984400485767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45893770739918656266990511 68840656109877984400485767)
            ·
              refine ⟨103260984164816976600728651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68840656109877984400485767 103260984164816976600728651)
              ·
                refine ⟨154891476247225464901092977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103260984164816976600728651 154891476247225464901092977)
                ·
                  refine ⟨116168607185419098675819733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154891476247225464901092977 116168607185419098675819733)
                  ·
                    refine ⟨2722701730908260125214525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 116168607185419098675819733 2722701730908260125214525)
                    ·
                      refine ⟨1021013149090597546955447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2722701730908260125214525 1021013149090597546955447)
                      ·
                        rfl

theorem cell23_1988416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_1988416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988416 prefixEnd_1988416 := by exact prefixLift 1988416
  have htrace : WordTrace (prefixWord ++ tailWord_1988416) baseStart_1988416 baseEnd_1988416 := by
    simpa [prefixWord, tailWord_1988416, baseEnd_1988416] using wordTrace_append hprefix tailTrace_1988416
  have hstable : (prefixWord ++ tailWord_1988416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988416).length < 2 ^ (prefixWord ++ tailWord_1988416).sum := by decide
  have hdescent : baseEnd_1988416 < baseStart_1988416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988451 : List Nat := [1, 1, 1, 5, 4, 2, 1, 3, 1, 2, 2]
def baseStart_1988451 : Nat := 118140960795 + 1988451 * 2 ^ 59
def prefixEnd_1988451 : Nat := 4983230072969 + 3 ^ 40 * 1988451 * 2
def baseEnd_1988451 : Nat := 1021031120913504910017787

theorem tailTrace_1988451 : CollatzResearch.WordTrace tailWord_1988451 prefixEnd_1988451 1021031120913504910017787 := by
  unfold tailWord_1988451
  simp only [CollatzResearch.WordTrace]
  refine ⟨72524766119189102238941207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48349844079459401492627471 72524766119189102238941207)
  ·
    refine ⟨108787149178783653358411811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72524766119189102238941207 108787149178783653358411811)
    ·
      refine ⟨163180723768175480037617717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108787149178783653358411811 163180723768175480037617717)
      ·
        refine ⟨15298192853266451253526661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163180723768175480037617717 15298192853266451253526661)
        ·
          refine ⟨2868411159987459610036249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15298192853266451253526661 2868411159987459610036249)
          ·
            refine ⟨2151308369990594707527187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868411159987459610036249 2151308369990594707527187)
            ·
              refine ⟨3226962554985892061290781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151308369990594707527187 3226962554985892061290781)
              ·
                refine ⟨1210110958119709522984043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3226962554985892061290781 1210110958119709522984043)
                ·
                  refine ⟨1815166437179564284476065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210110958119709522984043 1815166437179564284476065)
                  ·
                    refine ⟨1361374827884673213357049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1815166437179564284476065 1361374827884673213357049)
                    ·
                      refine ⟨1021031120913504910017787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361374827884673213357049 1021031120913504910017787)
                      ·
                        rfl

theorem cell23_1988451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_1988451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988451 prefixEnd_1988451 := by exact prefixLift 1988451
  have htrace : WordTrace (prefixWord ++ tailWord_1988451) baseStart_1988451 baseEnd_1988451 := by
    simpa [prefixWord, tailWord_1988451, baseEnd_1988451] using wordTrace_append hprefix tailTrace_1988451
  have hstable : (prefixWord ++ tailWord_1988451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988451).length < 2 ^ (prefixWord ++ tailWord_1988451).sum := by decide
  have hdescent : baseEnd_1988451 < baseStart_1988451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988494 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1988494 : Nat := 118140960795 + 1988494 * 2 ^ 59
def prefixEnd_1988494 : Nat := 4983230072969 + 3 ^ 40 * 1988494 * 2
def baseEnd_1988494 : Nat := 1021053200581648241780089

theorem tailTrace_1988494 : CollatzResearch.WordTrace tailWord_1988494 prefixEnd_1988494 1021053200581648241780089 := by
  unfold tailWord_1988494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9065791807254165072844567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48350889638688880388504357 9065791807254165072844567)
  ·
    refine ⟨13598687710881247609266851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9065791807254165072844567 13598687710881247609266851)
    ·
      refine ⟨20398031566321871413900277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13598687710881247609266851 20398031566321871413900277)
      ·
        refine ⟨1912315459342675445053151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20398031566321871413900277 1912315459342675445053151)
        ·
          refine ⟨2868473189014013167579727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912315459342675445053151 2868473189014013167579727)
          ·
            refine ⟨4302709783521019751369591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868473189014013167579727 4302709783521019751369591)
            ·
              refine ⟨6454064675281529627054387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4302709783521019751369591 6454064675281529627054387)
              ·
                refine ⟨9681097012922294440581581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454064675281529627054387 9681097012922294440581581)
                ·
                  refine ⟨3630411379845860415218093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9681097012922294440581581 3630411379845860415218093)
                  ·
                    refine ⟨1361404267442197655706785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630411379845860415218093 1361404267442197655706785)
                    ·
                      refine ⟨1021053200581648241780089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361404267442197655706785 1021053200581648241780089)
                      ·
                        rfl

theorem cell23_1988494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1988494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988494 prefixEnd_1988494 := by exact prefixLift 1988494
  have htrace : WordTrace (prefixWord ++ tailWord_1988494) baseStart_1988494 baseEnd_1988494 := by
    simpa [prefixWord, tailWord_1988494, baseEnd_1988494] using wordTrace_append hprefix tailTrace_1988494
  have hstable : (prefixWord ++ tailWord_1988494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988494).length < 2 ^ (prefixWord ++ tailWord_1988494).sum := by decide
  have hdescent : baseEnd_1988494 < baseStart_1988494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988580 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 4, 4, 2]
def baseStart_1988580 : Nat := 118140960795 + 1988580 * 2 ^ 59
def prefixEnd_1988580 : Nat := 4983230072969 + 3 ^ 40 * 1988580 * 2
def baseEnd_1988580 : Nat := 1021097359917934905304693

theorem tailTrace_1988580 : CollatzResearch.WordTrace tailWord_1988580 prefixEnd_1988580 1021097359917934905304693 := by
  unfold tailWord_1988580
  simp only [CollatzResearch.WordTrace]
  refine ⟨36264735567860878635193597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48352980757147838180258129 36264735567860878635193597)
  ·
    refine ⟨13599275837947829488197599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36264735567860878635193597 13599275837947829488197599)
    ·
      refine ⟨20398913756921744232296399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13599275837947829488197599 20398913756921744232296399)
      ·
        refine ⟨30598370635382616348444599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20398913756921744232296399 30598370635382616348444599)
        ·
          refine ⟨45897555953073924522666899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30598370635382616348444599 45897555953073924522666899)
          ·
            refine ⟨68846333929610886784000349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45897555953073924522666899 68846333929610886784000349)
            ·
              refine ⟨25817375223604082544000131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68846333929610886784000349 25817375223604082544000131)
              ·
                refine ⟨38726062835406123816000197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25817375223604082544000131 38726062835406123816000197)
                ·
                  refine ⟨7261136781638648215500037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38726062835406123816000197 7261136781638648215500037)
                  ·
                    refine ⟨1361463146557246540406257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7261136781638648215500037 1361463146557246540406257)
                    ·
                      refine ⟨1021097359917934905304693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361463146557246540406257 1021097359917934905304693)
                      ·
                        rfl

theorem cell23_1988580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_1988580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988580 prefixEnd_1988580 := by exact prefixLift 1988580
  have htrace : WordTrace (prefixWord ++ tailWord_1988580) baseStart_1988580 baseEnd_1988580 := by
    simpa [prefixWord, tailWord_1988580, baseEnd_1988580] using wordTrace_append hprefix tailTrace_1988580
  have hstable : (prefixWord ++ tailWord_1988580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988580).length < 2 ^ (prefixWord ++ tailWord_1988580).sum := by decide
  have hdescent : baseEnd_1988580 < baseStart_1988580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988603 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 6]
def baseStart_1988603 : Nat := 118140960795 + 1988603 * 2 ^ 59
def prefixEnd_1988603 : Nat := 4983230072969 + 3 ^ 40 * 1988603 * 2
def baseEnd_1988603 : Nat := 113456574441443146146343

theorem tailTrace_1988603 : CollatzResearch.WordTrace tailWord_1988603 prefixEnd_1988603 113456574441443146146343 := by
  unfold tailWord_1988603
  simp only [CollatzResearch.WordTrace]
  refine ⟨72530310014638432198474463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48353540009758954798982975 72530310014638432198474463)
  ·
    refine ⟨108795465021957648297711695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72530310014638432198474463 108795465021957648297711695)
    ·
      refine ⟨163193197532936472446567543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108795465021957648297711695 163193197532936472446567543)
      ·
        refine ⟨244789796299404708669851315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163193197532936472446567543 244789796299404708669851315)
        ·
          refine ⟨367184694449107063004776973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244789796299404708669851315 367184694449107063004776973)
          ·
            refine ⟨137694260418415148626791365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367184694449107063004776973 137694260418415148626791365)
            ·
              refine ⟨25817673828452840367523381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137694260418415148626791365 25817673828452840367523381)
              ·
                refine ⟨2420406921417453784455317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25817673828452840367523381 2420406921417453784455317)
                ·
                  refine ⟨113456574441443146146343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2420406921417453784455317 113456574441443146146343)
                  ·
                    rfl

theorem cell23_1988603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 6].length) (baseStart_1988603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988603 prefixEnd_1988603 := by exact prefixLift 1988603
  have htrace : WordTrace (prefixWord ++ tailWord_1988603) baseStart_1988603 baseEnd_1988603 := by
    simpa [prefixWord, tailWord_1988603, baseEnd_1988603] using wordTrace_append hprefix tailTrace_1988603
  have hstable : (prefixWord ++ tailWord_1988603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988603).length < 2 ^ (prefixWord ++ tailWord_1988603).sum := by decide
  have hdescent : baseEnd_1988603 < baseStart_1988603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988633 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 5, 5]
def baseStart_1988633 : Nat := 118140960795 + 1988633 * 2 ^ 59
def prefixEnd_1988633 : Nat := 4983230072969 + 3 ^ 40 * 1988633 * 2
def baseEnd_1988633 : Nat := 340374858130874399313983

theorem tailTrace_1988633 : CollatzResearch.WordTrace tailWord_1988633 prefixEnd_1988633 340374858130874399313983 := by
  unfold tailWord_1988633
  simp only [CollatzResearch.WordTrace]
  refine ⟨72531404204529747322066553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48354269469686498214711035 72531404204529747322066553)
  ·
    refine ⟨54398553153397310491549915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72531404204529747322066553 54398553153397310491549915)
    ·
      refine ⟨81597829730095965737324873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54398553153397310491549915 81597829730095965737324873)
      ·
        refine ⟨61198372297571974302993655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81597829730095965737324873 61198372297571974302993655)
        ·
          refine ⟨91797558446357961454490483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61198372297571974302993655 91797558446357961454490483)
          ·
            refine ⟨137696337669536942181735725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91797558446357961454490483 137696337669536942181735725)
            ·
              refine ⟨51636126626076353318150897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137696337669536942181735725 51636126626076353318150897)
              ·
                refine ⟨38727094969557264988613173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51636126626076353318150897 38727094969557264988613173)
                ·
                  refine ⟨3630665153395993592682485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38727094969557264988613173 3630665153395993592682485)
                  ·
                    refine ⟨340374858130874399313983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3630665153395993592682485 340374858130874399313983)
                    ·
                      rfl

theorem cell23_1988633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_1988633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988633 prefixEnd_1988633 := by exact prefixLift 1988633
  have htrace : WordTrace (prefixWord ++ tailWord_1988633) baseStart_1988633 baseEnd_1988633 := by
    simpa [prefixWord, tailWord_1988633, baseEnd_1988633] using wordTrace_append hprefix tailTrace_1988633
  have hstable : (prefixWord ++ tailWord_1988633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988633).length < 2 ^ (prefixWord ++ tailWord_1988633).sum := by decide
  have hdescent : baseEnd_1988633 < baseStart_1988633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988641 : List Nat := [1, 2, 3, 2, 4, 1, 3, 2, 1, 4]
def baseStart_1988641 : Nat := 118140960795 + 1988641 * 2 ^ 59
def prefixEnd_1988641 : Nat := 4983230072969 + 3 ^ 40 * 1988641 * 2
def baseEnd_1988641 : Nat := 340376227412619722213971

theorem tailTrace_1988641 : CollatzResearch.WordTrace tailWord_1988641 prefixEnd_1988641 340376227412619722213971 := by
  unfold tailWord_1988641
  simp only [CollatzResearch.WordTrace]
  refine ⟨72531695988500764688357777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48354463992333843125571851 72531695988500764688357777)
  ·
    refine ⟨54398771991375573516268333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72531695988500764688357777 54398771991375573516268333)
    ·
      refine ⟨20399539496765840068600625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54398771991375573516268333 20399539496765840068600625)
      ·
        refine ⟨15299654622574380051450469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20399539496765840068600625 15299654622574380051450469)
        ·
          refine ⟨2868685241732696259646963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15299654622574380051450469 2868685241732696259646963)
          ·
            refine ⟨4303027862599044389470445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868685241732696259646963 4303027862599044389470445)
            ·
              refine ⟨1613635448474641646051417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4303027862599044389470445 1613635448474641646051417)
              ·
                refine ⟨1210226586355981234538563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1613635448474641646051417 1210226586355981234538563)
                ·
                  refine ⟨1815339879533971851807845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210226586355981234538563 1815339879533971851807845)
                  ·
                    refine ⟨340376227412619722213971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1815339879533971851807845 340376227412619722213971)
                    ·
                      rfl

theorem cell23_1988641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_1988641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988641 prefixEnd_1988641 := by exact prefixLift 1988641
  have htrace : WordTrace (prefixWord ++ tailWord_1988641) baseStart_1988641 baseEnd_1988641 := by
    simpa [prefixWord, tailWord_1988641, baseEnd_1988641] using wordTrace_append hprefix tailTrace_1988641
  have hstable : (prefixWord ++ tailWord_1988641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988641).length < 2 ^ (prefixWord ++ tailWord_1988641).sum := by decide
  have hdescent : baseEnd_1988641 < baseStart_1988641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988654 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_1988654 : Nat := 118140960795 + 1988654 * 2 ^ 59
def prefixEnd_1988654 : Nat := 4983230072969 + 3 ^ 40 * 1988654 * 2
def baseEnd_1988654 : Nat := 113459484165151957308817

theorem tailTrace_1988654 : CollatzResearch.WordTrace tailWord_1988654 prefixEnd_1988654 113459484165151957308817 := by
  unfold tailWord_1988654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9066521267181708488572627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48354780091635778605720677 9066521267181708488572627)
  ·
    refine ⟨13599781900772562732858941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9066521267181708488572627 13599781900772562732858941)
    ·
      refine ⟨5099918212789711024822103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13599781900772562732858941 5099918212789711024822103)
      ·
        refine ⟨7649877319184566537233155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5099918212789711024822103 7649877319184566537233155)
        ·
          refine ⟨11474815978776849805849733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7649877319184566537233155 11474815978776849805849733)
          ·
            refine ⟨2151527996020659338596825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11474815978776849805849733 2151527996020659338596825)
            ·
              refine ⟨1613645997015494503947619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151527996020659338596825 1613645997015494503947619)
              ·
                refine ⟨2420468995523241755921429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613645997015494503947619 2420468995523241755921429)
                ·
                  refine ⟨113459484165151957308817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2420468995523241755921429 113459484165151957308817)
                  ·
                    rfl

theorem cell23_1988654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_1988654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988654 prefixEnd_1988654 := by exact prefixLift 1988654
  have htrace : WordTrace (prefixWord ++ tailWord_1988654) baseStart_1988654 baseEnd_1988654 := by
    simpa [prefixWord, tailWord_1988654, baseEnd_1988654] using wordTrace_append hprefix tailTrace_1988654
  have hstable : (prefixWord ++ tailWord_1988654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988654).length < 2 ^ (prefixWord ++ tailWord_1988654).sum := by decide
  have hdescent : baseEnd_1988654 < baseStart_1988654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988680 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 4, 4]
def baseStart_1988680 : Nat := 118140960795 + 1988680 * 2 ^ 59
def prefixEnd_1988680 : Nat := 4983230072969 + 3 ^ 40 * 1988680 * 2
def baseEnd_1988680 : Nat := 340382902661128171351411

theorem tailTrace_1988680 : CollatzResearch.WordTrace tailWord_1988680 prefixEnd_1988680 340382902661128171351411 := by
  unfold tailWord_1988680
  simp only [CollatzResearch.WordTrace]
  refine ⟨36266559217679737174513747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48355412290239649566018329 36266559217679737174513747)
  ·
    refine ⟨54399838826519605761770621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36266559217679737174513747 54399838826519605761770621)
    ·
      refine ⟨20399939559944852160663983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54399838826519605761770621 20399939559944852160663983)
      ·
        refine ⟨30599909339917278240995975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20399939559944852160663983 30599909339917278240995975)
        ·
          refine ⟨45899864009875917361493963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30599909339917278240995975 45899864009875917361493963)
          ·
            refine ⟨68849796014813876042240945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45899864009875917361493963 68849796014813876042240945)
            ·
              refine ⟨51637347011110407031680709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68849796014813876042240945 51637347011110407031680709)
              ·
                refine ⟨9682002564583201318440133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51637347011110407031680709 9682002564583201318440133)
                ·
                  refine ⟨1815375480859350247207525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9682002564583201318440133 1815375480859350247207525)
                  ·
                    refine ⟨340382902661128171351411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1815375480859350247207525 340382902661128171351411)
                    ·
                      rfl

theorem cell23_1988680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_1988680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988680 prefixEnd_1988680 := by exact prefixLift 1988680
  have htrace : WordTrace (prefixWord ++ tailWord_1988680) baseStart_1988680 baseEnd_1988680 := by
    simpa [prefixWord, tailWord_1988680, baseEnd_1988680] using wordTrace_append hprefix tailTrace_1988680
  have hstable : (prefixWord ++ tailWord_1988680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988680).length < 2 ^ (prefixWord ++ tailWord_1988680).sum := by decide
  have hdescent : baseEnd_1988680 < baseStart_1988680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988687 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 5, 2, 2]
def baseStart_1988687 : Nat := 118140960795 + 1988687 * 2 ^ 59
def prefixEnd_1988687 : Nat := 4983230072969 + 3 ^ 40 * 1988687 * 2
def baseEnd_1988687 : Nat := 1021152302347965986666701

theorem tailTrace_1988687 : CollatzResearch.WordTrace tailWord_1988687 prefixEnd_1988687 1021152302347965986666701 := by
  unfold tailWord_1988687
  simp only [CollatzResearch.WordTrace]
  refine ⟨72533373746334114544532315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48355582497556076363021543 72533373746334114544532315)
  ·
    refine ⟨108800060619501171816798473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72533373746334114544532315 108800060619501171816798473)
    ·
      refine ⟨81600045464625878862598855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108800060619501171816798473 81600045464625878862598855)
      ·
        refine ⟨122400068196938818293898283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81600045464625878862598855 122400068196938818293898283)
        ·
          refine ⟨183600102295408227440847425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122400068196938818293898283 183600102295408227440847425)
          ·
            refine ⟨137700076721556170580635569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183600102295408227440847425 137700076721556170580635569)
            ·
              refine ⟨103275057541167127935476677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137700076721556170580635569 103275057541167127935476677)
              ·
                refine ⟨19364073288968836487901877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103275057541167127935476677 19364073288968836487901877)
                ·
                  refine ⟨1815381870840828420740801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19364073288968836487901877 1815381870840828420740801)
                  ·
                    refine ⟨1361536403130621315555601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1815381870840828420740801 1361536403130621315555601)
                    ·
                      refine ⟨1021152302347965986666701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361536403130621315555601 1021152302347965986666701)
                      ·
                        rfl

theorem cell23_1988687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 2, 2].length) (baseStart_1988687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988687 prefixEnd_1988687 := by exact prefixLift 1988687
  have htrace : WordTrace (prefixWord ++ tailWord_1988687) baseStart_1988687 baseEnd_1988687 := by
    simpa [prefixWord, tailWord_1988687, baseEnd_1988687] using wordTrace_append hprefix tailTrace_1988687
  have hstable : (prefixWord ++ tailWord_1988687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988687).length < 2 ^ (prefixWord ++ tailWord_1988687).sum := by decide
  have hdescent : baseEnd_1988687 < baseStart_1988687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988693 : List Nat := [1, 3, 2, 2, 1, 14]
def baseStart_1988693 : Nat := 118140960795 + 1988693 * 2 ^ 59
def prefixEnd_1988693 : Nat := 4983230072969 + 3 ^ 40 * 1988693 * 2
def baseEnd_1988693 : Nat := 4202285527703263223011

theorem tailTrace_1988693 : CollatzResearch.WordTrace tailWord_1988693 prefixEnd_1988693 4202285527703263223011 := by
  unfold tailWord_1988693
  simp only [CollatzResearch.WordTrace]
  refine ⟨72533592584312377569250733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48355728389541585046167155 72533592584312377569250733)
  ·
    refine ⟨27200097219117141588469025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72533592584312377569250733 27200097219117141588469025)
    ·
      refine ⟨20400072914337856191351769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27200097219117141588469025 20400072914337856191351769)
      ·
        refine ⟨15300054685753392143513827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20400072914337856191351769 15300054685753392143513827)
        ·
          refine ⟨22950082028630088215270741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15300054685753392143513827 22950082028630088215270741)
          ·
            refine ⟨4202285527703263223011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 22950082028630088215270741 4202285527703263223011)
            ·
              rfl

theorem cell23_1988693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 14].length) (baseStart_1988693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988693 prefixEnd_1988693 := by exact prefixLift 1988693
  have htrace : WordTrace (prefixWord ++ tailWord_1988693) baseStart_1988693 baseEnd_1988693 := by
    simpa [prefixWord, tailWord_1988693, baseEnd_1988693] using wordTrace_append hprefix tailTrace_1988693
  have hstable : (prefixWord ++ tailWord_1988693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988693).length < 2 ^ (prefixWord ++ tailWord_1988693).sum := by decide
  have hdescent : baseEnd_1988693 < baseStart_1988693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988697 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 2, 4]
def baseStart_1988697 : Nat := 118140960795 + 1988697 * 2 ^ 59
def prefixEnd_1988697 : Nat := 4983230072969 + 3 ^ 40 * 1988697 * 2
def baseEnd_1988697 : Nat := 340385812384836982513885

theorem tailTrace_1988697 : CollatzResearch.WordTrace tailWord_1988697 prefixEnd_1988697 340385812384836982513885 := by
  unfold tailWord_1988697
  simp only [CollatzResearch.WordTrace]
  refine ⟨72533738476297886252396345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48355825650865257501597563 72533738476297886252396345)
  ·
    refine ⟨54400303857223414689297259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72533738476297886252396345 54400303857223414689297259)
    ·
      refine ⟨81600455785835122033945889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54400303857223414689297259 81600455785835122033945889)
      ·
        refine ⟨61200341839376341525459417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81600455785835122033945889 61200341839376341525459417)
        ·
          refine ⟨45900256379532256144094563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61200341839376341525459417 45900256379532256144094563)
          ·
            refine ⟨68850384569298384216141845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45900256379532256144094563 68850384569298384216141845)
            ·
              refine ⟨3227361776685861760131649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68850384569298384216141845 3227361776685861760131649)
              ·
                refine ⟨2420521332514396320098737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3227361776685861760131649 2420521332514396320098737)
                ·
                  refine ⟨1815390999385797240074053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2420521332514396320098737 1815390999385797240074053)
                  ·
                    refine ⟨340385812384836982513885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1815390999385797240074053 340385812384836982513885)
                    ·
                      rfl

theorem cell23_1988697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 4].length) (baseStart_1988697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988697 prefixEnd_1988697 := by exact prefixLift 1988697
  have htrace : WordTrace (prefixWord ++ tailWord_1988697) baseStart_1988697 baseEnd_1988697 := by
    simpa [prefixWord, tailWord_1988697, baseEnd_1988697] using wordTrace_append hprefix tailTrace_1988697
  have hstable : (prefixWord ++ tailWord_1988697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988697).length < 2 ^ (prefixWord ++ tailWord_1988697).sum := by decide
  have hdescent : baseEnd_1988697 < baseStart_1988697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988703 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_1988703 : Nat := 118140960795 + 1988703 * 2 ^ 59
def prefixEnd_1988703 : Nat := 4983230072969 + 3 ^ 40 * 1988703 * 2
def baseEnd_1988703 : Nat := 1021160518038437924066627

theorem tailTrace_1988703 : CollatzResearch.WordTrace tailWord_1988703 prefixEnd_1988703 1021160518038437924066627 := by
  unfold tailWord_1988703
  simp only [CollatzResearch.WordTrace]
  refine ⟨72533957314276149277114763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48355971542850766184743175 72533957314276149277114763)
  ·
    refine ⟨108800935971414223915672145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72533957314276149277114763 108800935971414223915672145)
    ·
      refine ⟨81600701978560667936754109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108800935971414223915672145 81600701978560667936754109)
      ·
        refine ⟨30600263241960250476282791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81600701978560667936754109 30600263241960250476282791)
        ·
          refine ⟨45900394862940375714424187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30600263241960250476282791 45900394862940375714424187)
          ·
            refine ⟨68850592294410563571636281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45900394862940375714424187 68850592294410563571636281)
            ·
              refine ⟨51637944220807922678727211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68850592294410563571636281 51637944220807922678727211)
              ·
                refine ⟨77456916331211884018090817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51637944220807922678727211 77456916331211884018090817)
                ·
                  refine ⟨58092687248408913013568113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77456916331211884018090817 58092687248408913013568113)
                  ·
                    refine ⟨43569515436306684760176085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58092687248408913013568113 43569515436306684760176085)
                    ·
                      refine ⟨1021160518038437924066627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43569515436306684760176085 1021160518038437924066627)
                      ·
                        rfl

theorem cell23_1988703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_1988703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988703 prefixEnd_1988703 := by exact prefixLift 1988703
  have htrace : WordTrace (prefixWord ++ tailWord_1988703) baseStart_1988703 baseEnd_1988703 := by
    simpa [prefixWord, tailWord_1988703, baseEnd_1988703] using wordTrace_append hprefix tailTrace_1988703
  have hstable : (prefixWord ++ tailWord_1988703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988703).length < 2 ^ (prefixWord ++ tailWord_1988703).sum := by decide
  have hdescent : baseEnd_1988703 < baseStart_1988703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988717 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1988717 : Nat := 118140960795 + 1988717 * 2 ^ 59
def prefixEnd_1988717 : Nat := 4983230072969 + 3 ^ 40 * 1988717 * 2
def baseEnd_1988717 : Nat := 1021167706767600869291563

theorem tailTrace_1988717 : CollatzResearch.WordTrace tailWord_1988717 prefixEnd_1988717 1021167706767600869291563 := by
  unfold tailWord_1988717
  simp only [CollatzResearch.WordTrace]
  refine ⟨72534467936225429668124405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48356311957483619778749603 72534467936225429668124405)
  ·
    refine ⟨6800106369021134031386663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72534467936225429668124405 6800106369021134031386663)
    ·
      refine ⟨10200159553531701047079995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6800106369021134031386663 10200159553531701047079995)
      ·
        refine ⟨15300239330297551570619993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10200159553531701047079995 15300239330297551570619993)
        ·
          refine ⟨11475179497723163677964995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15300239330297551570619993 11475179497723163677964995)
          ·
            refine ⟨17212769246584745516947493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11475179497723163677964995 17212769246584745516947493)
            ·
              refine ⟨3227394233734639784427655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17212769246584745516947493 3227394233734639784427655)
              ·
                refine ⟨4841091350601959676641483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227394233734639784427655 4841091350601959676641483)
                ·
                  refine ⟨7261637025902939514962225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841091350601959676641483 7261637025902939514962225)
                  ·
                    refine ⟨5446227769427204636221669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7261637025902939514962225 5446227769427204636221669)
                    ·
                      refine ⟨1021167706767600869291563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5446227769427204636221669 1021167706767600869291563)
                      ·
                        rfl

theorem cell23_1988717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1988717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988717 prefixEnd_1988717 := by exact prefixLift 1988717
  have htrace : WordTrace (prefixWord ++ tailWord_1988717) baseStart_1988717 baseEnd_1988717 := by
    simpa [prefixWord, tailWord_1988717, baseEnd_1988717] using wordTrace_append hprefix tailTrace_1988717
  have hstable : (prefixWord ++ tailWord_1988717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988717).length < 2 ^ (prefixWord ++ tailWord_1988717).sum := by decide
  have hdescent : baseEnd_1988717 < baseStart_1988717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988741 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 1, 2, 3]
def baseStart_1988741 : Nat := 118140960795 + 1988741 * 2 ^ 59
def prefixEnd_1988741 : Nat := 4983230072969 + 3 ^ 40 * 1988741 * 2
def baseEnd_1988741 : Nat := 1021180030303308775391453

theorem tailTrace_1988741 : CollatzResearch.WordTrace tailWord_1988741 prefixEnd_1988741 1021180030303308775391453 := by
  unfold tailWord_1988741
  simp only [CollatzResearch.WordTrace]
  refine ⟨72535343288138481766998077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48356895525425654511332051 72535343288138481766998077)
  ·
    refine ⟨27200753733051930662624279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72535343288138481766998077 27200753733051930662624279)
    ·
      refine ⟨40801130599577895993936419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27200753733051930662624279 40801130599577895993936419)
      ·
        refine ⟨61201695899366843990904629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40801130599577895993936419 61201695899366843990904629)
        ·
          refine ⟨5737658990565641624147309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61201695899366843990904629 5737658990565641624147309)
          ·
            refine ⟨2151622121462115609055241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5737658990565641624147309 2151622121462115609055241)
            ·
              refine ⟨1613716591096586706791431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151622121462115609055241 1613716591096586706791431)
              ·
                refine ⟨2420574886644880060187147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613716591096586706791431 2420574886644880060187147)
                ·
                  refine ⟨3630862329967320090280721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420574886644880060187147 3630862329967320090280721)
                  ·
                    refine ⟨2723146747475490067710541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3630862329967320090280721 2723146747475490067710541)
                    ·
                      refine ⟨1021180030303308775391453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2723146747475490067710541 1021180030303308775391453)
                      ·
                        rfl

theorem cell23_1988741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 2, 3].length) (baseStart_1988741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988741 prefixEnd_1988741 := by exact prefixLift 1988741
  have htrace : WordTrace (prefixWord ++ tailWord_1988741) baseStart_1988741 baseEnd_1988741 := by
    simpa [prefixWord, tailWord_1988741, baseEnd_1988741] using wordTrace_append hprefix tailTrace_1988741
  have hstable : (prefixWord ++ tailWord_1988741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988741).length < 2 ^ (prefixWord ++ tailWord_1988741).sum := by decide
  have hdescent : baseEnd_1988741 < baseStart_1988741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988754 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1988754 : Nat := 118140960795 + 1988754 * 2 ^ 59
def prefixEnd_1988754 : Nat := 4983230072969 + 3 ^ 40 * 1988754 * 2
def baseEnd_1988754 : Nat := 1021186705551817224528893

theorem tailTrace_1988754 : CollatzResearch.WordTrace tailWord_1988754 prefixEnd_1988754 1021186705551817224528893 := by
  unfold tailWord_1988754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18133954359272846246805329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48357211624727589991480877 18133954359272846246805329)
  ·
    refine ⟨13600465769454634685103997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18133954359272846246805329 13600465769454634685103997)
    ·
      refine ⟨5100174663545488006913999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13600465769454634685103997 5100174663545488006913999)
      ·
        refine ⟨7650261995318232010370999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5100174663545488006913999 7650261995318232010370999)
        ·
          refine ⟨11475392992977348015556499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7650261995318232010370999 11475392992977348015556499)
          ·
            refine ⟨17213089489466022023334749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11475392992977348015556499 17213089489466022023334749)
            ·
              refine ⟨6454908558549758258750531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17213089489466022023334749 6454908558549758258750531)
              ·
                refine ⟨9682362837824637388125797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454908558549758258750531 9682362837824637388125797)
                ·
                  refine ⟨1815443032092119510273587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9682362837824637388125797 1815443032092119510273587)
                  ·
                    refine ⟨2723164548138179265410381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1815443032092119510273587 2723164548138179265410381)
                    ·
                      refine ⟨1021186705551817224528893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2723164548138179265410381 1021186705551817224528893)
                      ·
                        rfl

theorem cell23_1988754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1988754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988754 prefixEnd_1988754 := by exact prefixLift 1988754
  have htrace : WordTrace (prefixWord ++ tailWord_1988754) baseStart_1988754 baseEnd_1988754 := by
    simpa [prefixWord, tailWord_1988754, baseEnd_1988754] using wordTrace_append hprefix tailTrace_1988754
  have hstable : (prefixWord ++ tailWord_1988754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988754).length < 2 ^ (prefixWord ++ tailWord_1988754).sum := by decide
  have hdescent : baseEnd_1988754 < baseStart_1988754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988780 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 3]
def baseStart_1988780 : Nat := 118140960795 + 1988780 * 2 ^ 59
def prefixEnd_1988780 : Nat := 4983230072969 + 3 ^ 40 * 1988780 * 2
def baseEnd_1988780 : Nat := 1021200056048834122803773

theorem tailTrace_1988780 : CollatzResearch.WordTrace tailWord_1988780 prefixEnd_1988780 1021200056048834122803773 := by
  unfold tailWord_1988780
  simp only [CollatzResearch.WordTrace]
  refine ⟨36268382867498595713833897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48357843823331460951778529 36268382867498595713833897)
  ·
    refine ⟨27201287150623946785375423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36268382867498595713833897 27201287150623946785375423)
    ·
      refine ⟨40801930725935920178063135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27201287150623946785375423 40801930725935920178063135)
      ·
        refine ⟨61202896088903880267094703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40801930725935920178063135 61202896088903880267094703)
        ·
          refine ⟨91804344133355820400642055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61202896088903880267094703 91804344133355820400642055)
          ·
            refine ⟨137706516200033730600963083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91804344133355820400642055 137706516200033730600963083)
            ·
              refine ⟨206559774300050595901444625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137706516200033730600963083 206559774300050595901444625)
              ·
                refine ⟨154919830725037946926083469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206559774300050595901444625 154919830725037946926083469)
                ·
                  refine ⟨58094936521889230097281301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154919830725037946926083469 58094936521889230097281301)
                  ·
                    refine ⟨2723200149463557660810061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58094936521889230097281301 2723200149463557660810061)
                    ·
                      refine ⟨1021200056048834122803773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2723200149463557660810061 1021200056048834122803773)
                      ·
                        rfl

theorem cell23_1988780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_1988780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988780 prefixEnd_1988780 := by exact prefixLift 1988780
  have htrace : WordTrace (prefixWord ++ tailWord_1988780) baseStart_1988780 baseEnd_1988780 := by
    simpa [prefixWord, tailWord_1988780, baseEnd_1988780] using wordTrace_append hprefix tailTrace_1988780
  have hstable : (prefixWord ++ tailWord_1988780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988780).length < 2 ^ (prefixWord ++ tailWord_1988780).sum := by decide
  have hdescent : baseEnd_1988780 < baseStart_1988780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988781 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_1988781 : Nat := 118140960795 + 1988781 * 2 ^ 59
def prefixEnd_1988781 : Nat := 4983230072969 + 3 ^ 40 * 1988781 * 2
def baseEnd_1988781 : Nat := 1021200569529488618891269

theorem tailTrace_1988781 : CollatzResearch.WordTrace tailWord_1988781 prefixEnd_1988781 1021200569529488618891269 := by
  unfold tailWord_1988781
  simp only [CollatzResearch.WordTrace]
  refine ⟨72536802207993568598454197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48357868138662379065636131 72536802207993568598454197)
  ·
    refine ⟨6800325206999397056105081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72536802207993568598454197 6800325206999397056105081)
    ·
      refine ⟨5100243905249547792078811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6800325206999397056105081 5100243905249547792078811)
      ·
        refine ⟨7650365857874321688118217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5100243905249547792078811 7650365857874321688118217)
        ·
          refine ⟨5737774393405741266088663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7650365857874321688118217 5737774393405741266088663)
          ·
            refine ⟨8606661590108611899132995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737774393405741266088663 8606661590108611899132995)
            ·
              refine ⟨12909992385162917848699493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8606661590108611899132995 12909992385162917848699493)
              ·
                refine ⟨2420623572218047096631155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12909992385162917848699493 2420623572218047096631155)
                ·
                  refine ⟨3630935358327070644946733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420623572218047096631155 3630935358327070644946733)
                  ·
                    refine ⟨1361600759372651491855025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630935358327070644946733 1361600759372651491855025)
                    ·
                      refine ⟨1021200569529488618891269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361600759372651491855025 1021200569529488618891269)
                      ·
                        rfl

theorem cell23_1988781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_1988781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988781 prefixEnd_1988781 := by exact prefixLift 1988781
  have htrace : WordTrace (prefixWord ++ tailWord_1988781) baseStart_1988781 baseEnd_1988781 := by
    simpa [prefixWord, tailWord_1988781, baseEnd_1988781] using wordTrace_append hprefix tailTrace_1988781
  have hstable : (prefixWord ++ tailWord_1988781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988781).length < 2 ^ (prefixWord ++ tailWord_1988781).sum := by decide
  have hdescent : baseEnd_1988781 < baseStart_1988781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988794 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2]
def baseStart_1988794 : Nat := 118140960795 + 1988794 * 2 ^ 59
def prefixEnd_1988794 : Nat := 4983230072969 + 3 ^ 40 * 1988794 * 2
def baseEnd_1988794 : Nat := 1021207244777997068028709

theorem tailTrace_1988794 : CollatzResearch.WordTrace tailWord_1988794 prefixEnd_1988794 1021207244777997068028709 := by
  unfold tailWord_1988794
  simp only [CollatzResearch.WordTrace]
  refine ⟨18134319089236617954669359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48358184237964314545784957 18134319089236617954669359)
  ·
    refine ⟨27201478633854926932004039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18134319089236617954669359 27201478633854926932004039)
    ·
      refine ⟨40802217950782390398006059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27201478633854926932004039 40802217950782390398006059)
      ·
        refine ⟨61203326926173585597009089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40802217950782390398006059 61203326926173585597009089)
        ·
          refine ⟨45902495194630189197756817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61203326926173585597009089 45902495194630189197756817)
          ·
            refine ⟨34426871395972641898317613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45902495194630189197756817 34426871395972641898317613)
            ·
              refine ⟨12910076773489740711869105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34426871395972641898317613 12910076773489740711869105)
              ·
                refine ⟨9682557580117305533901829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12910076773489740711869105 9682557580117305533901829)
                ·
                  refine ⟨1815479546271994787606593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9682557580117305533901829 1815479546271994787606593)
                  ·
                    refine ⟨1361609659703996090704945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1815479546271994787606593 1361609659703996090704945)
                    ·
                      refine ⟨1021207244777997068028709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361609659703996090704945 1021207244777997068028709)
                      ·
                        rfl

theorem cell23_1988794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2].length) (baseStart_1988794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988794 prefixEnd_1988794 := by exact prefixLift 1988794
  have htrace : WordTrace (prefixWord ++ tailWord_1988794) baseStart_1988794 baseEnd_1988794 := by
    simpa [prefixWord, tailWord_1988794, baseEnd_1988794] using wordTrace_append hprefix tailTrace_1988794
  have hstable : (prefixWord ++ tailWord_1988794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988794).length < 2 ^ (prefixWord ++ tailWord_1988794).sum := by decide
  have hdescent : baseEnd_1988794 < baseStart_1988794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988810 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_1988810 : Nat := 118140960795 + 1988810 * 2 ^ 59
def prefixEnd_1988810 : Nat := 4983230072969 + 3 ^ 40 * 1988810 * 2
def baseEnd_1988810 : Nat := 1021215460468469005428635

theorem tailTrace_1988810 : CollatzResearch.WordTrace tailWord_1988810 prefixEnd_1988810 1021215460468469005428635 := by
  unfold tailWord_1988810
  simp only [CollatzResearch.WordTrace]
  refine ⟨18134464981222126637814971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48358573283259004367506589 18134464981222126637814971)
  ·
    refine ⟨27201697471833189956722457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18134464981222126637814971 27201697471833189956722457)
    ·
      refine ⟨20401273103874892467541843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27201697471833189956722457 20401273103874892467541843)
      ·
        refine ⟨30601909655812338701312765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20401273103874892467541843 30601909655812338701312765)
        ·
          refine ⟨11475716120929627012992287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30601909655812338701312765 11475716120929627012992287)
          ·
            refine ⟨17213574181394440519488431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11475716120929627012992287 17213574181394440519488431)
            ·
              refine ⟨25820361272091660779232647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17213574181394440519488431 25820361272091660779232647)
              ·
                refine ⟨38730541908137491168848971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25820361272091660779232647 38730541908137491168848971)
                ·
                  refine ⟨58095812862206236753273457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38730541908137491168848971 58095812862206236753273457)
                  ·
                    refine ⟨43571859646654677564955093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58095812862206236753273457 43571859646654677564955093)
                    ·
                      refine ⟨1021215460468469005428635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43571859646654677564955093 1021215460468469005428635)
                      ·
                        rfl

theorem cell23_1988810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_1988810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988810 prefixEnd_1988810 := by exact prefixLift 1988810
  have htrace : WordTrace (prefixWord ++ tailWord_1988810) baseStart_1988810 baseEnd_1988810 := by
    simpa [prefixWord, tailWord_1988810, baseEnd_1988810] using wordTrace_append hprefix tailTrace_1988810
  have hstable : (prefixWord ++ tailWord_1988810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988810).length < 2 ^ (prefixWord ++ tailWord_1988810).sum := by decide
  have hdescent : baseEnd_1988810 < baseStart_1988810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988817 : List Nat := [1, 2, 2, 1, 2, 2, 2, 6, 5]
def baseStart_1988817 : Nat := 118140960795 + 1988817 * 2 ^ 59
def prefixEnd_1988817 : Nat := 4983230072969 + 3 ^ 40 * 1988817 * 2
def baseEnd_1988817 : Nat := 113468783870338942004567

theorem tailTrace_1988817 : CollatzResearch.WordTrace tailWord_1988817 prefixEnd_1988817 113468783870338942004567 := by
  unfold tailWord_1988817
  simp only [CollatzResearch.WordTrace]
  refine ⟨72538115235863146746764705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48358743490575431164509803 72538115235863146746764705)
  ·
    refine ⟨54403586426897360060073529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72538115235863146746764705 54403586426897360060073529)
    ·
      refine ⟨40802689820173020045055147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54403586426897360060073529 40802689820173020045055147)
      ·
        refine ⟨61204034730259530067582721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40802689820173020045055147 61204034730259530067582721)
        ·
          refine ⟨45903026047694647550687041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61204034730259530067582721 45903026047694647550687041)
          ·
            refine ⟨34427269535770985663015281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45903026047694647550687041 34427269535770985663015281)
            ·
              refine ⟨25820452151828239247261461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34427269535770985663015281 25820452151828239247261461)
              ·
                refine ⟨1210333694616948714715381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25820452151828239247261461 1210333694616948714715381)
                ·
                  refine ⟨113468783870338942004567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1210333694616948714715381 113468783870338942004567)
                  ·
                    rfl

theorem cell23_1988817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 5].length) (baseStart_1988817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988817 prefixEnd_1988817 := by exact prefixLift 1988817
  have htrace : WordTrace (prefixWord ++ tailWord_1988817) baseStart_1988817 baseEnd_1988817 := by
    simpa [prefixWord, tailWord_1988817, baseEnd_1988817] using wordTrace_append hprefix tailTrace_1988817
  have hstable : (prefixWord ++ tailWord_1988817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988817).length < 2 ^ (prefixWord ++ tailWord_1988817).sum := by decide
  have hdescent : baseEnd_1988817 < baseStart_1988817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988847 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 2, 5]
def baseStart_1988847 : Nat := 118140960795 + 1988847 * 2 ^ 59
def prefixEnd_1988847 : Nat := 4983230072969 + 3 ^ 40 * 1988847 * 2
def baseEnd_1988847 : Nat := 340411486417561786888655

theorem tailTrace_1988847 : CollatzResearch.WordTrace tailWord_1988847 prefixEnd_1988847 340411486417561786888655 := by
  unfold tailWord_1988847
  simp only [CollatzResearch.WordTrace]
  refine ⟨72539209425754461870356795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48359472950502974580237863 72539209425754461870356795)
  ·
    refine ⟨108808814138631692805535193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72539209425754461870356795 108808814138631692805535193)
    ·
      refine ⟨81606610603973769604151395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108808814138631692805535193 81606610603973769604151395)
      ·
        refine ⟨122409915905960654406227093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81606610603973769604151395 122409915905960654406227093)
        ·
          refine ⟨5737964808091905675291895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122409915905960654406227093 5737964808091905675291895)
          ·
            refine ⟨8606947212137858512937843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737964808091905675291895 8606947212137858512937843)
            ·
              refine ⟨12910420818206787769406765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8606947212137858512937843 12910420818206787769406765)
              ·
                refine ⟨4841407806827545413527537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12910420818206787769406765 4841407806827545413527537)
                ·
                  refine ⟨3631055855120659060145653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4841407806827545413527537 3631055855120659060145653)
                  ·
                    refine ⟨340411486417561786888655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3631055855120659060145653 340411486417561786888655)
                    ·
                      rfl

theorem cell23_1988847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_1988847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988847 prefixEnd_1988847 := by exact prefixLift 1988847
  have htrace : WordTrace (prefixWord ++ tailWord_1988847) baseStart_1988847 baseEnd_1988847 := by
    simpa [prefixWord, tailWord_1988847, baseEnd_1988847] using wordTrace_append hprefix tailTrace_1988847
  have hstable : (prefixWord ++ tailWord_1988847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988847).length < 2 ^ (prefixWord ++ tailWord_1988847).sum := by decide
  have hdescent : baseEnd_1988847 < baseStart_1988847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988867 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 4]
def baseStart_1988867 : Nat := 118140960795 + 1988867 * 2 ^ 59
def prefixEnd_1988867 : Nat := 4983230072969 + 3 ^ 40 * 1988867 * 2
def baseEnd_1988867 : Nat := 1021244728865775282415873

theorem tailTrace_1988867 : CollatzResearch.WordTrace tailWord_1988867 prefixEnd_1988867 1021244728865775282415873 := by
  unfold tailWord_1988867
  simp only [CollatzResearch.WordTrace]
  refine ⟨72539938885682005286084855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48359959257121336857389903 72539938885682005286084855)
  ·
    refine ⟨108809908328523007929127283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72539938885682005286084855 108809908328523007929127283)
    ·
      refine ⟨163214862492784511893690925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108809908328523007929127283 163214862492784511893690925)
      ·
        refine ⟨61205573434794191960134097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163214862492784511893690925 61205573434794191960134097)
        ·
          refine ⟨45904180076095643970100573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61205573434794191960134097 45904180076095643970100573)
          ·
            refine ⟨17214067528535866488787715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45904180076095643970100573 17214067528535866488787715)
            ·
              refine ⟨25821101292803799733181573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17214067528535866488787715 25821101292803799733181573)
              ·
                refine ⟨4841456492400712449971545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25821101292803799733181573 4841456492400712449971545)
                ·
                  refine ⟨3631092369300534337478659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4841456492400712449971545 3631092369300534337478659)
                  ·
                    refine ⟨5446638553950801506217989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3631092369300534337478659 5446638553950801506217989)
                    ·
                      refine ⟨1021244728865775282415873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5446638553950801506217989 1021244728865775282415873)
                      ·
                        rfl

theorem cell23_1988867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_1988867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988867 prefixEnd_1988867 := by exact prefixLift 1988867
  have htrace : WordTrace (prefixWord ++ tailWord_1988867) baseStart_1988867 baseEnd_1988867 := by
    simpa [prefixWord, tailWord_1988867, baseEnd_1988867] using wordTrace_append hprefix tailTrace_1988867
  have hstable : (prefixWord ++ tailWord_1988867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988867).length < 2 ^ (prefixWord ++ tailWord_1988867).sum := by decide
  have hdescent : baseEnd_1988867 < baseStart_1988867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988868 : List Nat := [2, 3, 2, 2, 3, 2, 2, 2, 5]
def baseStart_1988868 : Nat := 118140960795 + 1988868 * 2 ^ 59
def prefixEnd_1988868 : Nat := 4983230072969 + 3 ^ 40 * 1988868 * 2
def baseEnd_1988868 : Nat := 113471693594047753167041

theorem tailTrace_1988868 : CollatzResearch.WordTrace tailWord_1988868 prefixEnd_1988868 113471693594047753167041 := by
  unfold tailWord_1988868
  simp only [CollatzResearch.WordTrace]
  refine ⟨36269987679339191228435629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48359983572452254971247505 36269987679339191228435629)
  ·
    refine ⟨13601245379752196710663361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36269987679339191228435629 13601245379752196710663361)
    ·
      refine ⟨10200934034814147532997521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13601245379752196710663361 10200934034814147532997521)
      ·
        refine ⟨7650700526110610649748141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10200934034814147532997521 7650700526110610649748141)
        ·
          refine ⟨2869012697291478993655553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7650700526110610649748141 2869012697291478993655553)
          ·
            refine ⟨2151759522968609245241665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2869012697291478993655553 2151759522968609245241665)
            ·
              refine ⟨1613819642226456933931249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151759522968609245241665 1613819642226456933931249)
              ·
                refine ⟨1210364731669842700448437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1613819642226456933931249 1210364731669842700448437)
                ·
                  refine ⟨113471693594047753167041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1210364731669842700448437 113471693594047753167041)
                  ·
                    rfl

theorem cell23_1988868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_1988868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988868 prefixEnd_1988868 := by exact prefixLift 1988868
  have htrace : WordTrace (prefixWord ++ tailWord_1988868) baseStart_1988868 baseEnd_1988868 := by
    simpa [prefixWord, tailWord_1988868, baseEnd_1988868] using wordTrace_append hprefix tailTrace_1988868
  have hstable : (prefixWord ++ tailWord_1988868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988868).length < 2 ^ (prefixWord ++ tailWord_1988868).sum := by decide
  have hdescent : baseEnd_1988868 < baseStart_1988868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988901 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 4]
def baseStart_1988901 : Nat := 118140960795 + 1988901 * 2 ^ 59
def prefixEnd_1988901 : Nat := 4983230072969 + 3 ^ 40 * 1988901 * 2
def baseEnd_1988901 : Nat := 1021262187208028149390717

theorem tailTrace_1988901 : CollatzResearch.WordTrace tailWord_1988901 prefixEnd_1988901 1021262187208028149390717 := by
  unfold tailWord_1988901
  simp only [CollatzResearch.WordTrace]
  refine ⟨72541178967558829092822557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48360785978372552728548371 72541178967558829092822557)
  ·
    refine ⟨27202942112834560909808459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72541178967558829092822557 27202942112834560909808459)
    ·
      refine ⟨40804413169251841364712689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27202942112834560909808459 40804413169251841364712689)
      ·
        refine ⟨30603309876938881023534517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40804413169251841364712689 30603309876938881023534517)
        ·
          refine ⟨2869060300963020095956361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30603309876938881023534517 2869060300963020095956361)
          ·
            refine ⟨2151795225722265071967271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2869060300963020095956361 2151795225722265071967271)
            ·
              refine ⟨3227692838583397607950907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151795225722265071967271 3227692838583397607950907)
              ·
                refine ⟨4841539257875096411926361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227692838583397607950907 4841539257875096411926361)
                ·
                  refine ⟨3631154443406322308944771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4841539257875096411926361 3631154443406322308944771)
                  ·
                    refine ⟨5446731665109483463417157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3631154443406322308944771 5446731665109483463417157)
                    ·
                      refine ⟨1021262187208028149390717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5446731665109483463417157 1021262187208028149390717)
                      ·
                        rfl

theorem cell23_1988901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_1988901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988901 prefixEnd_1988901 := by exact prefixLift 1988901
  have htrace : WordTrace (prefixWord ++ tailWord_1988901) baseStart_1988901 baseEnd_1988901 := by
    simpa [prefixWord, tailWord_1988901, baseEnd_1988901] using wordTrace_append hprefix tailTrace_1988901
  have hstable : (prefixWord ++ tailWord_1988901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988901).length < 2 ^ (prefixWord ++ tailWord_1988901).sum := by decide
  have hdescent : baseEnd_1988901 < baseStart_1988901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988944 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 1, 5, 2]
def baseStart_1988944 : Nat := 118140960795 + 1988944 * 2 ^ 59
def prefixEnd_1988944 : Nat := 4983230072969 + 3 ^ 40 * 1988944 * 2
def baseEnd_1988944 : Nat := 1021284266876171481153019

theorem tailTrace_1988944 : CollatzResearch.WordTrace tailWord_1988944 prefixEnd_1988944 1021284266876171481153019 := by
  unfold tailWord_1988944
  simp only [CollatzResearch.WordTrace]
  refine ⟨36271373653201523718318943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48361831537602031624425257 36271373653201523718318943)
  ·
    refine ⟨54407060479802285577478415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36271373653201523718318943 54407060479802285577478415)
    ·
      refine ⟨81610590719703428366217623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54407060479802285577478415 81610590719703428366217623)
      ·
        refine ⟨122415886079555142549326435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81610590719703428366217623 122415886079555142549326435)
        ·
          refine ⟨183623829119332713823989653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122415886079555142549326435 183623829119332713823989653)
          ·
            refine ⟨8607366989968720960499515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 183623829119332713823989653 8607366989968720960499515)
            ·
              refine ⟨12911050484953081440749273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8607366989968720960499515 12911050484953081440749273)
              ·
                refine ⟨9683287863714811080561955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12911050484953081440749273 9683287863714811080561955)
                ·
                  refine ⟨14524931795572216620842933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9683287863714811080561955 14524931795572216620842933)
                  ·
                    refine ⟨1361712355834895308204025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14524931795572216620842933 1361712355834895308204025)
                    ·
                      refine ⟨1021284266876171481153019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361712355834895308204025 1021284266876171481153019)
                      ·
                        rfl

theorem cell23_1988944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 5, 2].length) (baseStart_1988944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988944 prefixEnd_1988944 := by exact prefixLift 1988944
  have htrace : WordTrace (prefixWord ++ tailWord_1988944) baseStart_1988944 baseEnd_1988944 := by
    simpa [prefixWord, tailWord_1988944, baseEnd_1988944] using wordTrace_append hprefix tailTrace_1988944
  have hstable : (prefixWord ++ tailWord_1988944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988944).length < 2 ^ (prefixWord ++ tailWord_1988944).sum := by decide
  have hdescent : baseEnd_1988944 < baseStart_1988944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988987 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 6]
def baseStart_1988987 : Nat := 118140960795 + 1988987 * 2 ^ 59
def prefixEnd_1988987 : Nat := 4983230072969 + 3 ^ 40 * 1988987 * 2
def baseEnd_1988987 : Nat := 1021306346544314812915321

theorem tailTrace_1988987 : CollatzResearch.WordTrace tailWord_1988987 prefixEnd_1988987 1021306346544314812915321 := by
  unfold tailWord_1988987
  simp only [CollatzResearch.WordTrace]
  refine ⟨72544315645247265780453215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48362877096831510520302143 72544315645247265780453215)
  ·
    refine ⟨108816473467870898670679823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72544315645247265780453215 108816473467870898670679823)
    ·
      refine ⟨163224710201806348006019735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108816473467870898670679823 163224710201806348006019735)
      ·
        refine ⟨244837065302709522009029603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163224710201806348006019735 244837065302709522009029603)
        ·
          refine ⟨367255597954064283013544405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244837065302709522009029603 367255597954064283013544405)
          ·
            refine ⟨8607553077048381633129947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 367255597954064283013544405 8607553077048381633129947)
            ·
              refine ⟨12911329615572572449694921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8607553077048381633129947 12911329615572572449694921)
              ·
                refine ⟨9683497211679429337271191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12911329615572572449694921 9683497211679429337271191)
                ·
                  refine ⟨14525245817519144005906787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9683497211679429337271191 14525245817519144005906787)
                  ·
                    refine ⟨21787868726278716008860181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14525245817519144005906787 21787868726278716008860181)
                    ·
                      refine ⟨1021306346544314812915321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21787868726278716008860181 1021306346544314812915321)
                      ·
                        rfl

theorem cell23_1988987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 6].length) (baseStart_1988987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1988987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1988987 prefixEnd_1988987 := by exact prefixLift 1988987
  have htrace : WordTrace (prefixWord ++ tailWord_1988987) baseStart_1988987 baseEnd_1988987 := by
    simpa [prefixWord, tailWord_1988987, baseEnd_1988987] using wordTrace_append hprefix tailTrace_1988987
  have hstable : (prefixWord ++ tailWord_1988987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988987).length < 2 ^ (prefixWord ++ tailWord_1988987).sum := by decide
  have hdescent : baseEnd_1988987 < baseStart_1988987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989001 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 2, 4]
def baseStart_1989001 : Nat := 118140960795 + 1989001 * 2 ^ 59
def prefixEnd_1989001 : Nat := 4983230072969 + 3 ^ 40 * 1989001 * 2
def baseEnd_1989001 : Nat := 340437845091159252713419

theorem tailTrace_1989001 : CollatzResearch.WordTrace tailWord_1989001 prefixEnd_1989001 340437845091159252713419 := by
  unfold tailWord_1989001
  simp only [CollatzResearch.WordTrace]
  refine ⟨72544826267196546171462857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48363217511464364114308571 72544826267196546171462857)
  ·
    refine ⟨54408619700397409628597143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72544826267196546171462857 54408619700397409628597143)
    ·
      refine ⟨81612929550596114442895715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54408619700397409628597143 81612929550596114442895715)
      ·
        refine ⟨122419394325894171664343573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81612929550596114442895715 122419394325894171664343573)
        ·
          refine ⟨5738409109026289296766105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122419394325894171664343573 5738409109026289296766105)
          ·
            refine ⟨4303806831769716972574579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5738409109026289296766105 4303806831769716972574579)
            ·
              refine ⟨6455710247654575458861869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303806831769716972574579 6455710247654575458861869)
              ·
                refine ⟨2420891342870465797073201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6455710247654575458861869 2420891342870465797073201)
                ·
                  refine ⟨1815668507152849347804901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2420891342870465797073201 1815668507152849347804901)
                  ·
                    refine ⟨340437845091159252713419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1815668507152849347804901 340437845091159252713419)
                    ·
                      rfl

theorem cell23_1989001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 4].length) (baseStart_1989001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989001 prefixEnd_1989001 := by exact prefixLift 1989001
  have htrace : WordTrace (prefixWord ++ tailWord_1989001) baseStart_1989001 baseEnd_1989001 := by
    simpa [prefixWord, tailWord_1989001, baseEnd_1989001] using wordTrace_append hprefix tailTrace_1989001
  have hstable : (prefixWord ++ tailWord_1989001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989001).length < 2 ^ (prefixWord ++ tailWord_1989001).sum := by decide
  have hdescent : baseEnd_1989001 < baseStart_1989001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989021 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1989021 : Nat := 118140960795 + 1989021 * 2 ^ 59
def prefixEnd_1989021 : Nat := 4983230072969 + 3 ^ 40 * 1989021 * 2
def baseEnd_1989021 : Nat := 1021323804886567679890165

theorem tailTrace_1989021 : CollatzResearch.WordTrace tailWord_1989021 prefixEnd_1989021 1021323804886567679890165 := by
  unfold tailWord_1989021
  simp only [CollatzResearch.WordTrace]
  refine ⟨72545555727124089587190917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48363703818082726391460611 72545555727124089587190917)
  ·
    refine ⟨13602291698835766797598297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72545555727124089587190917 13602291698835766797598297)
    ·
      refine ⟨10201718774126825098198723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13602291698835766797598297 10201718774126825098198723)
      ·
        refine ⟨15302578161190237647298085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10201718774126825098198723 15302578161190237647298085)
        ·
          refine ⟨2869233405223169558868391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15302578161190237647298085 2869233405223169558868391)
          ·
            refine ⟨4303850107834754338302587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2869233405223169558868391 4303850107834754338302587)
            ·
              refine ⟨6455775161752131507453881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303850107834754338302587 6455775161752131507453881)
              ·
                refine ⟨4841831371314098630590411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6455775161752131507453881 4841831371314098630590411)
                ·
                  refine ⟨7262747056971147945885617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841831371314098630590411 7262747056971147945885617)
                  ·
                    refine ⟨5447060292728360959414213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7262747056971147945885617 5447060292728360959414213)
                    ·
                      refine ⟨1021323804886567679890165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5447060292728360959414213 1021323804886567679890165)
                      ·
                        rfl

theorem cell23_1989021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1989021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989021 prefixEnd_1989021 := by exact prefixLift 1989021
  have htrace : WordTrace (prefixWord ++ tailWord_1989021) baseStart_1989021 baseEnd_1989021 := by
    simpa [prefixWord, tailWord_1989021, baseEnd_1989021] using wordTrace_append hprefix tailTrace_1989021
  have hstable : (prefixWord ++ tailWord_1989021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989021).length < 2 ^ (prefixWord ++ tailWord_1989021).sum := by decide
  have hdescent : baseEnd_1989021 < baseStart_1989021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989024 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 3]
def baseStart_1989024 : Nat := 118140960795 + 1989024 * 2 ^ 59
def prefixEnd_1989024 : Nat := 4983230072969 + 3 ^ 40 * 1989024 * 2
def baseEnd_1989024 : Nat := 1021325345328531168152651

theorem tailTrace_1989024 : CollatzResearch.WordTrace tailWord_1989024 prefixEnd_1989024 1021325345328531168152651 := by
  unfold tailWord_1989024
  simp only [CollatzResearch.WordTrace]
  refine ⟨36272832573056610549775063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48363776764075480733033417 36272832573056610549775063)
  ·
    refine ⟨54409248859584915824662595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36272832573056610549775063 54409248859584915824662595)
    ·
      refine ⟨81613873289377373736993893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54409248859584915824662595 81613873289377373736993893)
      ·
        refine ⟨15302601241758257575686355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81613873289377373736993893 15302601241758257575686355)
        ·
          refine ⟨22953901862637386363529533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15302601241758257575686355 22953901862637386363529533)
          ·
            refine ⟨8607713198489019886323575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22953901862637386363529533 8607713198489019886323575)
            ·
              refine ⟨12911569797733529829485363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8607713198489019886323575 12911569797733529829485363)
              ·
                refine ⟨19367354696600294744228045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12911569797733529829485363 19367354696600294744228045)
                ·
                  refine ⟨7262758011225110529085517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19367354696600294744228045 7262758011225110529085517)
                  ·
                    refine ⟨2723534254209416448407069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7262758011225110529085517 2723534254209416448407069)
                    ·
                      refine ⟨1021325345328531168152651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2723534254209416448407069 1021325345328531168152651)
                      ·
                        rfl

theorem cell23_1989024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_1989024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989024 prefixEnd_1989024 := by exact prefixLift 1989024
  have htrace : WordTrace (prefixWord ++ tailWord_1989024) baseStart_1989024 baseEnd_1989024 := by
    simpa [prefixWord, tailWord_1989024, baseEnd_1989024] using wordTrace_append hprefix tailTrace_1989024
  have hstable : (prefixWord ++ tailWord_1989024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989024).length < 2 ^ (prefixWord ++ tailWord_1989024).sum := by decide
  have hdescent : baseEnd_1989024 < baseStart_1989024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989025 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1989025 : Nat := 118140960795 + 1989025 * 2 ^ 59
def prefixEnd_1989025 : Nat := 4983230072969 + 3 ^ 40 * 1989025 * 2
def baseEnd_1989025 : Nat := 1021325858809185664240147

theorem tailTrace_1989025 : CollatzResearch.WordTrace tailWord_1989025 prefixEnd_1989025 1021325858809185664240147 := by
  unfold tailWord_1989025
  simp only [CollatzResearch.WordTrace]
  refine ⟨72545701619109598270336529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48363801079406398846891019 72545701619109598270336529)
  ·
    refine ⟨54409276214332198702752397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72545701619109598270336529 54409276214332198702752397)
    ·
      refine ⟨20403478580374574513532149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54409276214332198702752397 20403478580374574513532149)
      ·
        refine ⟨1912826116910116360643639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20403478580374574513532149 1912826116910116360643639)
        ·
          refine ⟨2869239175365174540965459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912826116910116360643639 2869239175365174540965459)
          ·
            refine ⟨4303858763047761811448189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2869239175365174540965459 4303858763047761811448189)
            ·
              refine ⟨1613947036142910679293071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4303858763047761811448189 1613947036142910679293071)
              ·
                refine ⟨2420920554214366018939607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613947036142910679293071 2420920554214366018939607)
                ·
                  refine ⟨3631380831321549028409411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420920554214366018939607 3631380831321549028409411)
                  ·
                    refine ⟨5447071246982323542614117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3631380831321549028409411 5447071246982323542614117)
                    ·
                      refine ⟨1021325858809185664240147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5447071246982323542614117 1021325858809185664240147)
                      ·
                        rfl

theorem cell23_1989025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1989025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989025 prefixEnd_1989025 := by exact prefixLift 1989025
  have htrace : WordTrace (prefixWord ++ tailWord_1989025) baseStart_1989025 baseEnd_1989025 := by
    simpa [prefixWord, tailWord_1989025, baseEnd_1989025] using wordTrace_append hprefix tailTrace_1989025
  have hstable : (prefixWord ++ tailWord_1989025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989025).length < 2 ^ (prefixWord ++ tailWord_1989025).sum := by decide
  have hdescent : baseEnd_1989025 < baseStart_1989025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989081 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 1, 4, 2]
def baseStart_1989081 : Nat := 118140960795 + 1989081 * 2 ^ 59
def prefixEnd_1989081 : Nat := 4983230072969 + 3 ^ 40 * 1989081 * 2
def baseEnd_1989081 : Nat := 1021354613725837445139889

theorem tailTrace_1989081 : CollatzResearch.WordTrace tailWord_1989081 prefixEnd_1989081 1021354613725837445139889 := by
  unfold tailWord_1989081
  simp only [CollatzResearch.WordTrace]
  refine ⟨72547744106906719834375097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48365162737937813222916731 72547744106906719834375097)
  ·
    refine ⟨54410808080180039875781323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72547744106906719834375097 54410808080180039875781323)
    ·
      refine ⟨81616212120270059813671985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54410808080180039875781323 81616212120270059813671985)
      ·
        refine ⟨61212159090202544860253989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81616212120270059813671985 61212159090202544860253989)
        ·
          refine ⟨11477279829412977161297623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61212159090202544860253989 11477279829412977161297623)
          ·
            refine ⟨17215919744119465741946435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11477279829412977161297623 17215919744119465741946435)
            ·
              refine ⟨25823879616179198612919653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17215919744119465741946435 25823879616179198612919653)
              ·
                refine ⟨4841977428033599739922435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25823879616179198612919653 4841977428033599739922435)
                ·
                  refine ⟨7262966142050399609883653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841977428033599739922435 7262966142050399609883653)
                  ·
                    refine ⟨1361806151634449926853185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7262966142050399609883653 1361806151634449926853185)
                    ·
                      refine ⟨1021354613725837445139889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361806151634449926853185 1021354613725837445139889)
                      ·
                        rfl

theorem cell23_1989081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 4, 2].length) (baseStart_1989081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989081 prefixEnd_1989081 := by exact prefixLift 1989081
  have htrace : WordTrace (prefixWord ++ tailWord_1989081) baseStart_1989081 baseEnd_1989081 := by
    simpa [prefixWord, tailWord_1989081, baseEnd_1989081] using wordTrace_append hprefix tailTrace_1989081
  have hstable : (prefixWord ++ tailWord_1989081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989081).length < 2 ^ (prefixWord ++ tailWord_1989081).sum := by decide
  have hdescent : baseEnd_1989081 < baseStart_1989081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989097 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_1989097 : Nat := 118140960795 + 1989097 * 2 ^ 59
def prefixEnd_1989097 : Nat := 4983230072969 + 3 ^ 40 * 1989097 * 2
def baseEnd_1989097 : Nat := 1021362829416309382539815

theorem tailTrace_1989097 : CollatzResearch.WordTrace tailWord_1989097 prefixEnd_1989097 1021362829416309382539815 := by
  unfold tailWord_1989097
  simp only [CollatzResearch.WordTrace]
  refine ⟨72548327674848754566957545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48365551783232503044638363 72548327674848754566957545)
  ·
    refine ⟨54411245756136565925218159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72548327674848754566957545 54411245756136565925218159)
    ·
      refine ⟨81616868634204848887827239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54411245756136565925218159 81616868634204848887827239)
      ·
        refine ⟨122425302951307273331740859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81616868634204848887827239 122425302951307273331740859)
        ·
          refine ⟨183637954426960909997611289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122425302951307273331740859 183637954426960909997611289)
          ·
            refine ⟨137728465820220682498208467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183637954426960909997611289 137728465820220682498208467)
            ·
              refine ⟨206592698730331023747312701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137728465820220682498208467 206592698730331023747312701)
              ·
                refine ⟨77472262023874133905242263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206592698730331023747312701 77472262023874133905242263)
                ·
                  refine ⟨116208393035811200857863395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77472262023874133905242263 116208393035811200857863395)
                  ·
                    refine ⟨174312589553716801286795093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116208393035811200857863395 174312589553716801286795093)
                    ·
                      refine ⟨1021362829416309382539815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 174312589553716801286795093 1021362829416309382539815)
                      ·
                        rfl

theorem cell23_1989097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_1989097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989097 prefixEnd_1989097 := by exact prefixLift 1989097
  have htrace : WordTrace (prefixWord ++ tailWord_1989097) baseStart_1989097 baseEnd_1989097 := by
    simpa [prefixWord, tailWord_1989097, baseEnd_1989097] using wordTrace_append hprefix tailTrace_1989097
  have hstable : (prefixWord ++ tailWord_1989097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989097).length < 2 ^ (prefixWord ++ tailWord_1989097).sum := by decide
  have hdescent : baseEnd_1989097 < baseStart_1989097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989104 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 7]
def baseStart_1989104 : Nat := 118140960795 + 1989104 * 2 ^ 59
def prefixEnd_1989104 : Nat := 4983230072969 + 3 ^ 40 * 1989104 * 2
def baseEnd_1989104 : Nat := 113485158197876761683587

theorem tailTrace_1989104 : CollatzResearch.WordTrace tailWord_1989104 prefixEnd_1989104 113485158197876761683587 := by
  unfold tailWord_1989104
  simp only [CollatzResearch.WordTrace]
  refine ⟨36274291492911697381231183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48365721990548929841641577 36274291492911697381231183)
  ·
    refine ⟨54411437239367546071846775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36274291492911697381231183 54411437239367546071846775)
    ·
      refine ⟨81617155859051319107770163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54411437239367546071846775 81617155859051319107770163)
      ·
        refine ⟨122425733788576978661655245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81617155859051319107770163 122425733788576978661655245)
        ·
          refine ⟨45909650170716366998120717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122425733788576978661655245 45909650170716366998120717)
          ·
            refine ⟨17216118814018637624295269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45909650170716366998120717 17216118814018637624295269)
            ·
              refine ⟨3228022277628494554555363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17216118814018637624295269 3228022277628494554555363)
              ·
                refine ⟨4842033416442741831833045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3228022277628494554555363 4842033416442741831833045)
                ·
                  refine ⟨113485158197876761683587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4842033416442741831833045 113485158197876761683587)
                  ·
                    rfl

theorem cell23_1989104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 7].length) (baseStart_1989104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989104 prefixEnd_1989104 := by exact prefixLift 1989104
  have htrace : WordTrace (prefixWord ++ tailWord_1989104) baseStart_1989104 baseEnd_1989104 := by
    simpa [prefixWord, tailWord_1989104, baseEnd_1989104] using wordTrace_append hprefix tailTrace_1989104
  have hstable : (prefixWord ++ tailWord_1989104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989104).length < 2 ^ (prefixWord ++ tailWord_1989104).sum := by decide
  have hdescent : baseEnd_1989104 < baseStart_1989104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989114 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3]
def baseStart_1989114 : Nat := 118140960795 + 1989114 * 2 ^ 59
def prefixEnd_1989114 : Nat := 4983230072969 + 3 ^ 40 * 1989114 * 2
def baseEnd_1989114 : Nat := 1021371558587435816027237

theorem tailTrace_1989114 : CollatzResearch.WordTrace tailWord_1989114 prefixEnd_1989114 1021371558587435816027237 := by
  unfold tailWord_1989114
  simp only [CollatzResearch.WordTrace]
  refine ⟨18137236928946791617581599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48365965143858110980217597 18137236928946791617581599)
  ·
    refine ⟨27205855393420187426372399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18137236928946791617581599 27205855393420187426372399)
    ·
      refine ⟨40808783090130281139558599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27205855393420187426372399 40808783090130281139558599)
      ·
        refine ⟨61213174635195421709337899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40808783090130281139558599 61213174635195421709337899)
        ·
          refine ⟨91819761952793132564006849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61213174635195421709337899 91819761952793132564006849)
          ·
            refine ⟨68864821464594849423005137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91819761952793132564006849 68864821464594849423005137)
            ·
              refine ⟨51648616098446137067253853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68864821464594849423005137 51648616098446137067253853)
              ·
                refine ⟨19368231036917301400220195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51648616098446137067253853 19368231036917301400220195)
                ·
                  refine ⟨29052346555375952100330293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19368231036917301400220195 29052346555375952100330293)
                  ·
                    refine ⟨2723657489566495509405965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29052346555375952100330293 2723657489566495509405965)
                    ·
                      refine ⟨1021371558587435816027237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2723657489566495509405965 1021371558587435816027237)
                      ·
                        rfl

theorem cell23_1989114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_1989114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989114 prefixEnd_1989114 := by exact prefixLift 1989114
  have htrace : WordTrace (prefixWord ++ tailWord_1989114) baseStart_1989114 baseEnd_1989114 := by
    simpa [prefixWord, tailWord_1989114, baseEnd_1989114] using wordTrace_append hprefix tailTrace_1989114
  have hstable : (prefixWord ++ tailWord_1989114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989114).length < 2 ^ (prefixWord ++ tailWord_1989114).sum := by decide
  have hdescent : baseEnd_1989114 < baseStart_1989114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989166 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_1989166 : Nat := 118140960795 + 1989166 * 2 ^ 59
def prefixEnd_1989166 : Nat := 4983230072969 + 3 ^ 40 * 1989166 * 2
def baseEnd_1989166 : Nat := 1021398259581469612576999

theorem tailTrace_1989166 : CollatzResearch.WordTrace tailWord_1989166 prefixEnd_1989166 1021398259581469612576999 := by
  unfold tailWord_1989166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9068855538949847418902419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48367229541065852900812901 9068855538949847418902419)
  ·
    refine ⟨13603283308424771128353629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9068855538949847418902419 13603283308424771128353629)
    ·
      refine ⟨5101231240659289173132611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13603283308424771128353629 5101231240659289173132611)
      ·
        refine ⟨7651846860988933759698917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5101231240659289173132611 7651846860988933759698917)
        ·
          refine ⟨1434721286435425079943547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7651846860988933759698917 1434721286435425079943547)
          ·
            refine ⟨2152081929653137619915321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434721286435425079943547 2152081929653137619915321)
            ·
              refine ⟨1614061447239853214936491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2152081929653137619915321 1614061447239853214936491)
              ·
                refine ⟨2421092170859779822404737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614061447239853214936491 2421092170859779822404737)
                ·
                  refine ⟨1815819128144834866803553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2421092170859779822404737 1815819128144834866803553)
                  ·
                    refine ⟨1361864346108626150102665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1815819128144834866803553 1361864346108626150102665)
                    ·
                      refine ⟨1021398259581469612576999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361864346108626150102665 1021398259581469612576999)
                      ·
                        rfl

theorem cell23_1989166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_1989166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989166 prefixEnd_1989166 := by exact prefixLift 1989166
  have htrace : WordTrace (prefixWord ++ tailWord_1989166) baseStart_1989166 baseEnd_1989166 := by
    simpa [prefixWord, tailWord_1989166, baseEnd_1989166] using wordTrace_append hprefix tailTrace_1989166
  have hstable : (prefixWord ++ tailWord_1989166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989166).length < 2 ^ (prefixWord ++ tailWord_1989166).sum := by decide
  have hdescent : baseEnd_1989166 < baseStart_1989166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989171 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 1, 6, 2]
def baseStart_1989171 : Nat := 118140960795 + 1989171 * 2 ^ 59
def prefixEnd_1989171 : Nat := 4983230072969 + 3 ^ 40 * 1989171 * 2
def baseEnd_1989171 : Nat := 1021400826984742093014475

theorem tailTrace_1989171 : CollatzResearch.WordTrace tailWord_1989171 prefixEnd_1989171 1021400826984742093014475 := by
  unfold tailWord_1989171
  simp only [CollatzResearch.WordTrace]
  refine ⟨72551026676580665205151367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48367351117720443470100911 72551026676580665205151367)
  ·
    refine ⟨108826540014870997807727051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72551026676580665205151367 108826540014870997807727051)
    ·
      refine ⟨163239810022306496711590577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108826540014870997807727051 163239810022306496711590577)
      ·
        refine ⟨122429857516729872533692933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163239810022306496711590577 122429857516729872533692933)
        ·
          refine ⟨22955598284386851100067425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122429857516729872533692933 22955598284386851100067425)
          ·
            refine ⟨17216698713290138325050569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22955598284386851100067425 17216698713290138325050569)
            ·
              refine ⟨12912524034967603743787927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17216698713290138325050569 12912524034967603743787927)
              ·
                refine ⟨19368786052451405615681891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12912524034967603743787927 19368786052451405615681891)
                ·
                  refine ⟨29053179078677108423522837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19368786052451405615681891 29053179078677108423522837)
                  ·
                    refine ⟨1361867769312989457352633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29053179078677108423522837 1361867769312989457352633)
                    ·
                      refine ⟨1021400826984742093014475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361867769312989457352633 1021400826984742093014475)
                      ·
                        rfl

theorem cell23_1989171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 6, 2].length) (baseStart_1989171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989171 prefixEnd_1989171 := by exact prefixLift 1989171
  have htrace : WordTrace (prefixWord ++ tailWord_1989171) baseStart_1989171 baseEnd_1989171 := by
    simpa [prefixWord, tailWord_1989171, baseEnd_1989171] using wordTrace_append hprefix tailTrace_1989171
  have hstable : (prefixWord ++ tailWord_1989171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989171).length < 2 ^ (prefixWord ++ tailWord_1989171).sum := by decide
  have hdescent : baseEnd_1989171 < baseStart_1989171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989184 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 4]
def baseStart_1989184 : Nat := 118140960795 + 1989184 * 2 ^ 59
def prefixEnd_1989184 : Nat := 4983230072969 + 3 ^ 40 * 1989184 * 2
def baseEnd_1989184 : Nat := 1021407502233250542151915

theorem tailTrace_1989184 : CollatzResearch.WordTrace tailWord_1989184 prefixEnd_1989184 1021407502233250542151915 := by
  unfold tailWord_1989184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36275750412766784212687303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48367667217022378950249737 36275750412766784212687303)
  ·
    refine ⟨54413625619150176319030955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36275750412766784212687303 54413625619150176319030955)
    ·
      refine ⟨81620438428725264478546433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54413625619150176319030955 81620438428725264478546433)
      ·
        refine ⟨61215328821543948358909825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81620438428725264478546433 61215328821543948358909825)
        ·
          refine ⟨45911496616157961269182369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61215328821543948358909825 45911496616157961269182369)
          ·
            refine ⟨34433622462118470951886777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45911496616157961269182369 34433622462118470951886777)
            ·
              refine ⟨25825216846588853213915083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34433622462118470951886777 25825216846588853213915083)
              ·
                refine ⟨38737825269883279820872625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25825216846588853213915083 38737825269883279820872625)
                ·
                  refine ⟨29053368952412459865654469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38737825269883279820872625 29053368952412459865654469)
                  ·
                    refine ⟨5447506678577336224810213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29053368952412459865654469 5447506678577336224810213)
                    ·
                      refine ⟨1021407502233250542151915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5447506678577336224810213 1021407502233250542151915)
                      ·
                        rfl

theorem cell23_1989184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_1989184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989184 prefixEnd_1989184 := by exact prefixLift 1989184
  have htrace : WordTrace (prefixWord ++ tailWord_1989184) baseStart_1989184 baseEnd_1989184 := by
    simpa [prefixWord, tailWord_1989184, baseEnd_1989184] using wordTrace_append hprefix tailTrace_1989184
  have hstable : (prefixWord ++ tailWord_1989184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989184).length < 2 ^ (prefixWord ++ tailWord_1989184).sum := by decide
  have hdescent : baseEnd_1989184 < baseStart_1989184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989241 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 3, 5]
def baseStart_1989241 : Nat := 118140960795 + 1989241 * 2 ^ 59
def prefixEnd_1989241 : Nat := 4983230072969 + 3 ^ 40 * 1989241 * 2
def baseEnd_1989241 : Nat := 340478923543518939713051

theorem tailTrace_1989241 : CollatzResearch.WordTrace tailWord_1989241 prefixEnd_1989241 340478923543518939713051 := by
  unfold tailWord_1989241
  simp only [CollatzResearch.WordTrace]
  refine ⟨72553579786327067160199577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48369053190884711440133051 72553579786327067160199577)
  ·
    refine ⟨54415184839745300370149683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72553579786327067160199577 54415184839745300370149683)
    ·
      refine ⟨81622777259617950555224525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54415184839745300370149683 81622777259617950555224525)
      ·
        refine ⟨30608541472356731458209197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81622777259617950555224525 30608541472356731458209197)
        ·
          refine ⟨11478203052133774296828449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30608541472356731458209197 11478203052133774296828449)
          ·
            refine ⟨8608652289100330722621337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11478203052133774296828449 8608652289100330722621337)
            ·
              refine ⟨6456489216825248041966003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8608652289100330722621337 6456489216825248041966003)
              ·
                refine ⟨9684733825237872062949005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6456489216825248041966003 9684733825237872062949005)
                ·
                  refine ⟨3631775184464202023605877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9684733825237872062949005 3631775184464202023605877)
                  ·
                    refine ⟨340478923543518939713051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3631775184464202023605877 340478923543518939713051)
                    ·
                      rfl

theorem cell23_1989241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_1989241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989241 prefixEnd_1989241 := by exact prefixLift 1989241
  have htrace : WordTrace (prefixWord ++ tailWord_1989241) baseStart_1989241 baseEnd_1989241 := by
    simpa [prefixWord, tailWord_1989241, baseEnd_1989241] using wordTrace_append hprefix tailTrace_1989241
  have hstable : (prefixWord ++ tailWord_1989241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989241).length < 2 ^ (prefixWord ++ tailWord_1989241).sum := by decide
  have hdescent : baseEnd_1989241 < baseStart_1989241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989248 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 1, 5, 2]
def baseStart_1989248 : Nat := 118140960795 + 1989248 * 2 ^ 59
def prefixEnd_1989248 : Nat := 4983230072969 + 3 ^ 40 * 1989248 * 2
def baseEnd_1989248 : Nat := 1021440364995138291751621

theorem tailTrace_1989248 : CollatzResearch.WordTrace tailWord_1989248 prefixEnd_1989248 1021440364995138291751621 := by
  unfold tailWord_1989248
  simp only [CollatzResearch.WordTrace]
  refine ⟨36276917548650853677852199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48369223398201138237136265 36276917548650853677852199)
  ·
    refine ⟨54415376322976280516778299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36276917548650853677852199 54415376322976280516778299)
    ·
      refine ⟨81623064484464420775167449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54415376322976280516778299 81623064484464420775167449)
      ·
        refine ⟨61217298363348315581375587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81623064484464420775167449 61217298363348315581375587)
        ·
          refine ⟨91825947545022473372063381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61217298363348315581375587 91825947545022473372063381)
          ·
            refine ⟨4304341291172928439315471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91825947545022473372063381 4304341291172928439315471)
            ·
              refine ⟨6456511936759392658973207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4304341291172928439315471 6456511936759392658973207)
              ·
                refine ⟨9684767905139088988459811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6456511936759392658973207 9684767905139088988459811)
                ·
                  refine ⟨14527151857708633482689717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9684767905139088988459811 14527151857708633482689717)
                  ·
                    refine ⟨1361920486660184389002161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14527151857708633482689717 1361920486660184389002161)
                    ·
                      refine ⟨1021440364995138291751621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361920486660184389002161 1021440364995138291751621)
                      ·
                        rfl

theorem cell23_1989248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 5, 2].length) (baseStart_1989248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989248 prefixEnd_1989248 := by exact prefixLift 1989248
  have htrace : WordTrace (prefixWord ++ tailWord_1989248) baseStart_1989248 baseEnd_1989248 := by
    simpa [prefixWord, tailWord_1989248, baseEnd_1989248] using wordTrace_append hprefix tailTrace_1989248
  have hstable : (prefixWord ++ tailWord_1989248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989248).length < 2 ^ (prefixWord ++ tailWord_1989248).sum := by decide
  have hdescent : baseEnd_1989248 < baseStart_1989248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989295 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 3, 2, 2]
def baseStart_1989295 : Nat := 118140960795 + 1989295 * 2 ^ 59
def prefixEnd_1989295 : Nat := 4983230072969 + 3 ^ 40 * 1989295 * 2
def baseEnd_1989295 : Nat := 1021464498585899607863905

theorem tailTrace_1989295 : CollatzResearch.WordTrace tailWord_1989295 prefixEnd_1989295 1021464498585899607863905 := by
  unfold tailWord_1989295
  simp only [CollatzResearch.WordTrace]
  refine ⟨72555549328131434382665339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48370366218754289588443559 72555549328131434382665339)
  ·
    refine ⟨108833323992197151573998009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72555549328131434382665339 108833323992197151573998009)
    ·
      refine ⟨81624992994147863680498507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108833323992197151573998009 81624992994147863680498507)
      ·
        refine ⟨122437489491221795520747761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81624992994147863680498507 122437489491221795520747761)
        ·
          refine ⟨91828117118416346640560821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122437489491221795520747761 91828117118416346640560821)
          ·
            refine ⟨8608885979851532497552577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91828117118416346640560821 8608885979851532497552577)
            ·
              refine ⟨6456664484888649373164433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8608885979851532497552577 6456664484888649373164433)
              ·
                refine ⟨4842498363666487029873325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6456664484888649373164433 4842498363666487029873325)
                ·
                  refine ⟨1815936886374932636202497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4842498363666487029873325 1815936886374932636202497)
                  ·
                    refine ⟨1361952664781199477151873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1815936886374932636202497 1361952664781199477151873)
                    ·
                      refine ⟨1021464498585899607863905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361952664781199477151873 1021464498585899607863905)
                      ·
                        rfl

theorem cell23_1989295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 2, 2].length) (baseStart_1989295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989295 prefixEnd_1989295 := by exact prefixLift 1989295
  have htrace : WordTrace (prefixWord ++ tailWord_1989295) baseStart_1989295 baseEnd_1989295 := by
    simpa [prefixWord, tailWord_1989295, baseEnd_1989295] using wordTrace_append hprefix tailTrace_1989295
  have hstable : (prefixWord ++ tailWord_1989295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989295).length < 2 ^ (prefixWord ++ tailWord_1989295).sum := by decide
  have hdescent : baseEnd_1989295 < baseStart_1989295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989329 : List Nat := [1, 2, 2, 1, 2, 3, 5, 2, 1, 2, 2]
def baseStart_1989329 : Nat := 118140960795 + 1989329 * 2 ^ 59
def prefixEnd_1989329 : Nat := 4983230072969 + 3 ^ 40 * 1989329 * 2
def baseEnd_1989329 : Nat := 1021481956928152474838749

theorem tailTrace_1989329 : CollatzResearch.WordTrace tailWord_1989329 prefixEnd_1989329 1021481956928152474838749 := by
  unfold tailWord_1989329
  simp only [CollatzResearch.WordTrace]
  refine ⟨72556789410008258189403041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48371192940005505459602027 72556789410008258189403041)
  ·
    refine ⟨54417592057506193642052281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72556789410008258189403041 54417592057506193642052281)
    ·
      refine ⟨40813194043129645231539211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54417592057506193642052281 40813194043129645231539211)
      ·
        refine ⟨61219791064694467847308817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40813194043129645231539211 61219791064694467847308817)
        ·
          refine ⟨45914843298520850885481613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61219791064694467847308817 45914843298520850885481613)
          ·
            refine ⟨17218066236945319082055605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45914843298520850885481613 17218066236945319082055605)
            ·
              refine ⟨1614193709713623663942713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17218066236945319082055605 1614193709713623663942713)
              ·
                refine ⟨1210645282285217747957035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1614193709713623663942713 1210645282285217747957035)
                ·
                  refine ⟨1815967923427826621935553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210645282285217747957035 1815967923427826621935553)
                  ·
                    refine ⟨1361975942570869966451665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1815967923427826621935553 1361975942570869966451665)
                    ·
                      refine ⟨1021481956928152474838749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1361975942570869966451665 1021481956928152474838749)
                      ·
                        rfl

theorem cell23_1989329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 1, 2, 2].length) (baseStart_1989329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989329 prefixEnd_1989329 := by exact prefixLift 1989329
  have htrace : WordTrace (prefixWord ++ tailWord_1989329) baseStart_1989329 baseEnd_1989329 := by
    simpa [prefixWord, tailWord_1989329, baseEnd_1989329] using wordTrace_append hprefix tailTrace_1989329
  have hstable : (prefixWord ++ tailWord_1989329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989329).length < 2 ^ (prefixWord ++ tailWord_1989329).sum := by decide
  have hdescent : baseEnd_1989329 < baseStart_1989329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989381 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_1989381 : Nat := 118140960795 + 1989381 * 2 ^ 59
def prefixEnd_1989381 : Nat := 4983230072969 + 3 ^ 40 * 1989381 * 2
def baseEnd_1989381 : Nat := 1021508657922186271388509

theorem tailTrace_1989381 : CollatzResearch.WordTrace tailWord_1989381 prefixEnd_1989381 1021508657922186271388509 := by
  unfold tailWord_1989381
  simp only [CollatzResearch.WordTrace]
  refine ⟨72558686005819871070295997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48372457337213247380197331 72558686005819871070295997)
  ·
    refine ⟨27209507252182451651360999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72558686005819871070295997 27209507252182451651360999)
    ·
      refine ⟨40814260878273677477041499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27209507252182451651360999 40814260878273677477041499)
      ·
        refine ⟨61221391317410516215562249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40814260878273677477041499 61221391317410516215562249)
        ·
          refine ⟨45916043488057887161671687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61221391317410516215562249 45916043488057887161671687)
          ·
            refine ⟨68874065232086830742507531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45916043488057887161671687 68874065232086830742507531)
            ·
              refine ⟨103311097848130246113761297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68874065232086830742507531 103311097848130246113761297)
              ·
                refine ⟨77483323386097684585320973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103311097848130246113761297 77483323386097684585320973)
                ·
                  refine ⟨29056246269786631719495365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77483323386097684585320973 29056246269786631719495365)
                  ·
                    refine ⟨5448046175584993447405381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29056246269786631719495365 5448046175584993447405381)
                    ·
                      refine ⟨1021508657922186271388509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5448046175584993447405381 1021508657922186271388509)
                      ·
                        rfl

theorem cell23_1989381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_1989381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989381 prefixEnd_1989381 := by exact prefixLift 1989381
  have htrace : WordTrace (prefixWord ++ tailWord_1989381) baseStart_1989381 baseEnd_1989381 := by
    simpa [prefixWord, tailWord_1989381, baseEnd_1989381] using wordTrace_append hprefix tailTrace_1989381
  have hstable : (prefixWord ++ tailWord_1989381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989381).length < 2 ^ (prefixWord ++ tailWord_1989381).sum := by decide
  have hdescent : baseEnd_1989381 < baseStart_1989381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989385 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 4, 2, 2]
def baseStart_1989385 : Nat := 118140960795 + 1989385 * 2 ^ 59
def prefixEnd_1989385 : Nat := 4983230072969 + 3 ^ 40 * 1989385 * 2
def baseEnd_1989385 : Nat := 1021510711844804255738491

theorem tailTrace_1989385 : CollatzResearch.WordTrace tailWord_1989385 prefixEnd_1989385 1021510711844804255738491 := by
  unfold tailWord_1989385
  simp only [CollatzResearch.WordTrace]
  refine ⟨72558831897805379753441609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48372554598536919835627739 72558831897805379753441609)
  ·
    refine ⟨54419123923354034815081207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72558831897805379753441609 54419123923354034815081207)
    ·
      refine ⟨81628685885031052222621811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54419123923354034815081207 81628685885031052222621811)
      ·
        refine ⟨122443028827546578333932717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81628685885031052222621811 122443028827546578333932717)
        ·
          refine ⟨45916135810329966875224769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122443028827546578333932717 45916135810329966875224769)
          ·
            refine ⟨34437101857747475156418577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45916135810329966875224769 34437101857747475156418577)
            ·
              refine ⟨25827826393310606367313933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34437101857747475156418577 25827826393310606367313933)
              ·
                refine ⟨9685434897491477387742725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25827826393310606367313933 9685434897491477387742725)
                ·
                  refine ⟨1816019043279652010201761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9685434897491477387742725 1816019043279652010201761)
                  ·
                    refine ⟨1362014282459739007651321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1816019043279652010201761 1362014282459739007651321)
                    ·
                      refine ⟨1021510711844804255738491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1362014282459739007651321 1021510711844804255738491)
                      ·
                        rfl

theorem cell23_1989385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 2, 2].length) (baseStart_1989385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989385 prefixEnd_1989385 := by exact prefixLift 1989385
  have htrace : WordTrace (prefixWord ++ tailWord_1989385) baseStart_1989385 baseEnd_1989385 := by
    simpa [prefixWord, tailWord_1989385, baseEnd_1989385] using wordTrace_append hprefix tailTrace_1989385
  have hstable : (prefixWord ++ tailWord_1989385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989385).length < 2 ^ (prefixWord ++ tailWord_1989385).sum := by decide
  have hdescent : baseEnd_1989385 < baseStart_1989385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989391 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 7]
def baseStart_1989391 : Nat := 118140960795 + 1989391 * 2 ^ 59
def prefixEnd_1989391 : Nat := 4983230072969 + 3 ^ 40 * 1989391 * 2
def baseEnd_1989391 : Nat := 113501532525414581362607

theorem tailTrace_1989391 : CollatzResearch.WordTrace tailWord_1989391 prefixEnd_1989391 113501532525414581362607 := by
  unfold tailWord_1989391
  simp only [CollatzResearch.WordTrace]
  refine ⟨72559050735783642778160027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48372700490522428518773351 72559050735783642778160027)
  ·
    refine ⟨108838576103675464167240041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72559050735783642778160027 108838576103675464167240041)
    ·
      refine ⟨81628932077756598125430031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108838576103675464167240041 81628932077756598125430031)
      ·
        refine ⟨122443398116634897188145047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81628932077756598125430031 122443398116634897188145047)
        ·
          refine ⟨183665097174952345782217571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122443398116634897188145047 183665097174952345782217571)
          ·
            refine ⟨275497645762428518673326357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183665097174952345782217571 275497645762428518673326357)
            ·
              refine ⟨12913952145113836812812173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 275497645762428518673326357 12913952145113836812812173)
              ·
                refine ⟨4842732054417688804804565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12913952145113836812812173 4842732054417688804804565)
                ·
                  refine ⟨113501532525414581362607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4842732054417688804804565 113501532525414581362607)
                  ·
                    rfl

theorem cell23_1989391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 7].length) (baseStart_1989391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989391 prefixEnd_1989391 := by exact prefixLift 1989391
  have htrace : WordTrace (prefixWord ++ tailWord_1989391) baseStart_1989391 baseEnd_1989391 := by
    simpa [prefixWord, tailWord_1989391, baseEnd_1989391] using wordTrace_append hprefix tailTrace_1989391
  have hstable : (prefixWord ++ tailWord_1989391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989391).length < 2 ^ (prefixWord ++ tailWord_1989391).sum := by decide
  have hdescent : baseEnd_1989391 < baseStart_1989391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989402 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2]
def baseStart_1989402 : Nat := 118140960795 + 1989402 * 2 ^ 59
def prefixEnd_1989402 : Nat := 4983230072969 + 3 ^ 40 * 1989402 * 2
def baseEnd_1989402 : Nat := 1021519441015930689225913

theorem tailTrace_1989402 : CollatzResearch.WordTrace tailWord_1989402 prefixEnd_1989402 1021519441015930689225913 := by
  unfold tailWord_1989402
  simp only [CollatzResearch.WordTrace]
  refine ⟨18139862984685947914202615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48372967959162527771206973 18139862984685947914202615)
  ·
    refine ⟨27209794477028921871303923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18139862984685947914202615 27209794477028921871303923)
    ·
      refine ⟨40814691715543382806955885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27209794477028921871303923 40814691715543382806955885)
      ·
        refine ⟨15305509393328768552608457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40814691715543382806955885 15305509393328768552608457)
        ·
          refine ⟨11479132044996576414456343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15305509393328768552608457 11479132044996576414456343)
          ·
            refine ⟨17218698067494864621684515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11479132044996576414456343 17218698067494864621684515)
            ·
              refine ⟨25828047101242296932526773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17218698067494864621684515 25828047101242296932526773)
              ·
                refine ⟨2421379415741465337424385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25828047101242296932526773 2421379415741465337424385)
                ·
                  refine ⟨1816034561806099003068289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2421379415741465337424385 1816034561806099003068289)
                  ·
                    refine ⟨1362025921354574252301217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1816034561806099003068289 1362025921354574252301217)
                    ·
                      refine ⟨1021519441015930689225913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1362025921354574252301217 1021519441015930689225913)
                      ·
                        rfl

theorem cell23_1989402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_1989402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989402 prefixEnd_1989402 := by exact prefixLift 1989402
  have htrace : WordTrace (prefixWord ++ tailWord_1989402) baseStart_1989402 baseEnd_1989402 := by
    simpa [prefixWord, tailWord_1989402, baseEnd_1989402] using wordTrace_append hprefix tailTrace_1989402
  have hstable : (prefixWord ++ tailWord_1989402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989402).length < 2 ^ (prefixWord ++ tailWord_1989402).sum := by decide
  have hdescent : baseEnd_1989402 < baseStart_1989402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989408 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 7]
def baseStart_1989408 : Nat := 118140960795 + 1989408 * 2 ^ 59
def prefixEnd_1989408 : Nat := 4983230072969 + 3 ^ 40 * 1989408 * 2
def baseEnd_1989408 : Nat := 113502502433317518416765

theorem tailTrace_1989408 : CollatzResearch.WordTrace tailWord_1989408 prefixEnd_1989408 113502502433317518416765 := by
  unfold tailWord_1989408
  simp only [CollatzResearch.WordTrace]
  refine ⟨36279835388361027340764439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48373113851148036454352585 36279835388361027340764439)
  ·
    refine ⟨54419753082541541011146659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36279835388361027340764439 54419753082541541011146659)
    ·
      refine ⟨81629629623812311516719989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54419753082541541011146659 81629629623812311516719989)
      ·
        refine ⟨7652777777232404204692499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81629629623812311516719989 7652777777232404204692499)
        ·
          refine ⟨11479166665848606307038749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7652777777232404204692499 11479166665848606307038749)
          ·
            refine ⟨4304687499693227365139531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11479166665848606307038749 4304687499693227365139531)
            ·
              refine ⟨6457031249539841047709297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4304687499693227365139531 6457031249539841047709297)
              ·
                refine ⟨4842773437154880785781973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6457031249539841047709297 4842773437154880785781973)
                ·
                  refine ⟨113502502433317518416765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4842773437154880785781973 113502502433317518416765)
                  ·
                    rfl

theorem cell23_1989408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 7].length) (baseStart_1989408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989408 prefixEnd_1989408 := by exact prefixLift 1989408
  have htrace : WordTrace (prefixWord ++ tailWord_1989408) baseStart_1989408 baseEnd_1989408 := by
    simpa [prefixWord, tailWord_1989408, baseEnd_1989408] using wordTrace_append hprefix tailTrace_1989408
  have hstable : (prefixWord ++ tailWord_1989408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989408).length < 2 ^ (prefixWord ++ tailWord_1989408).sum := by decide
  have hdescent : baseEnd_1989408 < baseStart_1989408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989425 : List Nat := [1, 2, 2, 3, 2, 1, 4, 3, 5]
def baseStart_1989425 : Nat := 118140960795 + 1989425 * 2 ^ 59
def prefixEnd_1989425 : Nat := 4983230072969 + 3 ^ 40 * 1989425 * 2
def baseEnd_1989425 : Nat := 113503472341220455470923

theorem tailTrace_1989425 : CollatzResearch.WordTrace tailWord_1989425 prefixEnd_1989425 113503472341220455470923 := by
  unfold tailWord_1989425
  simp only [CollatzResearch.WordTrace]
  refine ⟨72560290817660466584897729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48373527211773644389931819 72560290817660466584897729)
  ·
    refine ⟨54420218113245349938673297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72560290817660466584897729 54420218113245349938673297)
    ·
      refine ⟨40815163584934012454004973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54420218113245349938673297 40815163584934012454004973)
      ·
        refine ⟨15305686344350254670251865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40815163584934012454004973 15305686344350254670251865)
        ·
          refine ⟨11479264758262691002688899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15305686344350254670251865 11479264758262691002688899)
          ·
            refine ⟨17218897137394036504033349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11479264758262691002688899 17218897137394036504033349)
            ·
              refine ⟨3228543213261381844506253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17218897137394036504033349 3228543213261381844506253)
              ·
                refine ⟨1210703704973018191689845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3228543213261381844506253 1210703704973018191689845)
                ·
                  refine ⟨113503472341220455470923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1210703704973018191689845 113503472341220455470923)
                  ·
                    rfl

theorem cell23_1989425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 5].length) (baseStart_1989425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989425 prefixEnd_1989425 := by exact prefixLift 1989425
  have htrace : WordTrace (prefixWord ++ tailWord_1989425) baseStart_1989425 baseEnd_1989425 := by
    simpa [prefixWord, tailWord_1989425, baseEnd_1989425] using wordTrace_append hprefix tailTrace_1989425
  have hstable : (prefixWord ++ tailWord_1989425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989425).length < 2 ^ (prefixWord ++ tailWord_1989425).sum := by decide
  have hdescent : baseEnd_1989425 < baseStart_1989425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989453 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_1989453 : Nat := 118140960795 + 1989453 * 2 ^ 59
def prefixEnd_1989453 : Nat := 4983230072969 + 3 ^ 40 * 1989453 * 2
def baseEnd_1989453 : Nat := 1021545628529309989688179

theorem tailTrace_1989453 : CollatzResearch.WordTrace tailWord_1989453 prefixEnd_1989453 1021545628529309989688179 := by
  unfold tailWord_1989453
  simp only [CollatzResearch.WordTrace]
  refine ⟨72561312061559027366917013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48374208041039351577944675 72561312061559027366917013)
  ·
    refine ⟨3401311502885579407824235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72561312061559027366917013 3401311502885579407824235)
    ·
      refine ⟨5101967254328369111736353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3401311502885579407824235 5101967254328369111736353)
      ·
        refine ⟨3826475440746276833802265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5101967254328369111736353 3826475440746276833802265)
        ·
          refine ⟨2869856580559707625351699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3826475440746276833802265 2869856580559707625351699)
          ·
            refine ⟨4304784870839561438027549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2869856580559707625351699 4304784870839561438027549)
            ·
              refine ⟨1614294326564835539260331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4304784870839561438027549 1614294326564835539260331)
              ·
                refine ⟨2421441489847253308890497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614294326564835539260331 2421441489847253308890497)
                ·
                  refine ⟨1816081117385439981667873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2421441489847253308890497 1816081117385439981667873)
                  ·
                    refine ⟨1362060838039079986250905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1816081117385439981667873 1362060838039079986250905)
                    ·
                      refine ⟨1021545628529309989688179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1362060838039079986250905 1021545628529309989688179)
                      ·
                        rfl

theorem cell23_1989453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_1989453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989453 prefixEnd_1989453 := by exact prefixLift 1989453
  have htrace : WordTrace (prefixWord ++ tailWord_1989453) baseStart_1989453 baseEnd_1989453 := by
    simpa [prefixWord, tailWord_1989453, baseEnd_1989453] using wordTrace_append hprefix tailTrace_1989453
  have hstable : (prefixWord ++ tailWord_1989453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989453).length < 2 ^ (prefixWord ++ tailWord_1989453).sum := by decide
  have hdescent : baseEnd_1989453 < baseStart_1989453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989458 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1989458 : Nat := 118140960795 + 1989458 * 2 ^ 59
def prefixEnd_1989458 : Nat := 4983230072969 + 3 ^ 40 * 1989458 * 2
def baseEnd_1989458 : Nat := 1021548195932582470125655

theorem tailTrace_1989458 : CollatzResearch.WordTrace tailWord_1989458 prefixEnd_1989458 1021548195932582470125655 := by
  unfold tailWord_1989458
  simp only [CollatzResearch.WordTrace]
  refine ⟨18140373606635228305212257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48374329617693942147232685 18140373606635228305212257)
  ·
    refine ⟨13605280204976421228909193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18140373606635228305212257 13605280204976421228909193)
    ·
      refine ⟨10203960153732315921681895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13605280204976421228909193 10203960153732315921681895)
      ·
        refine ⟨15305940230598473882522843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10203960153732315921681895 15305940230598473882522843)
        ·
          refine ⟨22958910345897710823784265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15305940230598473882522843 22958910345897710823784265)
          ·
            refine ⟨17219182759423283117838199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22958910345897710823784265 17219182759423283117838199)
            ·
              refine ⟨25828774139134924676757299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17219182759423283117838199 25828774139134924676757299)
              ·
                refine ⟨38743161208702387015135949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25828774139134924676757299 38743161208702387015135949)
                ·
                  refine ⟨14528685453263395130675981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38743161208702387015135949 14528685453263395130675981)
                  ·
                    refine ⟨5448257044973773174003493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14528685453263395130675981 5448257044973773174003493)
                    ·
                      refine ⟨1021548195932582470125655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5448257044973773174003493 1021548195932582470125655)
                      ·
                        rfl

theorem cell23_1989458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1989458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989458 prefixEnd_1989458 := by exact prefixLift 1989458
  have htrace : WordTrace (prefixWord ++ tailWord_1989458) baseStart_1989458 baseEnd_1989458 := by
    simpa [prefixWord, tailWord_1989458, baseEnd_1989458] using wordTrace_append hprefix tailTrace_1989458
  have hstable : (prefixWord ++ tailWord_1989458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989458).length < 2 ^ (prefixWord ++ tailWord_1989458).sum := by decide
  have hdescent : baseEnd_1989458 < baseStart_1989458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989498 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 6]
def baseStart_1989498 : Nat := 118140960795 + 1989498 * 2 ^ 59
def prefixEnd_1989498 : Nat := 4983230072969 + 3 ^ 40 * 1989498 * 2
def baseEnd_1989498 : Nat := 113507637239862479291719

theorem tailTrace_1989498 : CollatzResearch.WordTrace tailWord_1989498 prefixEnd_1989498 113507637239862479291719 := by
  unfold tailWord_1989498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18140738336599000013076287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48375302230930666701536765 18140738336599000013076287)
  ·
    refine ⟨27211107504898500019614431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18140738336599000013076287 27211107504898500019614431)
    ·
      refine ⟨40816661257347750029421647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27211107504898500019614431 40816661257347750029421647)
      ·
        refine ⟨61224991886021625044132471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40816661257347750029421647 61224991886021625044132471)
        ·
          refine ⟨91837487829032437566198707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61224991886021625044132471 91837487829032437566198707)
          ·
            refine ⟨137756231743548656349298061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91837487829032437566198707 137756231743548656349298061)
            ·
              refine ⟨51658586903830746130986773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137756231743548656349298061 51658586903830746130986773)
              ·
                refine ⟨2421496261117066224890005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51658586903830746130986773 2421496261117066224890005)
                ·
                  refine ⟨113507637239862479291719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2421496261117066224890005 113507637239862479291719)
                  ·
                    rfl

theorem cell23_1989498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_1989498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989498 prefixEnd_1989498 := by exact prefixLift 1989498
  have htrace : WordTrace (prefixWord ++ tailWord_1989498) baseStart_1989498 baseEnd_1989498 := by
    simpa [prefixWord, tailWord_1989498, baseEnd_1989498] using wordTrace_append hprefix tailTrace_1989498
  have hstable : (prefixWord ++ tailWord_1989498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989498).length < 2 ^ (prefixWord ++ tailWord_1989498).sum := by decide
  have hdescent : baseEnd_1989498 < baseStart_1989498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989515 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 6]
def baseStart_1989515 : Nat := 118140960795 + 1989515 * 2 ^ 59
def prefixEnd_1989515 : Nat := 4983230072969 + 3 ^ 40 * 1989515 * 2
def baseEnd_1989515 : Nat := 113508607147765416345877

theorem tailTrace_1989515 : CollatzResearch.WordTrace tailWord_1989515 prefixEnd_1989515 113508607147765416345877 := by
  unfold tailWord_1989515
  simp only [CollatzResearch.WordTrace]
  refine ⟨72563573387334411955673999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48375715591556274637115999 72563573387334411955673999)
  ·
    refine ⟨108845360081001617933510999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72563573387334411955673999 108845360081001617933510999)
    ·
      refine ⟨163268040121502426900266499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108845360081001617933510999 163268040121502426900266499)
      ·
        refine ⟨244902060182253640350399749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163268040121502426900266499 244902060182253640350399749)
        ·
          refine ⟨45919136284172557565699953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244902060182253640350399749 45919136284172557565699953)
          ·
            refine ⟨34439352213129418174274965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45919136284172557565699953 34439352213129418174274965)
            ·
              refine ⟨1614344634990441476919139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34439352213129418174274965 1614344634990441476919139)
              ·
                refine ⟨2421516952485662215378709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614344634990441476919139 2421516952485662215378709)
                ·
                  refine ⟨113508607147765416345877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2421516952485662215378709 113508607147765416345877)
                  ·
                    rfl

theorem cell23_1989515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 6].length) (baseStart_1989515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989515 prefixEnd_1989515 := by exact prefixLift 1989515
  have htrace : WordTrace (prefixWord ++ tailWord_1989515) baseStart_1989515 baseEnd_1989515 := by
    simpa [prefixWord, tailWord_1989515, baseEnd_1989515] using wordTrace_append hprefix tailTrace_1989515
  have hstable : (prefixWord ++ tailWord_1989515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989515).length < 2 ^ (prefixWord ++ tailWord_1989515).sum := by decide
  have hdescent : baseEnd_1989515 < baseStart_1989515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989526 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1989526 : Nat := 118140960795 + 1989526 * 2 ^ 59
def prefixEnd_1989526 : Nat := 4983230072969 + 3 ^ 40 * 1989526 * 2
def baseEnd_1989526 : Nat := 1021583112617088204075343

theorem tailTrace_1989526 : CollatzResearch.WordTrace tailWord_1989526 prefixEnd_1989526 1021583112617088204075343 := by
  unfold tailWord_1989526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4535248411893410052145277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48375983060196373889549621 4535248411893410052145277)
  ·
    refine ⟨1700718154460028769554479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4535248411893410052145277 1700718154460028769554479)
    ·
      refine ⟨2551077231690043154331719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700718154460028769554479 2551077231690043154331719)
      ·
        refine ⟨3826615847535064731497579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551077231690043154331719 3826615847535064731497579)
        ·
          refine ⟨5739923771302597097246369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826615847535064731497579 5739923771302597097246369)
          ·
            refine ⟨4304942828476947822934777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5739923771302597097246369 4304942828476947822934777)
            ·
              refine ⟨3228707121357710867201083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4304942828476947822934777 3228707121357710867201083)
              ·
                refine ⟨4843060682036566300801625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3228707121357710867201083 4843060682036566300801625)
                ·
                  refine ⟨3632295511527424725601219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4843060682036566300801625 3632295511527424725601219)
                  ·
                    refine ⟨5448443267291137088401829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3632295511527424725601219 5448443267291137088401829)
                    ·
                      refine ⟨1021583112617088204075343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5448443267291137088401829 1021583112617088204075343)
                      ·
                        rfl

theorem cell23_1989526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1989526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989526 prefixEnd_1989526 := by exact prefixLift 1989526
  have htrace : WordTrace (prefixWord ++ tailWord_1989526) baseStart_1989526 baseEnd_1989526 := by
    simpa [prefixWord, tailWord_1989526, baseEnd_1989526] using wordTrace_append hprefix tailTrace_1989526
  have hstable : (prefixWord ++ tailWord_1989526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989526).length < 2 ^ (prefixWord ++ tailWord_1989526).sum := by decide
  have hdescent : baseEnd_1989526 < baseStart_1989526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989549 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 6]
def baseStart_1989549 : Nat := 118140960795 + 1989549 * 2 ^ 59
def prefixEnd_1989549 : Nat := 4983230072969 + 3 ^ 40 * 1989549 * 2
def baseEnd_1989549 : Nat := 113510546963571290454193

theorem tailTrace_1989549 : CollatzResearch.WordTrace tailWord_1989549 prefixEnd_1989549 113510546963571290454193 := by
  unfold tailWord_1989549
  simp only [CollatzResearch.WordTrace]
  refine ⟨72564813469211235762411701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48376542312807490508274467 72564813469211235762411701)
  ·
    refine ⟨6802951262738553352726097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72564813469211235762411701 6802951262738553352726097)
    ·
      refine ⟨5102213447053915014544573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6802951262738553352726097 5102213447053915014544573)
      ·
        refine ⟨1913330042645218130454215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5102213447053915014544573 1913330042645218130454215)
        ·
          refine ⟨2869995063967827195681323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913330042645218130454215 2869995063967827195681323)
          ·
            refine ⟨4304992595951740793521985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2869995063967827195681323 4304992595951740793521985)
            ·
              refine ⟨3228744446963805595141489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4304992595951740793521985 3228744446963805595141489)
              ·
                refine ⟨2421558335222854196356117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3228744446963805595141489 2421558335222854196356117)
                ·
                  refine ⟨113510546963571290454193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2421558335222854196356117 113510546963571290454193)
                  ·
                    rfl

theorem cell23_1989549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_1989549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989549 prefixEnd_1989549 := by exact prefixLift 1989549
  have htrace : WordTrace (prefixWord ++ tailWord_1989549) baseStart_1989549 baseEnd_1989549 := by
    simpa [prefixWord, tailWord_1989549, baseEnd_1989549] using wordTrace_append hprefix tailTrace_1989549
  have hstable : (prefixWord ++ tailWord_1989549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989549).length < 2 ^ (prefixWord ++ tailWord_1989549).sum := by decide
  have hdescent : baseEnd_1989549 < baseStart_1989549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989553 : List Nat := [1, 2, 2, 4, 4, 1, 2, 2, 1, 4]
def baseStart_1989553 : Nat := 118140960795 + 1989553 * 2 ^ 59
def prefixEnd_1989553 : Nat := 4983230072969 + 3 ^ 40 * 1989553 * 2
def baseEnd_1989553 : Nat := 340532325531586532812573

theorem tailTrace_1989553 : CollatzResearch.WordTrace tailWord_1989553 prefixEnd_1989553 340532325531586532812573 := by
  unfold tailWord_1989553
  simp only [CollatzResearch.WordTrace]
  refine ⟨72564959361196744445557313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48376639574131162963704875 72564959361196744445557313)
  ·
    refine ⟨54423719520897558334167985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72564959361196744445557313 54423719520897558334167985)
    ·
      refine ⟨40817789640673168750625989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54423719520897558334167985 40817789640673168750625989)
      ·
        refine ⟨7653335557626219140742373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40817789640673168750625989 7653335557626219140742373)
        ·
          refine ⟨1435000417054916088889195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7653335557626219140742373 1435000417054916088889195)
          ·
            refine ⟨2152500625582374133333793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435000417054916088889195 2152500625582374133333793)
            ·
              refine ⟨1614375469186780600000345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2152500625582374133333793 1614375469186780600000345)
              ·
                refine ⟨1210781601890085450000259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1614375469186780600000345 1210781601890085450000259)
                ·
                  refine ⟨1816172402835128175000389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210781601890085450000259 1816172402835128175000389)
                  ·
                    refine ⟨340532325531586532812573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1816172402835128175000389 340532325531586532812573)
                    ·
                      rfl

theorem cell23_1989553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_1989553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989553 prefixEnd_1989553 := by exact prefixLift 1989553
  have htrace : WordTrace (prefixWord ++ tailWord_1989553) baseStart_1989553 baseEnd_1989553 := by
    simpa [prefixWord, tailWord_1989553, baseEnd_1989553] using wordTrace_append hprefix tailTrace_1989553
  have hstable : (prefixWord ++ tailWord_1989553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989553).length < 2 ^ (prefixWord ++ tailWord_1989553).sum := by decide
  have hdescent : baseEnd_1989553 < baseStart_1989553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989585 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 3, 2, 3]
def baseStart_1989585 : Nat := 118140960795 + 1989585 * 2 ^ 59
def prefixEnd_1989585 : Nat := 4983230072969 + 3 ^ 40 * 1989585 * 2
def baseEnd_1989585 : Nat := 1021613407975703473237571

theorem tailTrace_1989585 : CollatzResearch.WordTrace tailWord_1989585 prefixEnd_1989585 1021613407975703473237571 := by
  unfold tailWord_1989585
  simp only [CollatzResearch.WordTrace]
  refine ⟨72566126497080813910722209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48377417664720542607148139 72566126497080813910722209)
  ·
    refine ⟨54424594872810610433041657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72566126497080813910722209 54424594872810610433041657)
    ·
      refine ⟨40818446154607957824781243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54424594872810610433041657 40818446154607957824781243)
      ·
        refine ⟨61227669231911936737171865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40818446154607957824781243 61227669231911936737171865)
        ·
          refine ⟨45920751923933952552878899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61227669231911936737171865 45920751923933952552878899)
          ·
            refine ⟨68881127885900928829318349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45920751923933952552878899 68881127885900928829318349)
            ·
              refine ⟨25830422957212848310994381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68881127885900928829318349 25830422957212848310994381)
              ·
                refine ⟨9686408608954818116622893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25830422957212848310994381 9686408608954818116622893)
                ·
                  refine ⟨3632403228358056793733585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9686408608954818116622893 3632403228358056793733585)
                  ·
                    refine ⟨2724302421268542595300189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3632403228358056793733585 2724302421268542595300189)
                    ·
                      refine ⟨1021613407975703473237571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2724302421268542595300189 1021613407975703473237571)
                      ·
                        rfl

theorem cell23_1989585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_1989585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989585 prefixEnd_1989585 := by exact prefixLift 1989585
  have htrace : WordTrace (prefixWord ++ tailWord_1989585) baseStart_1989585 baseEnd_1989585 := by
    simpa [prefixWord, tailWord_1989585, baseEnd_1989585] using wordTrace_append hprefix tailTrace_1989585
  have hstable : (prefixWord ++ tailWord_1989585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989585).length < 2 ^ (prefixWord ++ tailWord_1989585).sum := by decide
  have hdescent : baseEnd_1989585 < baseStart_1989585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989586 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_1989586 : Nat := 118140960795 + 1989586 * 2 ^ 59
def prefixEnd_1989586 : Nat := 4983230072969 + 3 ^ 40 * 1989586 * 2
def baseEnd_1989586 : Nat := 1021613921456357969325067

theorem tailTrace_1989586 : CollatzResearch.WordTrace tailWord_1989586 prefixEnd_1989586 1021613921456357969325067 := by
  unfold tailWord_1989586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18141540742519297770377153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48377441980051460721005741 18141540742519297770377153)
  ·
    refine ⟨13606155556889473327782865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18141540742519297770377153 13606155556889473327782865)
    ·
      refine ⟨10204616667667104995837149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13606155556889473327782865 10204616667667104995837149)
      ·
        refine ⟨3826731250375164373438931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10204616667667104995837149 3826731250375164373438931)
        ·
          refine ⟨5740096875562746560158397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826731250375164373438931 5740096875562746560158397)
          ·
            refine ⟨2152536328336029960059399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5740096875562746560158397 2152536328336029960059399)
            ·
              refine ⟨3228804492504044940089099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152536328336029960059399 3228804492504044940089099)
              ·
                refine ⟨4843206738756067410133649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3228804492504044940089099 4843206738756067410133649)
                ·
                  refine ⟨3632405054067050557600237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4843206738756067410133649 3632405054067050557600237)
                  ·
                    refine ⟨1362151895275143959100089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3632405054067050557600237 1362151895275143959100089)
                    ·
                      refine ⟨1021613921456357969325067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1362151895275143959100089 1021613921456357969325067)
                      ·
                        rfl

theorem cell23_1989586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_1989586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989586 prefixEnd_1989586 := by exact prefixLift 1989586
  have htrace : WordTrace (prefixWord ++ tailWord_1989586) baseStart_1989586 baseEnd_1989586 := by
    simpa [prefixWord, tailWord_1989586, baseEnd_1989586] using wordTrace_append hprefix tailTrace_1989586
  have hstable : (prefixWord ++ tailWord_1989586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989586).length < 2 ^ (prefixWord ++ tailWord_1989586).sum := by decide
  have hdescent : baseEnd_1989586 < baseStart_1989586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989675 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 3]
def baseStart_1989675 : Nat := 118140960795 + 1989675 * 2 ^ 59
def prefixEnd_1989675 : Nat := 4983230072969 + 3 ^ 40 * 1989675 * 2
def baseEnd_1989675 : Nat := 1021659621234608121112157

theorem tailTrace_1989675 : CollatzResearch.WordTrace tailWord_1989675 prefixEnd_1989675 1021659621234608121112157 := by
  unfold tailWord_1989675
  simp only [CollatzResearch.WordTrace]
  refine ⟨72569409066754759281498479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48379606044503172854332319 72569409066754759281498479)
  ·
    refine ⟨108854113600132138922247719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72569409066754759281498479 108854113600132138922247719)
    ·
      refine ⟨163281170400198208383371579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108854113600132138922247719 163281170400198208383371579)
      ·
        refine ⟨244921755600297312575057369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163281170400198208383371579 244921755600297312575057369)
        ·
          refine ⟨183691316700222984431293027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244921755600297312575057369 183691316700222984431293027)
          ·
            refine ⟨275536975050334476646939541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183691316700222984431293027 275536975050334476646939541)
            ·
              refine ⟨12915795705484428592825291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 275536975050334476646939541 12915795705484428592825291)
              ·
                refine ⟨19373693558226642889237937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915795705484428592825291 19373693558226642889237937)
                ·
                  refine ⟨14530270168669982166928453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19373693558226642889237937 14530270168669982166928453)
                  ·
                    refine ⟨2724425656625621656299085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14530270168669982166928453 2724425656625621656299085)
                    ·
                      refine ⟨1021659621234608121112157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2724425656625621656299085 1021659621234608121112157)
                      ·
                        rfl

theorem cell23_1989675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 3].length) (baseStart_1989675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989675 prefixEnd_1989675 := by exact prefixLift 1989675
  have htrace : WordTrace (prefixWord ++ tailWord_1989675) baseStart_1989675 baseEnd_1989675 := by
    simpa [prefixWord, tailWord_1989675, baseEnd_1989675] using wordTrace_append hprefix tailTrace_1989675
  have hstable : (prefixWord ++ tailWord_1989675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989675).length < 2 ^ (prefixWord ++ tailWord_1989675).sum := by decide
  have hdescent : baseEnd_1989675 < baseStart_1989675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989685 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1989685 : Nat := 118140960795 + 1989685 * 2 ^ 59
def prefixEnd_1989685 : Nat := 4983230072969 + 3 ^ 40 * 1989685 * 2
def baseEnd_1989685 : Nat := 1021664756041153081987111

theorem tailTrace_1989685 : CollatzResearch.WordTrace tailWord_1989685 prefixEnd_1989685 1021664756041153081987111 := by
  unfold tailWord_1989685
  simp only [CollatzResearch.WordTrace]
  refine ⟨72569773796718530989362509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48379849197812353992908339 72569773796718530989362509)
  ·
    refine ⟨27213665173769449121010941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72569773796718530989362509 27213665173769449121010941)
    ·
      refine ⟨10205124440163543420379103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27213665173769449121010941 10205124440163543420379103)
      ·
        refine ⟨15307686660245315130568655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10205124440163543420379103 15307686660245315130568655)
        ·
          refine ⟨22961529990367972695852983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15307686660245315130568655 22961529990367972695852983)
          ·
            refine ⟨34442294985551959043779475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22961529990367972695852983 34442294985551959043779475)
            ·
              refine ⟨51663442478327938565669213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34442294985551959043779475 51663442478327938565669213)
              ·
                refine ⟨19373790929372976962125955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51663442478327938565669213 19373790929372976962125955)
                ·
                  refine ⟨29060686394059465443188933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19373790929372976962125955 29060686394059465443188933)
                  ·
                    refine ⟨5448878698886149770597925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29060686394059465443188933 5448878698886149770597925)
                    ·
                      refine ⟨1021664756041153081987111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5448878698886149770597925 1021664756041153081987111)
                      ·
                        rfl

theorem cell23_1989685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1989685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989685 prefixEnd_1989685 := by exact prefixLift 1989685
  have htrace : WordTrace (prefixWord ++ tailWord_1989685) baseStart_1989685 baseEnd_1989685 := by
    simpa [prefixWord, tailWord_1989685, baseEnd_1989685] using wordTrace_append hprefix tailTrace_1989685
  have hstable : (prefixWord ++ tailWord_1989685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989685).length < 2 ^ (prefixWord ++ tailWord_1989685).sum := by decide
  have hdescent : baseEnd_1989685 < baseStart_1989685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989705 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 3, 5, 3]
def baseStart_1989705 : Nat := 118140960795 + 1989705 * 2 ^ 59
def prefixEnd_1989705 : Nat := 4983230072969 + 3 ^ 40 * 1989705 * 2
def baseEnd_1989705 : Nat := 1021675025654243003737019

theorem tailTrace_1989705 : CollatzResearch.WordTrace tailWord_1989705 prefixEnd_1989705 1021675025654243003737019 := by
  unfold tailWord_1989705
  simp only [CollatzResearch.WordTrace]
  refine ⟨72570503256646074405090569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48380335504430716270060379 72570503256646074405090569)
  ·
    refine ⟨54427877442484555803817927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72570503256646074405090569 54427877442484555803817927)
    ·
      refine ⟨81641816163726833705726891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54427877442484555803817927 81641816163726833705726891)
      ·
        refine ⟨122462724245590250558590337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81641816163726833705726891 122462724245590250558590337)
        ·
          refine ⟨91847043184192687918942753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122462724245590250558590337 91847043184192687918942753)
          ·
            refine ⟨68885282388144515939207065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91847043184192687918942753 68885282388144515939207065)
            ·
              refine ⟨51663961791108386954405299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68885282388144515939207065 51663961791108386954405299)
              ·
                refine ⟨77495942686662580431607949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51663961791108386954405299 77495942686662580431607949)
                ·
                  refine ⟨29060978507498467661852981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77495942686662580431607949 29060978507498467661852981)
                  ·
                    refine ⟨2724466735077981343298717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29060978507498467661852981 2724466735077981343298717)
                    ·
                      refine ⟨1021675025654243003737019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2724466735077981343298717 1021675025654243003737019)
                      ·
                        rfl

theorem cell23_1989705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5, 3].length) (baseStart_1989705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989705 prefixEnd_1989705 := by exact prefixLift 1989705
  have htrace : WordTrace (prefixWord ++ tailWord_1989705) baseStart_1989705 baseEnd_1989705 := by
    simpa [prefixWord, tailWord_1989705, baseEnd_1989705] using wordTrace_append hprefix tailTrace_1989705
  have hstable : (prefixWord ++ tailWord_1989705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989705).length < 2 ^ (prefixWord ++ tailWord_1989705).sum := by decide
  have hdescent : baseEnd_1989705 < baseStart_1989705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989726 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1989726 : Nat := 118140960795 + 1989726 * 2 ^ 59
def prefixEnd_1989726 : Nat := 4983230072969 + 3 ^ 40 * 1989726 * 2
def baseEnd_1989726 : Nat := 1021685808747987421574423

theorem tailTrace_1989726 : CollatzResearch.WordTrace tailWord_1989726 prefixEnd_1989726 1021685808747987421574423 := by
  unfold tailWord_1989726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9071408648696249373950629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48380846126379996661070021 9071408648696249373950629)
  ·
    refine ⟨1700889121630546757615743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9071408648696249373950629 1700889121630546757615743)
    ·
      refine ⟨2551333682445820136423615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700889121630546757615743 2551333682445820136423615)
      ·
        refine ⟨3827000523668730204635423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551333682445820136423615 3827000523668730204635423)
        ·
          refine ⟨5740500785503095306953135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827000523668730204635423 5740500785503095306953135)
          ·
            refine ⟨8610751178254642960429703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740500785503095306953135 8610751178254642960429703)
            ·
              refine ⟨12916126767381964440644555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610751178254642960429703 12916126767381964440644555)
              ·
                refine ⟨19374190151072946660966833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12916126767381964440644555 19374190151072946660966833)
                ·
                  refine ⟨14530642613304709995725125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19374190151072946660966833 14530642613304709995725125)
                  ·
                    refine ⟨2724495489994633124198461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14530642613304709995725125 2724495489994633124198461)
                    ·
                      refine ⟨1021685808747987421574423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2724495489994633124198461 1021685808747987421574423)
                      ·
                        rfl

theorem cell23_1989726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1989726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989726 prefixEnd_1989726 := by exact prefixLift 1989726
  have htrace : WordTrace (prefixWord ++ tailWord_1989726) baseStart_1989726 baseEnd_1989726 := by
    simpa [prefixWord, tailWord_1989726, baseEnd_1989726] using wordTrace_append hprefix tailTrace_1989726
  have hstable : (prefixWord ++ tailWord_1989726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989726).length < 2 ^ (prefixWord ++ tailWord_1989726).sum := by decide
  have hdescent : baseEnd_1989726 < baseStart_1989726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989729 : List Nat := [1, 2, 3, 1, 1, 2, 6, 2, 5]
def baseStart_1989729 : Nat := 118140960795 + 1989729 * 2 ^ 59
def prefixEnd_1989729 : Nat := 4983230072969 + 3 ^ 40 * 1989729 * 2
def baseEnd_1989729 : Nat := 113520816576661212204101

theorem tailTrace_1989729 : CollatzResearch.WordTrace tailWord_1989729 prefixEnd_1989729 113520816576661212204101 := by
  unfold tailWord_1989729
  simp only [CollatzResearch.WordTrace]
  refine ⟨72571378608559126503964241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48380919072372751002642827 72571378608559126503964241)
  ·
    refine ⟨54428533956419344877973181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72571378608559126503964241 54428533956419344877973181)
    ·
      refine ⟨20410700233657254329239943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54428533956419344877973181 20410700233657254329239943)
      ·
        refine ⟨30616050350485881493859915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20410700233657254329239943 30616050350485881493859915)
        ·
          refine ⟨45924075525728822240789873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30616050350485881493859915 45924075525728822240789873)
          ·
            refine ⟨34443056644296616680592405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45924075525728822240789873 34443056644296616680592405)
            ·
              refine ⟨1614518280201403906902769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34443056644296616680592405 1614518280201403906902769)
              ·
                refine ⟨1210888710151052930177077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1614518280201403906902769 1210888710151052930177077)
                ·
                  refine ⟨113520816576661212204101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1210888710151052930177077 113520816576661212204101)
                  ·
                    rfl

theorem cell23_1989729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 5].length) (baseStart_1989729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989729 prefixEnd_1989729 := by exact prefixLift 1989729
  have htrace : WordTrace (prefixWord ++ tailWord_1989729) baseStart_1989729 baseEnd_1989729 := by
    simpa [prefixWord, tailWord_1989729, baseEnd_1989729] using wordTrace_append hprefix tailTrace_1989729
  have hstable : (prefixWord ++ tailWord_1989729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989729).length < 2 ^ (prefixWord ++ tailWord_1989729).sum := by decide
  have hdescent : baseEnd_1989729 < baseStart_1989729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989789 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1989789 : Nat := 118140960795 + 1989789 * 2 ^ 59
def prefixEnd_1989789 : Nat := 4983230072969 + 3 ^ 40 * 1989789 * 2
def baseEnd_1989789 : Nat := 340572719343073558362211

theorem tailTrace_1989789 : CollatzResearch.WordTrace tailWord_1989789 prefixEnd_1989789 340572719343073558362211 := by
  unfold tailWord_1989789
  simp only [CollatzResearch.WordTrace]
  refine ⟨72573566988341756751148421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48382377992227837834098947 72573566988341756751148421)
  ·
    refine ⟨13607543810314079390840329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72573566988341756751148421 13607543810314079390840329)
    ·
      refine ⟨10205657857735559543130247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13607543810314079390840329 10205657857735559543130247)
      ·
        refine ⟨15308486786603339314695371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10205657857735559543130247 15308486786603339314695371)
        ·
          refine ⟨22962730179905008972043057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15308486786603339314695371 22962730179905008972043057)
          ·
            refine ⟨17222047634928756729032293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22962730179905008972043057 17222047634928756729032293)
            ·
              refine ⟨3229133931549141886693555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17222047634928756729032293 3229133931549141886693555)
              ·
                refine ⟨4843700897323712830040333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229133931549141886693555 4843700897323712830040333)
                ·
                  refine ⟨1816387836496392311265125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4843700897323712830040333 1816387836496392311265125)
                  ·
                    refine ⟨340572719343073558362211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1816387836496392311265125 340572719343073558362211)
                    ·
                      rfl

theorem cell23_1989789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1989789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989789 prefixEnd_1989789 := by exact prefixLift 1989789
  have htrace : WordTrace (prefixWord ++ tailWord_1989789) baseStart_1989789 baseEnd_1989789 := by
    simpa [prefixWord, tailWord_1989789, baseEnd_1989789] using wordTrace_append hprefix tailTrace_1989789
  have hstable : (prefixWord ++ tailWord_1989789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989789).length < 2 ^ (prefixWord ++ tailWord_1989789).sum := by decide
  have hdescent : baseEnd_1989789 < baseStart_1989789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989799 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1989799 : Nat := 118140960795 + 1989799 * 2 ^ 59
def prefixEnd_1989799 : Nat := 4983230072969 + 3 ^ 40 * 1989799 * 2
def baseEnd_1989799 : Nat := 1021723292835765635961587

theorem tailTrace_1989799 : CollatzResearch.WordTrace tailWord_1989799 prefixEnd_1989799 1021723292835765635961587 := by
  unfold tailWord_1989799
  simp only [CollatzResearch.WordTrace]
  refine ⟨72573931718305528459012451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48382621145537018972674967 72573931718305528459012451)
  ·
    refine ⟨108860897577458292688518677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72573931718305528459012451 108860897577458292688518677)
    ·
      refine ⟨5102854573943357469774313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108860897577458292688518677 5102854573943357469774313)
      ·
        refine ⟨3827140930457518102330735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5102854573943357469774313 3827140930457518102330735)
        ·
          refine ⟨5740711395686277153496103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827140930457518102330735 5740711395686277153496103)
          ·
            refine ⟨8611067093529415730244155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740711395686277153496103 8611067093529415730244155)
            ·
              refine ⟨12916600640294123595366233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8611067093529415730244155 12916600640294123595366233)
              ·
                refine ⟨9687450480220592696524675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12916600640294123595366233 9687450480220592696524675)
                ·
                  refine ⟨14531175720330889044787013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9687450480220592696524675 14531175720330889044787013)
                  ·
                    refine ⟨2724595447562041695897565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14531175720330889044787013 2724595447562041695897565)
                    ·
                      refine ⟨1021723292835765635961587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2724595447562041695897565 1021723292835765635961587)
                      ·
                        rfl

theorem cell23_1989799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1989799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989799 prefixEnd_1989799 := by exact prefixLift 1989799
  have htrace : WordTrace (prefixWord ++ tailWord_1989799) baseStart_1989799 baseEnd_1989799 := by
    simpa [prefixWord, tailWord_1989799, baseEnd_1989799] using wordTrace_append hprefix tailTrace_1989799
  have hstable : (prefixWord ++ tailWord_1989799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989799).length < 2 ^ (prefixWord ++ tailWord_1989799).sum := by decide
  have hdescent : baseEnd_1989799 < baseStart_1989799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989830 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1989830 : Nat := 118140960795 + 1989830 * 2 ^ 59
def prefixEnd_1989830 : Nat := 4983230072969 + 3 ^ 40 * 1989830 * 2
def baseEnd_1989830 : Nat := 1021739210736055014673945

theorem tailTrace_1989830 : CollatzResearch.WordTrace tailWord_1989830 prefixEnd_1989830 1021739210736055014673945 := by
  unfold tailWord_1989830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267970699412288148543467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48383374920795480502260629 2267970699412288148543467)
  ·
    refine ⟨3401956049118432222815201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2267970699412288148543467 3401956049118432222815201)
    ·
      refine ⟨2551467036838824167111401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3401956049118432222815201 2551467036838824167111401)
      ·
        refine ⟨1913600277629118125333551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2551467036838824167111401 1913600277629118125333551)
        ·
          refine ⟨2870400416443677188000327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913600277629118125333551 2870400416443677188000327)
          ·
            refine ⟨4305600624665515782000491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870400416443677188000327 4305600624665515782000491)
            ·
              refine ⟨6458400936998273673000737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305600624665515782000491 6458400936998273673000737)
              ·
                refine ⟨4843800702748705254750553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6458400936998273673000737 4843800702748705254750553)
                ·
                  refine ⟨3632850527061528941062915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4843800702748705254750553 3632850527061528941062915)
                  ·
                    refine ⟨5449275790592293411594373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3632850527061528941062915 5449275790592293411594373)
                    ·
                      refine ⟨1021739210736055014673945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5449275790592293411594373 1021739210736055014673945)
                      ·
                        rfl

theorem cell23_1989830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1989830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989830 prefixEnd_1989830 := by exact prefixLift 1989830
  have htrace : WordTrace (prefixWord ++ tailWord_1989830) baseStart_1989830 baseEnd_1989830 := by
    simpa [prefixWord, tailWord_1989830, baseEnd_1989830] using wordTrace_append hprefix tailTrace_1989830
  have hstable : (prefixWord ++ tailWord_1989830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989830).length < 2 ^ (prefixWord ++ tailWord_1989830).sum := by decide
  have hdescent : baseEnd_1989830 < baseStart_1989830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989853 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 6]
def baseStart_1989853 : Nat := 118140960795 + 1989853 * 2 ^ 59
def prefixEnd_1989853 : Nat := 4983230072969 + 3 ^ 40 * 1989853 * 2
def baseEnd_1989853 : Nat := 113527891199012047187371

theorem tailTrace_1989853 : CollatzResearch.WordTrace tailWord_1989853 prefixEnd_1989853 113527891199012047187371 := by
  unfold tailWord_1989853
  simp only [CollatzResearch.WordTrace]
  refine ⟨72575901260109895681478213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48383934173406597120985475 72575901260109895681478213)
  ·
    refine ⟨13607981486270605440277165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72575901260109895681478213 13607981486270605440277165)
    ·
      refine ⟨5102993057351477040103937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13607981486270605440277165 5102993057351477040103937)
      ·
        refine ⟨3827244793013607780077953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5102993057351477040103937 3827244793013607780077953)
        ·
          refine ⟨2870433594760205835058465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3827244793013607780077953 2870433594760205835058465)
          ·
            refine ⟨2152825196070154376293849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2870433594760205835058465 2152825196070154376293849)
            ·
              refine ⟨1614618897052615782220387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2152825196070154376293849 1614618897052615782220387)
              ·
                refine ⟨2421928345578923673330581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614618897052615782220387 2421928345578923673330581)
                ·
                  refine ⟨113527891199012047187371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2421928345578923673330581 113527891199012047187371)
                  ·
                    rfl

theorem cell23_1989853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_1989853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989853 prefixEnd_1989853 := by exact prefixLift 1989853
  have htrace : WordTrace (prefixWord ++ tailWord_1989853) baseStart_1989853 baseEnd_1989853 := by
    simpa [prefixWord, tailWord_1989853, baseEnd_1989853] using wordTrace_append hprefix tailTrace_1989853
  have hstable : (prefixWord ++ tailWord_1989853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989853).length < 2 ^ (prefixWord ++ tailWord_1989853).sum := by decide
  have hdescent : baseEnd_1989853 < baseStart_1989853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989866 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 1, 5]
def baseStart_1989866 : Nat := 118140960795 + 1989866 * 2 ^ 59
def prefixEnd_1989866 : Nat := 4983230072969 + 3 ^ 40 * 1989866 * 2
def baseEnd_1989866 : Nat := 340585898679872291274593

theorem tailTrace_1989866 : CollatzResearch.WordTrace tailWord_1989866 prefixEnd_1989866 340585898679872291274593 := by
  unfold tailWord_1989866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18144093852265699725425363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48384250272708532601134301 18144093852265699725425363)
  ·
    refine ⟨27216140778398549588138045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18144093852265699725425363 27216140778398549588138045)
    ·
      refine ⟨10206052791899456095551767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27216140778398549588138045 10206052791899456095551767)
      ·
        refine ⟨15309079187849184143327651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10206052791899456095551767 15309079187849184143327651)
        ·
          refine ⟨22963618781773776214991477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15309079187849184143327651 22963618781773776214991477)
          ·
            refine ⟨2152839260791291520155451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22963618781773776214991477 2152839260791291520155451)
            ·
              refine ⟨3229258891186937280233177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152839260791291520155451 3229258891186937280233177)
              ·
                refine ⟨2421944168390202960174883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3229258891186937280233177 2421944168390202960174883)
                ·
                  refine ⟨3632916252585304440262325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2421944168390202960174883 3632916252585304440262325)
                  ·
                    refine ⟨340585898679872291274593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3632916252585304440262325 340585898679872291274593)
                    ·
                      rfl

theorem cell23_1989866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_1989866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989866 prefixEnd_1989866 := by exact prefixLift 1989866
  have htrace : WordTrace (prefixWord ++ tailWord_1989866) baseStart_1989866 baseEnd_1989866 := by
    simpa [prefixWord, tailWord_1989866, baseEnd_1989866] using wordTrace_append hprefix tailTrace_1989866
  have hstable : (prefixWord ++ tailWord_1989866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989866).length < 2 ^ (prefixWord ++ tailWord_1989866).sum := by decide
  have hdescent : baseEnd_1989866 < baseStart_1989866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989889 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_1989889 : Nat := 118140960795 + 1989889 * 2 ^ 59
def prefixEnd_1989889 : Nat := 4983230072969 + 3 ^ 40 * 1989889 * 2
def baseEnd_1989889 : Nat := 1021769506094670283836173

theorem tailTrace_1989889 : CollatzResearch.WordTrace tailWord_1989889 prefixEnd_1989889 1021769506094670283836173 := by
  unfold tailWord_1989889
  simp only [CollatzResearch.WordTrace]
  refine ⟨72577214287979473829788721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48384809525319649219859147 72577214287979473829788721)
  ·
    refine ⟨54432910715984605372341541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72577214287979473829788721 54432910715984605372341541)
    ·
      refine ⟨10206170759247113507314039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54432910715984605372341541 10206170759247113507314039)
      ·
        refine ⟨15309256138870670260971059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10206170759247113507314039 15309256138870670260971059)
        ·
          refine ⟨22963884208306005391456589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15309256138870670260971059 22963884208306005391456589)
          ·
            refine ⟨8611456578114752021796221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22963884208306005391456589 8611456578114752021796221)
            ·
              refine ⟨3229296216793032008173583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8611456578114752021796221 3229296216793032008173583)
              ·
                refine ⟨4843944325189548012260375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229296216793032008173583 4843944325189548012260375)
                ·
                  refine ⟨7265916487784322018390563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4843944325189548012260375 7265916487784322018390563)
                  ·
                    refine ⟨10898874731676483027585845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7265916487784322018390563 10898874731676483027585845)
                    ·
                      refine ⟨1021769506094670283836173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10898874731676483027585845 1021769506094670283836173)
                      ·
                        rfl

theorem cell23_1989889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_1989889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989889 prefixEnd_1989889 := by exact prefixLift 1989889
  have htrace : WordTrace (prefixWord ++ tailWord_1989889) baseStart_1989889 baseEnd_1989889 := by
    simpa [prefixWord, tailWord_1989889, baseEnd_1989889] using wordTrace_append hprefix tailTrace_1989889
  have hstable : (prefixWord ++ tailWord_1989889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989889).length < 2 ^ (prefixWord ++ tailWord_1989889).sum := by decide
  have hdescent : baseEnd_1989889 < baseStart_1989889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989892 : List Nat := [2, 3, 2, 2, 2, 12]
def baseStart_1989892 : Nat := 118140960795 + 1989892 * 2 ^ 59
def prefixEnd_1989892 : Nat := 4983230072969 + 3 ^ 40 * 1989892 * 2
def baseEnd_1989892 : Nat := 4204819121549933218513

theorem tailTrace_1989892 : CollatzResearch.WordTrace tailWord_1989892 prefixEnd_1989892 4204819121549933218513 := by
  unfold tailWord_1989892
  simp only [CollatzResearch.WordTrace]
  refine ⟨36288661853484302671073965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48384882471312403561431953 36288661853484302671073965)
  ·
    refine ⟨13608248195056613501652737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36288661853484302671073965 13608248195056613501652737)
    ·
      refine ⟨10206186146292460126239553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13608248195056613501652737 10206186146292460126239553)
      ·
        refine ⟨7654639609719345094679665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10206186146292460126239553 7654639609719345094679665)
        ·
          refine ⟨5740979707289508821009749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7654639609719345094679665 5740979707289508821009749)
          ·
            refine ⟨4204819121549933218513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5740979707289508821009749 4204819121549933218513)
            ·
              rfl

theorem cell23_1989892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 12].length) (baseStart_1989892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989892 prefixEnd_1989892 := by exact prefixLift 1989892
  have htrace : WordTrace (prefixWord ++ tailWord_1989892) baseStart_1989892 baseEnd_1989892 := by
    simpa [prefixWord, tailWord_1989892, baseEnd_1989892] using wordTrace_append hprefix tailTrace_1989892
  have hstable : (prefixWord ++ tailWord_1989892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989892).length < 2 ^ (prefixWord ++ tailWord_1989892).sum := by decide
  have hdescent : baseEnd_1989892 < baseStart_1989892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989932 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_1989932 : Nat := 118140960795 + 1989932 * 2 ^ 59
def prefixEnd_1989932 : Nat := 4983230072969 + 3 ^ 40 * 1989932 * 2
def baseEnd_1989932 : Nat := 1021791585762813615598475

theorem tailTrace_1989932 : CollatzResearch.WordTrace tailWord_1989932 prefixEnd_1989932 1021791585762813615598475 := by
  unfold tailWord_1989932
  simp only [CollatzResearch.WordTrace]
  refine ⟨36289391313411846086802025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48385855084549128115736033 36289391313411846086802025)
  ·
    refine ⟨27217043485058884565101519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36289391313411846086802025 27217043485058884565101519)
    ·
      refine ⟨40825565227588326847652279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27217043485058884565101519 40825565227588326847652279)
      ·
        refine ⟨61238347841382490271478419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40825565227588326847652279 61238347841382490271478419)
        ·
          refine ⟨91857521762073735407217629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61238347841382490271478419 91857521762073735407217629)
          ·
            refine ⟨34446570660777650777706611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91857521762073735407217629 34446570660777650777706611)
            ·
              refine ⟨51669855991166476166559917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34446570660777650777706611 51669855991166476166559917)
              ·
                refine ⟨19376195996687428562459969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51669855991166476166559917 19376195996687428562459969)
                ·
                  refine ⟨14532146997515571421844977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19376195996687428562459969 14532146997515571421844977)
                  ·
                    refine ⟨10899110248136678566383733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14532146997515571421844977 10899110248136678566383733)
                    ·
                      refine ⟨1021791585762813615598475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10899110248136678566383733 1021791585762813615598475)
                      ·
                        rfl

theorem cell23_1989932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_1989932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989932 prefixEnd_1989932 := by exact prefixLift 1989932
  have htrace : WordTrace (prefixWord ++ tailWord_1989932) baseStart_1989932 baseEnd_1989932 := by
    simpa [prefixWord, tailWord_1989932, baseEnd_1989932] using wordTrace_append hprefix tailTrace_1989932
  have hstable : (prefixWord ++ tailWord_1989932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989932).length < 2 ^ (prefixWord ++ tailWord_1989932).sum := by decide
  have hdescent : baseEnd_1989932 < baseStart_1989932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989952 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 4, 6]
def baseStart_1989952 : Nat := 118140960795 + 1989952 * 2 ^ 59
def prefixEnd_1989952 : Nat := 4983230072969 + 3 ^ 40 * 1989952 * 2
def baseEnd_1989952 : Nat := 340600618458634512449461

theorem tailTrace_1989952 : CollatzResearch.WordTrace tailWord_1989952 prefixEnd_1989952 340600618458634512449461 := by
  unfold tailWord_1989952
  simp only [CollatzResearch.WordTrace]
  refine ⟨36289756043375617794666055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48386341391167490392888073 36289756043375617794666055)
  ·
    refine ⟨54434634065063426691999083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36289756043375617794666055 54434634065063426691999083)
    ·
      refine ⟨81651951097595140037998625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54434634065063426691999083 81651951097595140037998625)
      ·
        refine ⟨61238963323196355028498969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81651951097595140037998625 61238963323196355028498969)
        ·
          refine ⟨45929222492397266271374227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61238963323196355028498969 45929222492397266271374227)
          ·
            refine ⟨68893833738595899407061341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45929222492397266271374227 68893833738595899407061341)
            ·
              refine ⟨25835187651973462277648003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68893833738595899407061341 25835187651973462277648003)
              ·
                refine ⟨38752781477960193416472005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25835187651973462277648003 38752781477960193416472005)
                ·
                  refine ⟨7266146527117536265588501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38752781477960193416472005 7266146527117536265588501)
                  ·
                    refine ⟨340600618458634512449461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7266146527117536265588501 340600618458634512449461)
                    ·
                      rfl

theorem cell23_1989952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_1989952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989952 prefixEnd_1989952 := by exact prefixLift 1989952
  have htrace : WordTrace (prefixWord ++ tailWord_1989952) baseStart_1989952 baseEnd_1989952 := by
    simpa [prefixWord, tailWord_1989952, baseEnd_1989952] using wordTrace_append hprefix tailTrace_1989952
  have hstable : (prefixWord ++ tailWord_1989952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989952).length < 2 ^ (prefixWord ++ tailWord_1989952).sum := by decide
  have hdescent : baseEnd_1989952 < baseStart_1989952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989953 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1989953 : Nat := 118140960795 + 1989953 * 2 ^ 59
def prefixEnd_1989953 : Nat := 4983230072969 + 3 ^ 40 * 1989953 * 2
def baseEnd_1989953 : Nat := 1021802368856558033435879

theorem tailTrace_1989953 : CollatzResearch.WordTrace tailWord_1989953 prefixEnd_1989953 1021802368856558033435879 := by
  unfold tailWord_1989953
  simp only [CollatzResearch.WordTrace]
  refine ⟨72579548559747612760118513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48386365706498408506745675 72579548559747612760118513)
  ·
    refine ⟨54434661419810709570088885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72579548559747612760118513 54434661419810709570088885)
    ·
      refine ⟨5103249508107254022195833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54434661419810709570088885 5103249508107254022195833)
      ·
        refine ⟨3827437131080440516646875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5103249508107254022195833 3827437131080440516646875)
        ·
          refine ⟨5741155696620660774970313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827437131080440516646875 5741155696620660774970313)
          ·
            refine ⟨4305866772465495581227735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5741155696620660774970313 4305866772465495581227735)
            ·
              refine ⟨6458800158698243371841603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305866772465495581227735 6458800158698243371841603)
              ·
                refine ⟨9688200238047365057762405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458800158698243371841603 9688200238047365057762405)
                ·
                  refine ⟨1816537544633880948330451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9688200238047365057762405 1816537544633880948330451)
                  ·
                    refine ⟨2724806316950821422495677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1816537544633880948330451 2724806316950821422495677)
                    ·
                      refine ⟨1021802368856558033435879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2724806316950821422495677 1021802368856558033435879)
                      ·
                        rfl

theorem cell23_1989953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1989953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989953 prefixEnd_1989953 := by exact prefixLift 1989953
  have htrace : WordTrace (prefixWord ++ tailWord_1989953) baseStart_1989953 baseEnd_1989953 := by
    simpa [prefixWord, tailWord_1989953, baseEnd_1989953] using wordTrace_append hprefix tailTrace_1989953
  have hstable : (prefixWord ++ tailWord_1989953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989953).length < 2 ^ (prefixWord ++ tailWord_1989953).sum := by decide
  have hdescent : baseEnd_1989953 < baseStart_1989953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989974 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1989974 : Nat := 118140960795 + 1989974 * 2 ^ 59
def prefixEnd_1989974 : Nat := 4983230072969 + 3 ^ 40 * 1989974 * 2
def baseEnd_1989974 : Nat := 1021813151950302451273283

theorem tailTrace_1989974 : CollatzResearch.WordTrace tailWord_1989974 prefixEnd_1989974 1021813151950302451273283 := by
  unfold tailWord_1989974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4536269655791970834164561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48386876328447688897755317 4536269655791970834164561)
  ·
    refine ⟨3402202241843978125623421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4536269655791970834164561 3402202241843978125623421)
    ·
      refine ⟨1275825840691491797108783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3402202241843978125623421 1275825840691491797108783)
      ·
        refine ⟨1913738761037237695663175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275825840691491797108783 1913738761037237695663175)
        ·
          refine ⟨2870608141555856543494763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913738761037237695663175 2870608141555856543494763)
          ·
            refine ⟨4305912212333784815242145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870608141555856543494763 4305912212333784815242145)
            ·
              refine ⟨3229434159250338611431609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4305912212333784815242145 3229434159250338611431609)
              ·
                refine ⟨2422075619437753958573707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3229434159250338611431609 2422075619437753958573707)
                ·
                  refine ⟨3633113429156630937860561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422075619437753958573707 3633113429156630937860561)
                  ·
                    refine ⟨2724835071867473203395421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3633113429156630937860561 2724835071867473203395421)
                    ·
                      refine ⟨1021813151950302451273283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2724835071867473203395421 1021813151950302451273283)
                      ·
                        rfl

theorem cell23_1989974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1989974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1989974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1989974 prefixEnd_1989974 := by exact prefixLift 1989974
  have htrace : WordTrace (prefixWord ++ tailWord_1989974) baseStart_1989974 baseEnd_1989974 := by
    simpa [prefixWord, tailWord_1989974, baseEnd_1989974] using wordTrace_append hprefix tailTrace_1989974
  have hstable : (prefixWord ++ tailWord_1989974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989974).length < 2 ^ (prefixWord ++ tailWord_1989974).sum := by decide
  have hdescent : baseEnd_1989974 < baseStart_1989974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990009 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 4, 3, 3]
def baseStart_1990009 : Nat := 118140960795 + 1990009 * 2 ^ 59
def prefixEnd_1990009 : Nat := 4983230072969 + 3 ^ 40 * 1990009 * 2
def baseEnd_1990009 : Nat := 1021831123773209814335621

theorem tailTrace_1990009 : CollatzResearch.WordTrace tailWord_1990009 prefixEnd_1990009 1021831123773209814335621 := by
  unfold tailWord_1990009
  simp only [CollatzResearch.WordTrace]
  refine ⟨72581591047544734324157081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48387727365029822882771387 72581591047544734324157081)
  ·
    refine ⟨54436193285658550743117811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72581591047544734324157081 54436193285658550743117811)
    ·
      refine ⟨81654289928487826114676717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54436193285658550743117811 81654289928487826114676717)
      ·
        refine ⟨30620358723182934793003769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81654289928487826114676717 30620358723182934793003769)
        ·
          refine ⟨22965269042387201094752827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30620358723182934793003769 22965269042387201094752827)
          ·
            refine ⟨34447903563580801642129241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22965269042387201094752827 34447903563580801642129241)
            ·
              refine ⟨25835927672685601231596931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34447903563580801642129241 25835927672685601231596931)
              ·
                refine ⟨38753891509028401847395397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25835927672685601231596931 38753891509028401847395397)
                ·
                  refine ⟨7266354657942825346386637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38753891509028401847395397 7266354657942825346386637)
                  ·
                    refine ⟨2724882996728559504894989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7266354657942825346386637 2724882996728559504894989)
                    ·
                      refine ⟨1021831123773209814335621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2724882996728559504894989 1021831123773209814335621)
                      ·
                        rfl

theorem cell23_1990009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_1990009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990009 prefixEnd_1990009 := by exact prefixLift 1990009
  have htrace : WordTrace (prefixWord ++ tailWord_1990009) baseStart_1990009 baseEnd_1990009 := by
    simpa [prefixWord, tailWord_1990009, baseEnd_1990009] using wordTrace_append hprefix tailTrace_1990009
  have hstable : (prefixWord ++ tailWord_1990009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990009).length < 2 ^ (prefixWord ++ tailWord_1990009).sum := by decide
  have hdescent : baseEnd_1990009 < baseStart_1990009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990100 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_1990100 : Nat := 118140960795 + 1990100 * 2 ^ 59
def prefixEnd_1990100 : Nat := 4983230072969 + 3 ^ 40 * 1990100 * 2
def baseEnd_1990100 : Nat := 1021877850512768958297703

theorem tailTrace_1990100 : CollatzResearch.WordTrace tailWord_1990100 prefixEnd_1990100 1021877850512768958297703 := by
  unfold tailWord_1990100
  simp only [CollatzResearch.WordTrace]
  refine ⟨36292455045107528432859877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48389940060143371243813169 36292455045107528432859877)
  ·
    refine ⟨6804835320957661581161227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36292455045107528432859877 6804835320957661581161227)
    ·
      refine ⟨10207252981436492371741841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6804835320957661581161227 10207252981436492371741841)
      ·
        refine ⟨7655439736077369278806381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10207252981436492371741841 7655439736077369278806381)
        ·
          refine ⟨2870789901029013479552393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7655439736077369278806381 2870789901029013479552393)
          ·
            refine ⟨2153092425771760109664295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2870789901029013479552393 2153092425771760109664295)
            ·
              refine ⟨3229638638657640164496443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153092425771760109664295 3229638638657640164496443)
              ·
                refine ⟨4844457957986460246744665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229638638657640164496443 4844457957986460246744665)
                ·
                  refine ⟨3633343468489845185058499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4844457957986460246744665 3633343468489845185058499)
                  ·
                    refine ⟨5450015202734767777587749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3633343468489845185058499 5450015202734767777587749)
                    ·
                      refine ⟨1021877850512768958297703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5450015202734767777587749 1021877850512768958297703)
                      ·
                        rfl

theorem cell23_1990100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_1990100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990100 prefixEnd_1990100 := by exact prefixLift 1990100
  have htrace : WordTrace (prefixWord ++ tailWord_1990100) baseStart_1990100 baseEnd_1990100 := by
    simpa [prefixWord, tailWord_1990100, baseEnd_1990100] using wordTrace_append hprefix tailTrace_1990100
  have hstable : (prefixWord ++ tailWord_1990100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990100).length < 2 ^ (prefixWord ++ tailWord_1990100).sum := by decide
  have hdescent : baseEnd_1990100 < baseStart_1990100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990169 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_1990169 : Nat := 118140960795 + 1990169 * 2 ^ 59
def prefixEnd_1990169 : Nat := 4983230072969 + 3 ^ 40 * 1990169 * 2
def baseEnd_1990169 : Nat := 1021913280677929188334885

theorem tailTrace_1990169 : CollatzResearch.WordTrace tailWord_1990169 prefixEnd_1990169 1021913280677929188334885 := by
  unfold tailWord_1990169
  simp only [CollatzResearch.WordTrace]
  refine ⟨72587426726965081649981561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48391617817976721099987707 72587426726965081649981561)
  ·
    refine ⟨54440570045223811237486171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72587426726965081649981561 54440570045223811237486171)
    ·
      refine ⟨81660855067835716856229257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54440570045223811237486171 81660855067835716856229257)
      ·
        refine ⟨61245641300876787642171943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81660855067835716856229257 61245641300876787642171943)
        ·
          refine ⟨91868461951315181463257915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61245641300876787642171943 91868461951315181463257915)
          ·
            refine ⟨137802692926972772194886873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91868461951315181463257915 137802692926972772194886873)
            ·
              refine ⟨103352019695229579146165155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137802692926972772194886873 103352019695229579146165155)
              ·
                refine ⟨155028029542844368719247733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103352019695229579146165155 155028029542844368719247733)
                ·
                  refine ⟨14533877769641659567429475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155028029542844368719247733 14533877769641659567429475)
                  ·
                    refine ⟨21800816654462489351144213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14533877769641659567429475 21800816654462489351144213)
                    ·
                      refine ⟨1021913280677929188334885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21800816654462489351144213 1021913280677929188334885)
                      ·
                        rfl

theorem cell23_1990169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_1990169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990169 prefixEnd_1990169 := by exact prefixLift 1990169
  have htrace : WordTrace (prefixWord ++ tailWord_1990169) baseStart_1990169 baseEnd_1990169 := by
    simpa [prefixWord, tailWord_1990169, baseEnd_1990169] using wordTrace_append hprefix tailTrace_1990169
  have hstable : (prefixWord ++ tailWord_1990169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990169).length < 2 ^ (prefixWord ++ tailWord_1990169).sum := by decide
  have hdescent : baseEnd_1990169 < baseStart_1990169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990173 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_1990173 : Nat := 118140960795 + 1990173 * 2 ^ 59
def prefixEnd_1990173 : Nat := 4983230072969 + 3 ^ 40 * 1990173 * 2
def baseEnd_1990173 : Nat := 1021915334600547172684867

theorem tailTrace_1990173 : CollatzResearch.WordTrace tailWord_1990173 prefixEnd_1990173 1021915334600547172684867 := by
  unfold tailWord_1990173
  simp only [CollatzResearch.WordTrace]
  refine ⟨72587572618950590333127173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48391715079300393555418115 72587572618950590333127173)
  ·
    refine ⟨13610169866053235687461345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72587572618950590333127173 13610169866053235687461345)
    ·
      refine ⟨10207627399539926765596009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13610169866053235687461345 10207627399539926765596009)
      ·
        refine ⟨7655720549654945074197007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10207627399539926765596009 7655720549654945074197007)
        ·
          refine ⟨11483580824482417611295511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655720549654945074197007 11483580824482417611295511)
          ·
            refine ⟨17225371236723626416943267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11483580824482417611295511 17225371236723626416943267)
            ·
              refine ⟨25838056855085439625414901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17225371236723626416943267 25838056855085439625414901)
              ·
                refine ⟨2422317830164259964882647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25838056855085439625414901 2422317830164259964882647)
                ·
                  refine ⟨3633476745246389947323971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422317830164259964882647 3633476745246389947323971)
                  ·
                    refine ⟨5450215117869584920985957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3633476745246389947323971 5450215117869584920985957)
                    ·
                      refine ⟨1021915334600547172684867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5450215117869584920985957 1021915334600547172684867)
                      ·
                        rfl

theorem cell23_1990173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_1990173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990173 prefixEnd_1990173 := by exact prefixLift 1990173
  have htrace : WordTrace (prefixWord ++ tailWord_1990173) baseStart_1990173 baseEnd_1990173 := by
    simpa [prefixWord, tailWord_1990173, baseEnd_1990173] using wordTrace_append hprefix tailTrace_1990173
  have hstable : (prefixWord ++ tailWord_1990173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990173).length < 2 ^ (prefixWord ++ tailWord_1990173).sum := by decide
  have hdescent : baseEnd_1990173 < baseStart_1990173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990184 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_1990184 : Nat := 118140960795 + 1990184 * 2 ^ 59
def prefixEnd_1990184 : Nat := 4983230072969 + 3 ^ 40 * 1990184 * 2
def baseEnd_1990184 : Nat := 1021920982887746629647317

theorem tailTrace_1990184 : CollatzResearch.WordTrace tailWord_1990184 prefixEnd_1990184 1021920982887746629647317 := by
  unfold tailWord_1990184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36293986910955369605888803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48391982547940492807851737 36293986910955369605888803)
  ·
    refine ⟨54440980366433054408833205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36293986910955369605888803 54440980366433054408833205)
    ·
      refine ⟨5103841909353098850828113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54440980366433054408833205 5103841909353098850828113)
      ·
        refine ⟨3827881432014824138121085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5103841909353098850828113 3827881432014824138121085)
        ·
          refine ⟨1435455537005559051795407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3827881432014824138121085 1435455537005559051795407)
          ·
            refine ⟨2153183305508338577693111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435455537005559051795407 2153183305508338577693111)
            ·
              refine ⟨3229774958262507866539667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153183305508338577693111 3229774958262507866539667)
              ·
                refine ⟨4844662437393761799809501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229774958262507866539667 4844662437393761799809501)
                ·
                  refine ⟨1816748414022660674928563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4844662437393761799809501 1816748414022660674928563)
                  ·
                    refine ⟨2725122621033991012392845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1816748414022660674928563 2725122621033991012392845)
                    ·
                      refine ⟨1021920982887746629647317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2725122621033991012392845 1021920982887746629647317)
                      ·
                        rfl

theorem cell23_1990184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_1990184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990184 prefixEnd_1990184 := by exact prefixLift 1990184
  have htrace : WordTrace (prefixWord ++ tailWord_1990184) baseStart_1990184 baseEnd_1990184 := by
    simpa [prefixWord, tailWord_1990184, baseEnd_1990184] using wordTrace_append hprefix tailTrace_1990184
  have hstable : (prefixWord ++ tailWord_1990184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990184).length < 2 ^ (prefixWord ++ tailWord_1990184).sum := by decide
  have hdescent : baseEnd_1990184 < baseStart_1990184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990186 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1990186 : Nat := 118140960795 + 1990186 * 2 ^ 59
def prefixEnd_1990186 : Nat := 4983230072969 + 3 ^ 40 * 1990186 * 2
def baseEnd_1990186 : Nat := 1021922009849055621822307

theorem tailTrace_1990186 : CollatzResearch.WordTrace tailWord_1990186 prefixEnd_1990186 1021922009849055621822307 := by
  unfold tailWord_1990186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147011691975873388337603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48392031178602329035566941 18147011691975873388337603)
  ·
    refine ⟨27220517537963810082506405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18147011691975873388337603 27220517537963810082506405)
    ·
      refine ⟨5103847038368214390469951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27220517537963810082506405 5103847038368214390469951)
      ·
        refine ⟨7655770557552321585704927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5103847038368214390469951 7655770557552321585704927)
        ·
          refine ⟨11483655836328482378557391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655770557552321585704927 11483655836328482378557391)
          ·
            refine ⟨17225483754492723567836087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11483655836328482378557391 17225483754492723567836087)
            ·
              refine ⟨25838225631739085351754131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17225483754492723567836087 25838225631739085351754131)
              ·
                refine ⟨38757338447608628027631197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25838225631739085351754131 38757338447608628027631197)
                ·
                  refine ⟨14534001917853235510361699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38757338447608628027631197 14534001917853235510361699)
                  ·
                    refine ⟨21801002876779853265542549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14534001917853235510361699 21801002876779853265542549)
                    ·
                      refine ⟨1021922009849055621822307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21801002876779853265542549 1021922009849055621822307)
                      ·
                        rfl

theorem cell23_1990186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1990186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990186 prefixEnd_1990186 := by exact prefixLift 1990186
  have htrace : WordTrace (prefixWord ++ tailWord_1990186) baseStart_1990186 baseEnd_1990186 := by
    simpa [prefixWord, tailWord_1990186, baseEnd_1990186] using wordTrace_append hprefix tailTrace_1990186
  have hstable : (prefixWord ++ tailWord_1990186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990186).length < 2 ^ (prefixWord ++ tailWord_1990186).sum := by decide
  have hdescent : baseEnd_1990186 < baseStart_1990186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990200 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 2, 4]
def baseStart_1990200 : Nat := 118140960795 + 1990200 * 2 ^ 59
def prefixEnd_1990200 : Nat := 4983230072969 + 3 ^ 40 * 1990200 * 2
def baseEnd_1990200 : Nat := 340643066192739522349081

theorem tailTrace_1990200 : CollatzResearch.WordTrace tailWord_1990200 prefixEnd_1990200 340643066192739522349081 := by
  unfold tailWord_1990200
  simp only [CollatzResearch.WordTrace]
  refine ⟨36294278694926386972180027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48392371593235182629573369 36294278694926386972180027)
  ·
    refine ⟨54441418042389580458270041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36294278694926386972180027 54441418042389580458270041)
    ·
      refine ⟨40831063531792185343702531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54441418042389580458270041 40831063531792185343702531)
      ·
        refine ⟨61246595297688278015553797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40831063531792185343702531 61246595297688278015553797)
        ·
          refine ⟨11483736618316552127916337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61246595297688278015553797 11483736618316552127916337)
          ·
            refine ⟨8612802463737414095937253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11483736618316552127916337 8612802463737414095937253)
            ·
              refine ⟨1614900461950765142988235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8612802463737414095937253 1614900461950765142988235)
              ·
                refine ⟨2422350692926147714482353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614900461950765142988235 2422350692926147714482353)
                ·
                  refine ⟨1816763019694610785861765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2422350692926147714482353 1816763019694610785861765)
                  ·
                    refine ⟨340643066192739522349081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1816763019694610785861765 340643066192739522349081)
                    ·
                      rfl

theorem cell23_1990200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_1990200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990200 prefixEnd_1990200 := by exact prefixLift 1990200
  have htrace : WordTrace (prefixWord ++ tailWord_1990200) baseStart_1990200 baseEnd_1990200 := by
    simpa [prefixWord, tailWord_1990200, baseEnd_1990200] using wordTrace_append hprefix tailTrace_1990200
  have hstable : (prefixWord ++ tailWord_1990200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990200).length < 2 ^ (prefixWord ++ tailWord_1990200).sum := by decide
  have hdescent : baseEnd_1990200 < baseStart_1990200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990230 : List Nat := [5, 2, 2, 2, 1, 11]
def baseStart_1990230 : Nat := 118140960795 + 1990230 * 2 ^ 59
def prefixEnd_1990230 : Nat := 4983230072969 + 3 ^ 40 * 1990230 * 2
def baseEnd_1990230 : Nat := 4205533345670178805235

theorem tailTrace_1990230 : CollatzResearch.WordTrace tailWord_1990230 prefixEnd_1990230 4205533345670178805235 := by
  unfold tailWord_1990230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4536853223734005566747009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48393101053162726045301429 4536853223734005566747009)
  ·
    refine ⟨3402639917800504175060257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4536853223734005566747009 3402639917800504175060257)
    ·
      refine ⟨2551979938350378131295193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3402639917800504175060257 2551979938350378131295193)
      ·
        refine ⟨1913984953762783598471395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2551979938350378131295193 1913984953762783598471395)
        ·
          refine ⟨2870977430644175397707093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913984953762783598471395 2870977430644175397707093)
          ·
            refine ⟨4205533345670178805235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2870977430644175397707093 4205533345670178805235)
            ·
              rfl

theorem cell23_1990230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 11].length) (baseStart_1990230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990230 prefixEnd_1990230 := by exact prefixLift 1990230
  have htrace : WordTrace (prefixWord ++ tailWord_1990230) baseStart_1990230 baseEnd_1990230 := by
    simpa [prefixWord, tailWord_1990230, baseEnd_1990230] using wordTrace_append hprefix tailTrace_1990230
  have hstable : (prefixWord ++ tailWord_1990230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990230).length < 2 ^ (prefixWord ++ tailWord_1990230).sum := by decide
  have hdescent : baseEnd_1990230 < baseStart_1990230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990250 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_1990250 : Nat := 118140960795 + 1990250 * 2 ^ 59
def prefixEnd_1990250 : Nat := 4983230072969 + 3 ^ 40 * 1990250 * 2
def baseEnd_1990250 : Nat := 1021954872610943371422013

theorem tailTrace_1990250 : CollatzResearch.WordTrace tailWord_1990250 prefixEnd_1990250 1021954872610943371422013 := by
  unfold tailWord_1990250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147595259917908120920051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48393587359781088322453469 18147595259917908120920051)
  ·
    refine ⟨27221392889876862181380077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18147595259917908120920051 27221392889876862181380077)
    ·
      refine ⟨10208022333703823318017529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27221392889876862181380077 10208022333703823318017529)
      ·
        refine ⟨7656016750277867488513147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10208022333703823318017529 7656016750277867488513147)
        ·
          refine ⟨11484025125416801232769721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7656016750277867488513147 11484025125416801232769721)
          ·
            refine ⟨8613018844062600924577291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11484025125416801232769721 8613018844062600924577291)
            ·
              refine ⟨12919528266093901386865937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613018844062600924577291 12919528266093901386865937)
              ·
                refine ⟨9689646199570426040149453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12919528266093901386865937 9689646199570426040149453)
                ·
                  refine ⟨3633617324838909765056045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9689646199570426040149453 3633617324838909765056045)
                  ·
                    refine ⟨1362606496814591161896017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3633617324838909765056045 1362606496814591161896017)
                    ·
                      refine ⟨1021954872610943371422013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1362606496814591161896017 1021954872610943371422013)
                      ·
                        rfl

theorem cell23_1990250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_1990250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990250 prefixEnd_1990250 := by exact prefixLift 1990250
  have htrace : WordTrace (prefixWord ++ tailWord_1990250) baseStart_1990250 baseEnd_1990250 := by
    simpa [prefixWord, tailWord_1990250, baseEnd_1990250] using wordTrace_append hprefix tailTrace_1990250
  have hstable : (prefixWord ++ tailWord_1990250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990250).length < 2 ^ (prefixWord ++ tailWord_1990250).sum := by decide
  have hdescent : baseEnd_1990250 < baseStart_1990250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990256 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 1, 8]
def baseStart_1990256 : Nat := 118140960795 + 1990256 * 2 ^ 59
def prefixEnd_1990256 : Nat := 4983230072969 + 3 ^ 40 * 1990256 * 2
def baseEnd_1990256 : Nat := 340652651164956782648995

theorem tailTrace_1990256 : CollatzResearch.WordTrace tailWord_1990256 prefixEnd_1990256 340652651164956782648995 := by
  unfold tailWord_1990256
  simp only [CollatzResearch.WordTrace]
  refine ⟨36295299938824947754199311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48393733251766597005599081 36295299938824947754199311)
  ·
    refine ⟨54442949908237421631298967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36295299938824947754199311 54442949908237421631298967)
    ·
      refine ⟨81664424862356132446948451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54442949908237421631298967 81664424862356132446948451)
      ·
        refine ⟨122496637293534198670422677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81664424862356132446948451 122496637293534198670422677)
        ·
          refine ⟨5742029873134415562676063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122496637293534198670422677 5742029873134415562676063)
          ·
            refine ⟨8613044809701623344014095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742029873134415562676063 8613044809701623344014095)
            ·
              refine ⟨12919567214552435016021143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613044809701623344014095 12919567214552435016021143)
              ·
                refine ⟨19379350821828652524031715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12919567214552435016021143 19379350821828652524031715)
                ·
                  refine ⟨29069026232742978786047573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19379350821828652524031715 29069026232742978786047573)
                  ·
                    refine ⟨340652651164956782648995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29069026232742978786047573 340652651164956782648995)
                    ·
                      rfl

theorem cell23_1990256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_1990256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990256 prefixEnd_1990256 := by exact prefixLift 1990256
  have htrace : WordTrace (prefixWord ++ tailWord_1990256) baseStart_1990256 baseEnd_1990256 := by
    simpa [prefixWord, tailWord_1990256, baseEnd_1990256] using wordTrace_append hprefix tailTrace_1990256
  have hstable : (prefixWord ++ tailWord_1990256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990256).length < 2 ^ (prefixWord ++ tailWord_1990256).sum := by decide
  have hdescent : baseEnd_1990256 < baseStart_1990256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990266 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_1990266 : Nat := 118140960795 + 1990266 * 2 ^ 59
def prefixEnd_1990266 : Nat := 4983230072969 + 3 ^ 40 * 1990266 * 2
def baseEnd_1990266 : Nat := 1021963088301415308821939

theorem tailTrace_1990266 : CollatzResearch.WordTrace tailWord_1990266 prefixEnd_1990266 1021963088301415308821939 := by
  unfold tailWord_1990266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147741151903416804065663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48393976405075778144175101 18147741151903416804065663)
  ·
    refine ⟨27221611727855125206098495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18147741151903416804065663 27221611727855125206098495)
    ·
      refine ⟨40832417591782687809147743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27221611727855125206098495 40832417591782687809147743)
      ·
        refine ⟨61248626387674031713721615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40832417591782687809147743 61248626387674031713721615)
        ·
          refine ⟨91872939581511047570582423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61248626387674031713721615 91872939581511047570582423)
          ·
            refine ⟨137809409372266571355873635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91872939581511047570582423 137809409372266571355873635)
            ·
              refine ⟨206714114058399857033810453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137809409372266571355873635 206714114058399857033810453)
              ·
                refine ⟨9689724096487493298459865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206714114058399857033810453 9689724096487493298459865)
                ·
                  refine ⟨7267293072365619973844899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9689724096487493298459865 7267293072365619973844899)
                  ·
                    refine ⟨10900939608548429960767349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7267293072365619973844899 10900939608548429960767349)
                    ·
                      refine ⟨1021963088301415308821939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10900939608548429960767349 1021963088301415308821939)
                      ·
                        rfl

theorem cell23_1990266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_1990266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990266 prefixEnd_1990266 := by exact prefixLift 1990266
  have htrace : WordTrace (prefixWord ++ tailWord_1990266) baseStart_1990266 baseEnd_1990266 := by
    simpa [prefixWord, tailWord_1990266, baseEnd_1990266] using wordTrace_append hprefix tailTrace_1990266
  have hstable : (prefixWord ++ tailWord_1990266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990266).length < 2 ^ (prefixWord ++ tailWord_1990266).sum := by decide
  have hdescent : baseEnd_1990266 < baseStart_1990266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990333 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_1990333 : Nat := 118140960795 + 1990333 * 2 ^ 59
def prefixEnd_1990333 : Nat := 4983230072969 + 3 ^ 40 * 1990333 * 2
def baseEnd_1990333 : Nat := 340665830501755515561377

theorem tailTrace_1990333 : CollatzResearch.WordTrace tailWord_1990333 prefixEnd_1990333 340665830501755515561377 := by
  unfold tailWord_1990333
  simp only [CollatzResearch.WordTrace]
  refine ⟨72593408298370937658951653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48395605532247291772634435 72593408298370937658951653)
  ·
    refine ⟨13611264055944550811053435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72593408298370937658951653 13611264055944550811053435)
    ·
      refine ⟨20416896083916826216580153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13611264055944550811053435 20416896083916826216580153)
      ·
        refine ⟨15312672062937619662435115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20416896083916826216580153 15312672062937619662435115)
        ·
          refine ⟨22969008094406429493652673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15312672062937619662435115 22969008094406429493652673)
          ·
            refine ⟨17226756070804822120239505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22969008094406429493652673 17226756070804822120239505)
            ·
              refine ⟨12920067053103616590179629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17226756070804822120239505 12920067053103616590179629)
              ·
                refine ⟨4845025144913856221317361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12920067053103616590179629 4845025144913856221317361)
                ·
                  refine ⟨3633768858685392165988021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4845025144913856221317361 3633768858685392165988021)
                  ·
                    refine ⟨340665830501755515561377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3633768858685392165988021 340665830501755515561377)
                    ·
                      rfl

theorem cell23_1990333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_1990333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990333 prefixEnd_1990333 := by exact prefixLift 1990333
  have htrace : WordTrace (prefixWord ++ tailWord_1990333) baseStart_1990333 baseEnd_1990333 := by
    simpa [prefixWord, tailWord_1990333, baseEnd_1990333] using wordTrace_append hprefix tailTrace_1990333
  have hstable : (prefixWord ++ tailWord_1990333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990333).length < 2 ^ (prefixWord ++ tailWord_1990333).sum := by decide
  have hdescent : baseEnd_1990333 < baseStart_1990333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990353 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_1990353 : Nat := 118140960795 + 1990353 * 2 ^ 59
def prefixEnd_1990353 : Nat := 4983230072969 + 3 ^ 40 * 1990353 * 2
def baseEnd_1990353 : Nat := 1022007761118356468434039

theorem tailTrace_1990353 : CollatzResearch.WordTrace tailWord_1990353 prefixEnd_1990353 1022007761118356468434039 := by
  unfold tailWord_1990353
  simp only [CollatzResearch.WordTrace]
  refine ⟨72594137758298481074679713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48396091838865654049786475 72594137758298481074679713)
  ·
    refine ⟨54445603318723860806009785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72594137758298481074679713 54445603318723860806009785)
    ·
      refine ⟨40834202489042895604507339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54445603318723860806009785 40834202489042895604507339)
      ·
        refine ⟨61251303733564343406761009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40834202489042895604507339 61251303733564343406761009)
        ·
          refine ⟨45938477800173257555070757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61251303733564343406761009 45938477800173257555070757)
          ·
            refine ⟨8613464587532485791575767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45938477800173257555070757 8613464587532485791575767)
            ·
              refine ⟨12920196881298728687363651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613464587532485791575767 12920196881298728687363651)
              ·
                refine ⟨19380295321948093031045477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12920196881298728687363651 19380295321948093031045477)
                ·
                  refine ⟨3633805372865267443321027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19380295321948093031045477 3633805372865267443321027)
                  ·
                    refine ⟨5450708059297901164981541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3633805372865267443321027 5450708059297901164981541)
                    ·
                      refine ⟨1022007761118356468434039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5450708059297901164981541 1022007761118356468434039)
                      ·
                        rfl

theorem cell23_1990353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_1990353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990353 prefixEnd_1990353 := by exact prefixLift 1990353
  have htrace : WordTrace (prefixWord ++ tailWord_1990353) baseStart_1990353 baseEnd_1990353 := by
    simpa [prefixWord, tailWord_1990353, baseEnd_1990353] using wordTrace_append hprefix tailTrace_1990353
  have hstable : (prefixWord ++ tailWord_1990353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990353).length < 2 ^ (prefixWord ++ tailWord_1990353).sum := by decide
  have hdescent : baseEnd_1990353 < baseStart_1990353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990365 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1990365 : Nat := 118140960795 + 1990365 * 2 ^ 59
def prefixEnd_1990365 : Nat := 4983230072969 + 3 ^ 40 * 1990365 * 2
def baseEnd_1990365 : Nat := 1022013922886210421483985

theorem tailTrace_1990365 : CollatzResearch.WordTrace tailWord_1990365 prefixEnd_1990365 1022013922886210421483985 := by
  unfold tailWord_1990365
  simp only [CollatzResearch.WordTrace]
  refine ⟨72594575434255007124116549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48396383622836671416077699 72594575434255007124116549)
  ·
    refine ⟨13611482893922813835771853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72594575434255007124116549 13611482893922813835771853)
    ·
      refine ⟨5104306085221055188414445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13611482893922813835771853 5104306085221055188414445)
      ·
        refine ⟨1914114781957895695655417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5104306085221055188414445 1914114781957895695655417)
        ·
          refine ⟨1435586086468421771741563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1914114781957895695655417 1435586086468421771741563)
          ·
            refine ⟨2153379129702632657612345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435586086468421771741563 2153379129702632657612345)
            ·
              refine ⟨1615034347276974493209259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2153379129702632657612345 1615034347276974493209259)
              ·
                refine ⟨2422551520915461739813889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615034347276974493209259 2422551520915461739813889)
                ·
                  refine ⟨1816913640686596304860417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2422551520915461739813889 1816913640686596304860417)
                  ·
                    refine ⟨1362685230514947228645313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1816913640686596304860417 1362685230514947228645313)
                    ·
                      refine ⟨1022013922886210421483985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1362685230514947228645313 1022013922886210421483985)
                      ·
                        rfl

theorem cell23_1990365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1990365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990365 prefixEnd_1990365 := by exact prefixLift 1990365
  have htrace : WordTrace (prefixWord ++ tailWord_1990365) baseStart_1990365 baseEnd_1990365 := by
    simpa [prefixWord, tailWord_1990365, baseEnd_1990365] using wordTrace_append hprefix tailTrace_1990365
  have hstable : (prefixWord ++ tailWord_1990365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990365).length < 2 ^ (prefixWord ++ tailWord_1990365).sum := by decide
  have hdescent : baseEnd_1990365 < baseStart_1990365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990410 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 6]
def baseStart_1990410 : Nat := 118140960795 + 1990410 * 2 ^ 59
def prefixEnd_1990410 : Nat := 4983230072969 + 3 ^ 40 * 1990410 * 2
def baseEnd_1990410 : Nat := 113559669946184749491253

theorem tailTrace_1990410 : CollatzResearch.WordTrace tailWord_1990410 prefixEnd_1990410 113559669946184749491253 := by
  unfold tailWord_1990410
  simp only [CollatzResearch.WordTrace]
  refine ⟨18149054179772994952376171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48397477812727986539669789 18149054179772994952376171)
  ·
    refine ⟨27223581269659492428564257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18149054179772994952376171 27223581269659492428564257)
    ·
      refine ⟨20417685952244619321423193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27223581269659492428564257 20417685952244619321423193)
      ·
        refine ⟨15313264464183464491067395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20417685952244619321423193 15313264464183464491067395)
        ·
          refine ⟨22969896696275196736601093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15313264464183464491067395 22969896696275196736601093)
          ·
            refine ⟨4306855630551599388112705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22969896696275196736601093 4306855630551599388112705)
            ·
              refine ⟨3230141722913699541084529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4306855630551599388112705 3230141722913699541084529)
              ·
                refine ⟨2422606292185274655813397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230141722913699541084529 2422606292185274655813397)
                ·
                  refine ⟨113559669946184749491253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2422606292185274655813397 113559669946184749491253)
                  ·
                    rfl

theorem cell23_1990410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_1990410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990410 prefixEnd_1990410 := by exact prefixLift 1990410
  have htrace : WordTrace (prefixWord ++ tailWord_1990410) baseStart_1990410 baseEnd_1990410 := by
    simpa [prefixWord, tailWord_1990410, baseEnd_1990410] using wordTrace_append hprefix tailTrace_1990410
  have hstable : (prefixWord ++ tailWord_1990410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990410).length < 2 ^ (prefixWord ++ tailWord_1990410).sum := by decide
  have hdescent : baseEnd_1990410 < baseStart_1990410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990414 : List Nat := [4, 1, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_1990414 : Nat := 118140960795 + 1990414 * 2 ^ 59
def prefixEnd_1990414 : Nat := 4983230072969 + 3 ^ 40 * 1990414 * 2
def baseEnd_1990414 : Nat := 340679694479426909923753

theorem tailTrace_1990414 : CollatzResearch.WordTrace tailWord_1990414 prefixEnd_1990414 340679694479426909923753 := by
  unfold tailWord_1990414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9074545326384686061581287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48397575074051658995100197 9074545326384686061581287)
  ·
    refine ⟨13611817989577029092371931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9074545326384686061581287 13611817989577029092371931)
    ·
      refine ⟨20417726984365543638557897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13611817989577029092371931 20417726984365543638557897)
      ·
        refine ⟨15313295238274157728918423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20417726984365543638557897 15313295238274157728918423)
        ·
          refine ⟨22969942857411236593377635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15313295238274157728918423 22969942857411236593377635)
          ·
            refine ⟨34454914286116854890066453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22969942857411236593377635 34454914286116854890066453)
            ·
              refine ⟨1615074107161727572971865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34454914286116854890066453 1615074107161727572971865)
              ·
                refine ⟨1211305580371295679728899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615074107161727572971865 1211305580371295679728899)
                ·
                  refine ⟨1816958370556943519593349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211305580371295679728899 1816958370556943519593349)
                  ·
                    refine ⟨340679694479426909923753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1816958370556943519593349 340679694479426909923753)
                    ·
                      rfl

theorem cell23_1990414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_1990414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990414 prefixEnd_1990414 := by exact prefixLift 1990414
  have htrace : WordTrace (prefixWord ++ tailWord_1990414) baseStart_1990414 baseEnd_1990414 := by
    simpa [prefixWord, tailWord_1990414, baseEnd_1990414] using wordTrace_append hprefix tailTrace_1990414
  have hstable : (prefixWord ++ tailWord_1990414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990414).length < 2 ^ (prefixWord ++ tailWord_1990414).sum := by decide
  have hdescent : baseEnd_1990414 < baseStart_1990414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990437 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 3, 1, 3]
def baseStart_1990437 : Nat := 118140960795 + 1990437 * 2 ^ 59
def prefixEnd_1990437 : Nat := 4983230072969 + 3 ^ 40 * 1990437 * 2
def baseEnd_1990437 : Nat := 1022050893493334139783653

theorem tailTrace_1990437 : CollatzResearch.WordTrace tailWord_1990437 prefixEnd_1990437 1022050893493334139783653 := by
  unfold tailWord_1990437
  simp only [CollatzResearch.WordTrace]
  refine ⟨72597201489994163420737565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48398134326662775613825043 72597201489994163420737565)
  ·
    refine ⟨27223950558747811282776587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72597201489994163420737565 27223950558747811282776587)
    ·
      refine ⟨40835925838121716924164881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27223950558747811282776587 40835925838121716924164881)
      ·
        refine ⟨30626944378591287693123661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40835925838121716924164881 30626944378591287693123661)
        ·
          refine ⟨11485104141971732884921373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30626944378591287693123661 11485104141971732884921373)
          ·
            refine ⟨4306914053239399831845515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11485104141971732884921373 4306914053239399831845515)
            ·
              refine ⟨6460371079859099747768273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4306914053239399831845515 6460371079859099747768273)
              ·
                refine ⟨4845278309894324810826205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6460371079859099747768273 4845278309894324810826205)
                ·
                  refine ⟨1816979366210371804059827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4845278309894324810826205 1816979366210371804059827)
                  ·
                    refine ⟨2725469049315557706089741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1816979366210371804059827 2725469049315557706089741)
                    ·
                      refine ⟨1022050893493334139783653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2725469049315557706089741 1022050893493334139783653)
                      ·
                        rfl

theorem cell23_1990437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_1990437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990437 prefixEnd_1990437 := by exact prefixLift 1990437
  have htrace : WordTrace (prefixWord ++ tailWord_1990437) baseStart_1990437 baseEnd_1990437 := by
    simpa [prefixWord, tailWord_1990437, baseEnd_1990437] using wordTrace_append hprefix tailTrace_1990437
  have hstable : (prefixWord ++ tailWord_1990437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990437).length < 2 ^ (prefixWord ++ tailWord_1990437).sum := by decide
  have hdescent : baseEnd_1990437 < baseStart_1990437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990440 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1990440 : Nat := 118140960795 + 1990440 * 2 ^ 59
def prefixEnd_1990440 : Nat := 4983230072969 + 3 ^ 40 * 1990440 * 2
def baseEnd_1990440 : Nat := 340684144645099209348713

theorem tailTrace_1990440 : CollatzResearch.WordTrace tailWord_1990440 prefixEnd_1990440 340684144645099209348713 := by
  unfold tailWord_1990440
  simp only [CollatzResearch.WordTrace]
  refine ⟨36298655454491647466548387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48398207272655529955397849 36298655454491647466548387)
  ·
    refine ⟨54447983181737471199822581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36298655454491647466548387 54447983181737471199822581)
    ·
      refine ⟨5104498423287887924983367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54447983181737471199822581 5104498423287887924983367)
      ·
        refine ⟨7656747634931831887475051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5104498423287887924983367 7656747634931831887475051)
        ·
          refine ⟨11485121452397747831212577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7656747634931831887475051 11485121452397747831212577)
          ·
            refine ⟨8613841089298310873409433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11485121452397747831212577 8613841089298310873409433)
            ·
              refine ⟨6460380816973733155057075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8613841089298310873409433 6460380816973733155057075)
              ·
                refine ⟨9690571225460599732585613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460380816973733155057075 9690571225460599732585613)
                ·
                  refine ⟨3633964209547724899719605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9690571225460599732585613 3633964209547724899719605)
                  ·
                    refine ⟨340684144645099209348713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3633964209547724899719605 340684144645099209348713)
                    ·
                      rfl

theorem cell23_1990440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1990440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990440 prefixEnd_1990440 := by exact prefixLift 1990440
  have htrace : WordTrace (prefixWord ++ tailWord_1990440) baseStart_1990440 baseEnd_1990440 := by
    simpa [prefixWord, tailWord_1990440, baseEnd_1990440] using wordTrace_append hprefix tailTrace_1990440
  have hstable : (prefixWord ++ tailWord_1990440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990440).length < 2 ^ (prefixWord ++ tailWord_1990440).sum := by decide
  have hdescent : baseEnd_1990440 < baseStart_1990440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990443 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 4]
def baseStart_1990443 : Nat := 118140960795 + 1990443 * 2 ^ 59
def prefixEnd_1990443 : Nat := 4983230072969 + 3 ^ 40 * 1990443 * 2
def baseEnd_1990443 : Nat := 1022053974377261116308625

theorem tailTrace_1990443 : CollatzResearch.WordTrace tailWord_1990443 prefixEnd_1990443 1022053974377261116308625 := by
  unfold tailWord_1990443
  simp only [CollatzResearch.WordTrace]
  refine ⟨72597420327972426445455983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48398280218648284296970655 72597420327972426445455983)
  ·
    refine ⟨108896130491958639668183975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72597420327972426445455983 108896130491958639668183975)
    ·
      refine ⟨163344195737937959502275963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108896130491958639668183975 163344195737937959502275963)
      ·
        refine ⟨245016293606906939253413945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163344195737937959502275963 245016293606906939253413945)
        ·
          refine ⟨183762220205180204440060459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245016293606906939253413945 183762220205180204440060459)
          ·
            refine ⟨275643330307770306660090689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183762220205180204440060459 275643330307770306660090689)
            ·
              refine ⟨206732497730827729995068017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275643330307770306660090689 206732497730827729995068017)
              ·
                refine ⟨155049373298120797496301013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206732497730827729995068017 155049373298120797496301013)
                ·
                  refine ⟨3633969686674706191319555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 155049373298120797496301013 3633969686674706191319555)
                  ·
                    refine ⟨5450954530012059286979333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3633969686674706191319555 5450954530012059286979333)
                    ·
                      refine ⟨1022053974377261116308625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5450954530012059286979333 1022053974377261116308625)
                      ·
                        rfl

theorem cell23_1990443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 4].length) (baseStart_1990443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990443 prefixEnd_1990443 := by exact prefixLift 1990443
  have htrace : WordTrace (prefixWord ++ tailWord_1990443) baseStart_1990443 baseEnd_1990443 := by
    simpa [prefixWord, tailWord_1990443, baseEnd_1990443] using wordTrace_append hprefix tailTrace_1990443
  have hstable : (prefixWord ++ tailWord_1990443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990443).length < 2 ^ (prefixWord ++ tailWord_1990443).sum := by decide
  have hdescent : baseEnd_1990443 < baseStart_1990443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990473 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 6]
def baseStart_1990473 : Nat := 118140960795 + 1990473 * 2 ^ 59
def prefixEnd_1990473 : Nat := 4983230072969 + 3 ^ 40 * 1990473 * 2
def baseEnd_1990473 : Nat := 1022069378796895998933487

theorem tailTrace_1990473 : CollatzResearch.WordTrace tailWord_1990473 prefixEnd_1990473 1022069378796895998933487 := by
  unfold tailWord_1990473
  simp only [CollatzResearch.WordTrace]
  refine ⟨72598514517863741569048073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48399009678575827712698715 72598514517863741569048073)
  ·
    refine ⟨54448885888397806176786055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72598514517863741569048073 54448885888397806176786055)
    ·
      refine ⟨81673328832596709265179083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54448885888397806176786055 81673328832596709265179083)
      ·
        refine ⟨122509993248895063897768625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81673328832596709265179083 122509993248895063897768625)
        ·
          refine ⟨91882494936671297923326469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122509993248895063897768625 91882494936671297923326469)
          ·
            refine ⟨17227967800625868360623713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91882494936671297923326469 17227967800625868360623713)
            ·
              refine ⟨12920975850469401270467785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17227967800625868360623713 12920975850469401270467785)
              ·
                refine ⟨9690731887852050952850839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12920975850469401270467785 9690731887852050952850839)
                ·
                  refine ⟨14536097831778076429276259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9690731887852050952850839 14536097831778076429276259)
                  ·
                    refine ⟨21804146747667114643914389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14536097831778076429276259 21804146747667114643914389)
                    ·
                      refine ⟨1022069378796895998933487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21804146747667114643914389 1022069378796895998933487)
                      ·
                        rfl

theorem cell23_1990473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_1990473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990473 prefixEnd_1990473 := by exact prefixLift 1990473
  have htrace : WordTrace (prefixWord ++ tailWord_1990473) baseStart_1990473 baseEnd_1990473 := by
    simpa [prefixWord, tailWord_1990473, baseEnd_1990473] using wordTrace_append hprefix tailTrace_1990473
  have hstable : (prefixWord ++ tailWord_1990473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990473).length < 2 ^ (prefixWord ++ tailWord_1990473).sum := by decide
  have hdescent : baseEnd_1990473 < baseStart_1990473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990487 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 1, 6]
def baseStart_1990487 : Nat := 118140960795 + 1990487 * 2 ^ 59
def prefixEnd_1990487 : Nat := 4983230072969 + 3 ^ 40 * 1990487 * 2
def baseEnd_1990487 : Nat := 340692189175352981386141

theorem tailTrace_1990487 : CollatzResearch.WordTrace tailWord_1990487 prefixEnd_1990487 340692189175352981386141 := by
  unfold tailWord_1990487
  simp only [CollatzResearch.WordTrace]
  refine ⟨72599025139813021960057715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48399350093208681306705143 72599025139813021960057715)
  ·
    refine ⟨108898537709719532940086573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72599025139813021960057715 108898537709719532940086573)
    ·
      refine ⟨40836951641144824852532465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108898537709719532940086573 40836951641144824852532465)
      ·
        refine ⟨30627713730858618639399349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40836951641144824852532465 30627713730858618639399349)
        ·
          refine ⟨2871348162267995497443689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30627713730858618639399349 2871348162267995497443689)
          ·
            refine ⟨2153511121700996623082767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2871348162267995497443689 2153511121700996623082767)
            ·
              refine ⟨3230266682551494934624151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153511121700996623082767 3230266682551494934624151)
              ·
                refine ⟨4845400023827242401936227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230266682551494934624151 4845400023827242401936227)
                ·
                  refine ⟨7268100035740863602904341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845400023827242401936227 7268100035740863602904341)
                  ·
                    refine ⟨340692189175352981386141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7268100035740863602904341 340692189175352981386141)
                    ·
                      rfl

theorem cell23_1990487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_1990487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990487 prefixEnd_1990487 := by exact prefixLift 1990487
  have htrace : WordTrace (prefixWord ++ tailWord_1990487) baseStart_1990487 baseEnd_1990487 := by
    simpa [prefixWord, tailWord_1990487, baseEnd_1990487] using wordTrace_append hprefix tailTrace_1990487
  have hstable : (prefixWord ++ tailWord_1990487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990487).length < 2 ^ (prefixWord ++ tailWord_1990487).sum := by decide
  have hdescent : baseEnd_1990487 < baseStart_1990487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990497 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_1990497 : Nat := 118140960795 + 1990497 * 2 ^ 59
def prefixEnd_1990497 : Nat := 4983230072969 + 3 ^ 40 * 1990497 * 2
def baseEnd_1990497 : Nat := 1022081702332603905033377

theorem tailTrace_1990497 : CollatzResearch.WordTrace tailWord_1990497 prefixEnd_1990497 1022081702332603905033377 := by
  unfold tailWord_1990497
  simp only [CollatzResearch.WordTrace]
  refine ⟨72599389869776793667921745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48399593246517862445281163 72599389869776793667921745)
  ·
    refine ⟨54449542402332595250941309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72599389869776793667921745 54449542402332595250941309)
    ·
      refine ⟨20418578400874723219102991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54449542402332595250941309 20418578400874723219102991)
      ·
        refine ⟨30627867601312084828654487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20418578400874723219102991 30627867601312084828654487)
        ·
          refine ⟨45941801401968127242981731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30627867601312084828654487 45941801401968127242981731)
          ·
            refine ⟨68912702102952190864472597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45941801401968127242981731 68912702102952190864472597)
            ·
              refine ⟨3230282911075883946772153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68912702102952190864472597 3230282911075883946772153)
              ·
                refine ⟨2422712183306912960079115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230282911075883946772153 2422712183306912960079115)
                ·
                  refine ⟨3634068274960369440118673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422712183306912960079115 3634068274960369440118673)
                  ·
                    refine ⟨2725551206220277080089005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3634068274960369440118673 2725551206220277080089005)
                    ·
                      refine ⟨1022081702332603905033377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2725551206220277080089005 1022081702332603905033377)
                      ·
                        rfl

theorem cell23_1990497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_1990497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990497 prefixEnd_1990497 := by exact prefixLift 1990497
  have htrace : WordTrace (prefixWord ++ tailWord_1990497) baseStart_1990497 baseEnd_1990497 := by
    simpa [prefixWord, tailWord_1990497, baseEnd_1990497] using wordTrace_append hprefix tailTrace_1990497
  have hstable : (prefixWord ++ tailWord_1990497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990497).length < 2 ^ (prefixWord ++ tailWord_1990497).sum := by decide
  have hdescent : baseEnd_1990497 < baseStart_1990497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990500 : List Nat := [2, 3, 1, 1, 5, 1, 1, 9]
def baseStart_1990500 : Nat := 118140960795 + 1990500 * 2 ^ 59
def prefixEnd_1990500 : Nat := 4983230072969 + 3 ^ 40 * 1990500 * 2
def baseEnd_1990500 : Nat := 37854934917576570122069

theorem tailTrace_1990500 : CollatzResearch.WordTrace tailWord_1990500 prefixEnd_1990500 37854934917576570122069 := by
  unfold tailWord_1990500
  simp only [CollatzResearch.WordTrace]
  refine ⟨36299749644382962590140477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48399666192510616786853969 36299749644382962590140477)
  ·
    refine ⟨13612406116643610971302679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36299749644382962590140477 13612406116643610971302679)
    ·
      refine ⟨20418609174965416456954019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13612406116643610971302679 20418609174965416456954019)
      ·
        refine ⟨30627913762448124685431029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20418609174965416456954019 30627913762448124685431029)
        ·
          refine ⟨2871366915229511689259159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30627913762448124685431029 2871366915229511689259159)
          ·
            refine ⟨4307050372844267533888739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871366915229511689259159 4307050372844267533888739)
            ·
              refine ⟨6460575559266401300833109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307050372844267533888739 6460575559266401300833109)
              ·
                refine ⟨37854934917576570122069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6460575559266401300833109 37854934917576570122069)
                ·
                  rfl

theorem cell23_1990500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 9].length) (baseStart_1990500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990500 prefixEnd_1990500 := by exact prefixLift 1990500
  have htrace : WordTrace (prefixWord ++ tailWord_1990500) baseStart_1990500 baseEnd_1990500 := by
    simpa [prefixWord, tailWord_1990500, baseEnd_1990500] using wordTrace_append hprefix tailTrace_1990500
  have hstable : (prefixWord ++ tailWord_1990500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990500).length < 2 ^ (prefixWord ++ tailWord_1990500).sum := by decide
  have hdescent : baseEnd_1990500 < baseStart_1990500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990520 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 1, 9, 2]
def baseStart_1990520 : Nat := 118140960795 + 1990520 * 2 ^ 59
def prefixEnd_1990520 : Nat := 4983230072969 + 3 ^ 40 * 1990520 * 2
def baseEnd_1990520 : Nat := 1022093512387657315045771

theorem tailTrace_1990520 : CollatzResearch.WordTrace tailWord_1990520 prefixEnd_1990520 1022093512387657315045771 := by
  unfold tailWord_1990520
  simp only [CollatzResearch.WordTrace]
  refine ⟨36300114374346734298004507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48400152499128979064006009 36300114374346734298004507)
  ·
    refine ⟨54450171561520101447006761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36300114374346734298004507 54450171561520101447006761)
    ·
      refine ⟨40837628671140076085255071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54450171561520101447006761 40837628671140076085255071)
      ·
        refine ⟨61256443006710114127882607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40837628671140076085255071 61256443006710114127882607)
        ·
          refine ⟨91884664510065171191823911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61256443006710114127882607 91884664510065171191823911)
          ·
            refine ⟨137826996765097756787735867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91884664510065171191823911 137826996765097756787735867)
            ·
              refine ⟨206740495147646635181603801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137826996765097756787735867 206740495147646635181603801)
              ·
                refine ⟨155055371360734976386202851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206740495147646635181603801 155055371360734976386202851)
                ·
                  refine ⟨232583057041102464579304277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155055371360734976386202851 232583057041102464579304277)
                  ·
                    refine ⟨1362791349850209753394361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 232583057041102464579304277 1362791349850209753394361)
                    ·
                      refine ⟨1022093512387657315045771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1362791349850209753394361 1022093512387657315045771)
                      ·
                        rfl

theorem cell23_1990520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 9, 2].length) (baseStart_1990520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990520 prefixEnd_1990520 := by exact prefixLift 1990520
  have htrace : WordTrace (prefixWord ++ tailWord_1990520) baseStart_1990520 baseEnd_1990520 := by
    simpa [prefixWord, tailWord_1990520, baseEnd_1990520] using wordTrace_append hprefix tailTrace_1990520
  have hstable : (prefixWord ++ tailWord_1990520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990520).length < 2 ^ (prefixWord ++ tailWord_1990520).sum := by decide
  have hdescent : baseEnd_1990520 < baseStart_1990520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990523 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 5]
def baseStart_1990523 : Nat := 118140960795 + 1990523 * 2 ^ 59
def prefixEnd_1990523 : Nat := 4983230072969 + 3 ^ 40 * 1990523 * 2
def baseEnd_1990523 : Nat := 1022095052829620803308257

theorem tailTrace_1990523 : CollatzResearch.WordTrace tailWord_1990523 prefixEnd_1990523 1022095052829620803308257 := by
  unfold tailWord_1990523
  simp only [CollatzResearch.WordTrace]
  refine ⟨72600338167682600108368223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48400225445121733405578815 72600338167682600108368223)
  ·
    refine ⟨108900507251523900162552335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72600338167682600108368223 108900507251523900162552335)
    ·
      refine ⟨163350760877285850243828503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108900507251523900162552335 163350760877285850243828503)
      ·
        refine ⟨245026141315928775365742755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163350760877285850243828503 245026141315928775365742755)
        ·
          refine ⟨367539211973893163048614133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245026141315928775365742755 367539211973893163048614133)
          ·
            refine ⟨34456801122552484035807575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 367539211973893163048614133 34456801122552484035807575)
            ·
              refine ⟨51685201683828726053711363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34456801122552484035807575 51685201683828726053711363)
              ·
                refine ⟨77527802525743089080567045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51685201683828726053711363 77527802525743089080567045)
                ·
                  refine ⟨14536462973576829202606321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77527802525743089080567045 14536462973576829202606321)
                  ·
                    refine ⟨10902347230182621901954741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14536462973576829202606321 10902347230182621901954741)
                    ·
                      refine ⟨1022095052829620803308257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10902347230182621901954741 1022095052829620803308257)
                      ·
                        rfl

theorem cell23_1990523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_1990523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990523 prefixEnd_1990523 := by exact prefixLift 1990523
  have htrace : WordTrace (prefixWord ++ tailWord_1990523) baseStart_1990523 baseEnd_1990523 := by
    simpa [prefixWord, tailWord_1990523, baseEnd_1990523] using wordTrace_append hprefix tailTrace_1990523
  have hstable : (prefixWord ++ tailWord_1990523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990523).length < 2 ^ (prefixWord ++ tailWord_1990523).sum := by decide
  have hdescent : baseEnd_1990523 < baseStart_1990523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990527 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 2, 1, 3]
def baseStart_1990527 : Nat := 118140960795 + 1990527 * 2 ^ 59
def prefixEnd_1990527 : Nat := 4983230072969 + 3 ^ 40 * 1990527 * 2
def baseEnd_1990527 : Nat := 1022097106752238787658239

theorem tailTrace_1990527 : CollatzResearch.WordTrace tailWord_1990527 prefixEnd_1990527 1022097106752238787658239 := by
  unfold tailWord_1990527
  simp only [CollatzResearch.WordTrace]
  refine ⟨72600484059668108791513835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48400322706445405861009223 72600484059668108791513835)
  ·
    refine ⟨108900726089502163187270753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72600484059668108791513835 108900726089502163187270753)
    ·
      refine ⟨81675544567126622390453065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108900726089502163187270753 81675544567126622390453065)
      ·
        refine ⟨61256658425344966792839799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81675544567126622390453065 61256658425344966792839799)
        ·
          refine ⟨91884987638017450189259699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61256658425344966792839799 91884987638017450189259699)
          ·
            refine ⟨137827481457026175283889549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91884987638017450189259699 137827481457026175283889549)
            ·
              refine ⟨51685305546384815731458581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137827481457026175283889549 51685305546384815731458581)
              ·
                refine ⟨2422748697486788237412121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51685305546384815731458581 2422748697486788237412121)
                ·
                  refine ⟨1817061523115091178059091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2422748697486788237412121 1817061523115091178059091)
                  ·
                    refine ⟨2725592284672636767088637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1817061523115091178059091 2725592284672636767088637)
                    ·
                      refine ⟨1022097106752238787658239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2725592284672636767088637 1022097106752238787658239)
                      ·
                        rfl

theorem cell23_1990527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_1990527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990527 prefixEnd_1990527 := by exact prefixLift 1990527
  have htrace : WordTrace (prefixWord ++ tailWord_1990527) baseStart_1990527 baseEnd_1990527 := by
    simpa [prefixWord, tailWord_1990527, baseEnd_1990527] using wordTrace_append hprefix tailTrace_1990527
  have hstable : (prefixWord ++ tailWord_1990527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990527).length < 2 ^ (prefixWord ++ tailWord_1990527).sum := by decide
  have hdescent : baseEnd_1990527 < baseStart_1990527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990537 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 3, 3, 2]
def baseStart_1990537 : Nat := 118140960795 + 1990537 * 2 ^ 59
def prefixEnd_1990537 : Nat := 4983230072969 + 3 ^ 40 * 1990537 * 2
def baseEnd_1990537 : Nat := 1022102241558783748533193

theorem tailTrace_1990537 : CollatzResearch.WordTrace tailWord_1990537 prefixEnd_1990537 1022102241558783748533193 := by
  unfold tailWord_1990537
  simp only [CollatzResearch.WordTrace]
  refine ⟨72600848789631880499377865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48400565859754586999585243 72600848789631880499377865)
  ·
    refine ⟨54450636592223910374533399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72600848789631880499377865 54450636592223910374533399)
    ·
      refine ⟨81675954888335865561800099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54450636592223910374533399 81675954888335865561800099)
      ·
        refine ⟨122513932332503798342700149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81675954888335865561800099 122513932332503798342700149)
        ·
          refine ⟨11485681156172231094628139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122513932332503798342700149 11485681156172231094628139)
          ·
            refine ⟨17228521734258346641942209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11485681156172231094628139 17228521734258346641942209)
            ·
              refine ⟨12921391300693759981456657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17228521734258346641942209 12921391300693759981456657)
              ·
                refine ⟨9691043475520319986092493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12921391300693759981456657 9691043475520319986092493)
                ·
                  refine ⟨3634141303320119994784685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9691043475520319986092493 3634141303320119994784685)
                  ·
                    refine ⟨1362802988745044998044257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3634141303320119994784685 1362802988745044998044257)
                    ·
                      refine ⟨1022102241558783748533193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1362802988745044998044257 1022102241558783748533193)
                      ·
                        rfl

theorem cell23_1990537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 3, 2].length) (baseStart_1990537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990537 prefixEnd_1990537 := by exact prefixLift 1990537
  have htrace : WordTrace (prefixWord ++ tailWord_1990537) baseStart_1990537 baseEnd_1990537 := by
    simpa [prefixWord, tailWord_1990537, baseEnd_1990537] using wordTrace_append hprefix tailTrace_1990537
  have hstable : (prefixWord ++ tailWord_1990537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990537).length < 2 ^ (prefixWord ++ tailWord_1990537).sum := by decide
  have hdescent : baseEnd_1990537 < baseStart_1990537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990538 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 2, 4]
def baseStart_1990538 : Nat := 118140960795 + 1990538 * 2 ^ 59
def prefixEnd_1990538 : Nat := 4983230072969 + 3 ^ 40 * 1990538 * 2
def baseEnd_1990538 : Nat := 340700918346479414873563

theorem tailTrace_1990538 : CollatzResearch.WordTrace tailWord_1990538 prefixEnd_1990538 340700918346479414873563 := by
  unfold tailWord_1990538
  simp only [CollatzResearch.WordTrace]
  refine ⟨18150221315657064417541067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48400590175085505113442845 18150221315657064417541067)
  ·
    refine ⟨27225331973485596626311601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18150221315657064417541067 27225331973485596626311601)
    ·
      refine ⟨20418998980114197469733701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27225331973485596626311601 20418998980114197469733701)
      ·
        refine ⟨3828562308771412025575069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20418998980114197469733701 3828562308771412025575069)
        ·
          refine ⟨1435710865789279509590651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3828562308771412025575069 1435710865789279509590651)
          ·
            refine ⟨2153566298683919264385977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435710865789279509590651 2153566298683919264385977)
            ·
              refine ⟨1615174724012939448289483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2153566298683919264385977 1615174724012939448289483)
              ·
                refine ⟨2422762086019409172434225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615174724012939448289483 2422762086019409172434225)
                ·
                  refine ⟨1817071564514556879325669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2422762086019409172434225 1817071564514556879325669)
                  ·
                    refine ⟨340700918346479414873563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1817071564514556879325669 340700918346479414873563)
                    ·
                      rfl

theorem cell23_1990538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_1990538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990538 prefixEnd_1990538 := by exact prefixLift 1990538
  have htrace : WordTrace (prefixWord ++ tailWord_1990538) baseStart_1990538 baseEnd_1990538 := by
    simpa [prefixWord, tailWord_1990538, baseEnd_1990538] using wordTrace_append hprefix tailTrace_1990538
  have hstable : (prefixWord ++ tailWord_1990538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990538).length < 2 ^ (prefixWord ++ tailWord_1990538).sum := by decide
  have hdescent : baseEnd_1990538 < baseStart_1990538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990543 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 8, 6]
def baseStart_1990543 : Nat := 118140960795 + 1990543 * 2 ^ 59
def prefixEnd_1990543 : Nat := 4983230072969 + 3 ^ 40 * 1990543 * 2
def baseEnd_1990543 : Nat := 340701774147570241686055

theorem tailTrace_1990543 : CollatzResearch.WordTrace tailWord_1990543 prefixEnd_1990543 340701774147570241686055 := by
  unfold tailWord_1990543
  simp only [CollatzResearch.WordTrace]
  refine ⟨72601067627610143524096283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48400711751740095682730855 72601067627610143524096283)
  ·
    refine ⟨108901601441415215286144425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72601067627610143524096283 108901601441415215286144425)
    ·
      refine ⟨81676201081061411464608319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108901601441415215286144425 81676201081061411464608319)
      ·
        refine ⟨122514301621592117196912479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81676201081061411464608319 122514301621592117196912479)
        ·
          refine ⟨183771452432388175795368719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122514301621592117196912479 183771452432388175795368719)
          ·
            refine ⟨275657178648582263693053079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183771452432388175795368719 275657178648582263693053079)
            ·
              refine ⟨413485767972873395539579619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275657178648582263693053079 413485767972873395539579619)
              ·
                refine ⟨620228651959310093309369429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413485767972873395539579619 620228651959310093309369429)
                ·
                  refine ⟨7268304515148165155969173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 620228651959310093309369429 7268304515148165155969173)
                  ·
                    refine ⟨340701774147570241686055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7268304515148165155969173 340701774147570241686055)
                    ·
                      rfl

theorem cell23_1990543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_1990543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990543 prefixEnd_1990543 := by exact prefixLift 1990543
  have htrace : WordTrace (prefixWord ++ tailWord_1990543) baseStart_1990543 baseEnd_1990543 := by
    simpa [prefixWord, tailWord_1990543, baseEnd_1990543] using wordTrace_append hprefix tailTrace_1990543
  have hstable : (prefixWord ++ tailWord_1990543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990543).length < 2 ^ (prefixWord ++ tailWord_1990543).sum := by decide
  have hdescent : baseEnd_1990543 < baseStart_1990543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990554 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2]
def baseStart_1990554 : Nat := 118140960795 + 1990554 * 2 ^ 59
def prefixEnd_1990554 : Nat := 4983230072969 + 3 ^ 40 * 1990554 * 2
def baseEnd_1990554 : Nat := 1022110970729910182020615

theorem tailTrace_1990554 : CollatzResearch.WordTrace tailWord_1990554 prefixEnd_1990554 1022110970729910182020615 := by
  unfold tailWord_1990554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18150367207642573100686679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48400979220380194935164477 18150367207642573100686679)
  ·
    refine ⟨27225550811463859651030019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18150367207642573100686679 27225550811463859651030019)
    ·
      refine ⟨40838326217195789476545029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27225550811463859651030019 40838326217195789476545029)
      ·
        refine ⟨7657186165724210526852193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40838326217195789476545029 7657186165724210526852193)
        ·
          refine ⟨5742889624293157895139145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7657186165724210526852193 5742889624293157895139145)
          ·
            refine ⟨4307167218219868421354359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5742889624293157895139145 4307167218219868421354359)
            ·
              refine ⟨6460750827329802632031539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307167218219868421354359 6460750827329802632031539)
              ·
                refine ⟨9691126240994703948047309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460750827329802632031539 9691126240994703948047309)
                ·
                  refine ⟨3634172340373013980517741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9691126240994703948047309 3634172340373013980517741)
                  ·
                    refine ⟨1362814627639880242694153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3634172340373013980517741 1362814627639880242694153)
                    ·
                      refine ⟨1022110970729910182020615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1362814627639880242694153 1022110970729910182020615)
                      ·
                        rfl

theorem cell23_1990554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_1990554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990554 prefixEnd_1990554 := by exact prefixLift 1990554
  have htrace : WordTrace (prefixWord ++ tailWord_1990554) baseStart_1990554 baseEnd_1990554 := by
    simpa [prefixWord, tailWord_1990554, baseEnd_1990554] using wordTrace_append hprefix tailTrace_1990554
  have hstable : (prefixWord ++ tailWord_1990554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990554).length < 2 ^ (prefixWord ++ tailWord_1990554).sum := by decide
  have hdescent : baseEnd_1990554 < baseStart_1990554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990667 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 3, 4]
def baseStart_1990667 : Nat := 118140960795 + 1990667 * 2 ^ 59
def prefixEnd_1990667 : Nat := 4983230072969 + 3 ^ 40 * 1990667 * 2
def baseEnd_1990667 : Nat := 340722998014622746635865

theorem tailTrace_1990667 : CollatzResearch.WordTrace tailWord_1990667 prefixEnd_1990667 340722998014622746635865 := by
  unfold tailWord_1990667
  simp only [CollatzResearch.WordTrace]
  refine ⟨72605590279160912701610255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48403726852773941801073503 72605590279160912701610255)
  ·
    refine ⟨108908385418741369052415383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72605590279160912701610255 108908385418741369052415383)
    ·
      refine ⟨163362578128112053578623075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108908385418741369052415383 163362578128112053578623075)
      ·
        refine ⟨245043867192168080367934613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163362578128112053578623075 245043867192168080367934613)
        ·
          refine ⟨11486431274632878767246935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 245043867192168080367934613 11486431274632878767246935)
          ·
            refine ⟨17229646911949318150870403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11486431274632878767246935 17229646911949318150870403)
            ·
              refine ⟨25844470367923977226305605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17229646911949318150870403 25844470367923977226305605)
              ·
                refine ⟨4845838193985745729932301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25844470367923977226305605 4845838193985745729932301)
                ·
                  refine ⟨1817189322744654648724613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4845838193985745729932301 1817189322744654648724613)
                  ·
                    refine ⟨340722998014622746635865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1817189322744654648724613 340722998014622746635865)
                    ·
                      rfl

theorem cell23_1990667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 4].length) (baseStart_1990667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990667 prefixEnd_1990667 := by exact prefixLift 1990667
  have htrace : WordTrace (prefixWord ++ tailWord_1990667) baseStart_1990667 baseEnd_1990667 := by
    simpa [prefixWord, tailWord_1990667, baseEnd_1990667] using wordTrace_append hprefix tailTrace_1990667
  have hstable : (prefixWord ++ tailWord_1990667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990667).length < 2 ^ (prefixWord ++ tailWord_1990667).sum := by decide
  have hdescent : baseEnd_1990667 < baseStart_1990667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990680 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 10]
def baseStart_1990680 : Nat := 118140960795 + 1990680 * 2 ^ 59
def prefixEnd_1990680 : Nat := 4983230072969 + 3 ^ 40 * 1990680 * 2
def baseEnd_1990680 : Nat := 113575074365819632116115

theorem tailTrace_1990680 : CollatzResearch.WordTrace tailWord_1990680 prefixEnd_1990680 113575074365819632116115 := by
  unfold tailWord_1990680
  simp only [CollatzResearch.WordTrace]
  refine ⟨36303032214056907960916747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48404042952075877281222329 36303032214056907960916747)
  ·
    refine ⟨54454548321085361941375121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36303032214056907960916747 54454548321085361941375121)
    ·
      refine ⟨40840911240814021456031341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54454548321085361941375121 40840911240814021456031341)
      ·
        refine ⟨15315341715305258046011753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40840911240814021456031341 15315341715305258046011753)
        ·
          refine ⟨11486506286478943534508815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15315341715305258046011753 11486506286478943534508815)
          ·
            refine ⟨17229759429718415301763223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11486506286478943534508815 17229759429718415301763223)
            ·
              refine ⟨25844639144577622952644835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17229759429718415301763223 25844639144577622952644835)
              ·
                refine ⟨38766958716866434428967253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25844639144577622952644835 38766958716866434428967253)
                ·
                  refine ⟨113575074365819632116115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 38766958716866434428967253 113575074365819632116115)
                  ·
                    rfl

theorem cell23_1990680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 10].length) (baseStart_1990680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990680 prefixEnd_1990680 := by exact prefixLift 1990680
  have htrace : WordTrace (prefixWord ++ tailWord_1990680) baseStart_1990680 baseEnd_1990680 := by
    simpa [prefixWord, tailWord_1990680, baseEnd_1990680] using wordTrace_append hprefix tailTrace_1990680
  have hstable : (prefixWord ++ tailWord_1990680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990680).length < 2 ^ (prefixWord ++ tailWord_1990680).sum := by decide
  have hdescent : baseEnd_1990680 < baseStart_1990680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990700 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_1990700 : Nat := 118140960795 + 1990700 * 2 ^ 59
def prefixEnd_1990700 : Nat := 4983230072969 + 3 ^ 40 * 1990700 * 2
def baseEnd_1990700 : Nat := 1022185938905466610794943

theorem tailTrace_1990700 : CollatzResearch.WordTrace tailWord_1990700 prefixEnd_1990700 1022185938905466610794943 := by
  unfold tailWord_1990700
  simp only [CollatzResearch.WordTrace]
  refine ⟨36303396944020679668780777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48404529258694239558374369 36303396944020679668780777)
  ·
    refine ⟨27227547708015509751585583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36303396944020679668780777 27227547708015509751585583)
    ·
      refine ⟨40841321562023264627378375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27227547708015509751585583 40841321562023264627378375)
      ·
        refine ⟨61261982343034896941067563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40841321562023264627378375 61261982343034896941067563)
        ·
          refine ⟨91892973514552345411601345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61261982343034896941067563 91892973514552345411601345)
          ·
            refine ⟨68919730135914259058701009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91892973514552345411601345 68919730135914259058701009)
            ·
              refine ⟨51689797601935694294025757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68919730135914259058701009 51689797601935694294025757)
              ·
                refine ⟨19383674100725885360259659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51689797601935694294025757 19383674100725885360259659)
                ·
                  refine ⟨29075511151088828040389489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19383674100725885360259659 29075511151088828040389489)
                  ·
                    refine ⟨21806633363316621030292117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29075511151088828040389489 21806633363316621030292117)
                    ·
                      refine ⟨1022185938905466610794943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21806633363316621030292117 1022185938905466610794943)
                      ·
                        rfl

theorem cell23_1990700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_1990700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990700 prefixEnd_1990700 := by exact prefixLift 1990700
  have htrace : WordTrace (prefixWord ++ tailWord_1990700) baseStart_1990700 baseEnd_1990700 := by
    simpa [prefixWord, tailWord_1990700, baseEnd_1990700] using wordTrace_append hprefix tailTrace_1990700
  have hstable : (prefixWord ++ tailWord_1990700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990700).length < 2 ^ (prefixWord ++ tailWord_1990700).sum := by decide
  have hdescent : baseEnd_1990700 < baseStart_1990700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990727 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 3, 5]
def baseStart_1990727 : Nat := 118140960795 + 1990727 * 2 ^ 59
def prefixEnd_1990727 : Nat := 4983230072969 + 3 ^ 40 * 1990727 * 2
def baseEnd_1990727 : Nat := 340733267627712668385773

theorem tailTrace_1990727 : CollatzResearch.WordTrace tailWord_1990727 prefixEnd_1990727 340733267627712668385773 := by
  unfold tailWord_1990727
  simp only [CollatzResearch.WordTrace]
  refine ⟨72607778658943542948794435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48405185772629028632529623 72607778658943542948794435)
  ·
    refine ⟨108911667988415314423191653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72607778658943542948794435 108911667988415314423191653)
    ·
      refine ⟨20420937747827871454348435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108911667988415314423191653 20420937747827871454348435)
      ·
        refine ⟨30631406621741807181522653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20420937747827871454348435 30631406621741807181522653)
        ·
          refine ⟨11486777483153177693070995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30631406621741807181522653 11486777483153177693070995)
          ·
            refine ⟨17230166224729766539606493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11486777483153177693070995 17230166224729766539606493)
            ·
              refine ⟨6461312334273662452352435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17230166224729766539606493 6461312334273662452352435)
              ·
                refine ⟨9691968501410493678528653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6461312334273662452352435 9691968501410493678528653)
                ·
                  refine ⟨3634488188028935129448245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9691968501410493678528653 3634488188028935129448245)
                  ·
                    refine ⟨340733267627712668385773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3634488188028935129448245 340733267627712668385773)
                    ·
                      rfl

theorem cell23_1990727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_1990727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990727 prefixEnd_1990727 := by exact prefixLift 1990727
  have htrace : WordTrace (prefixWord ++ tailWord_1990727) baseStart_1990727 baseEnd_1990727 := by
    simpa [prefixWord, tailWord_1990727, baseEnd_1990727] using wordTrace_append hprefix tailTrace_1990727
  have hstable : (prefixWord ++ tailWord_1990727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990727).length < 2 ^ (prefixWord ++ tailWord_1990727).sum := by decide
  have hdescent : baseEnd_1990727 < baseStart_1990727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990774 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1990774 : Nat := 118140960795 + 1990774 * 2 ^ 59
def prefixEnd_1990774 : Nat := 4983230072969 + 3 ^ 40 * 1990774 * 2
def baseEnd_1990774 : Nat := 340741312157966440423201

theorem tailTrace_1990774 : CollatzResearch.WordTrace tailWord_1990774 prefixEnd_1990774 340741312157966440423201 := by
  unfold tailWord_1990774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4538093305610829373484711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48406328593182179983836917 4538093305610829373484711)
  ·
    refine ⟨6807139958416244060227067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4538093305610829373484711 6807139958416244060227067)
    ·
      refine ⟨10210709937624366090340601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6807139958416244060227067 10210709937624366090340601)
      ·
        refine ⟨7658032453218274567755451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10210709937624366090340601 7658032453218274567755451)
        ·
          refine ⟨11487048679827411851633177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658032453218274567755451 11487048679827411851633177)
          ·
            refine ⟨8615286509870558888724883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11487048679827411851633177 8615286509870558888724883)
            ·
              refine ⟨12922929764805838333087325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8615286509870558888724883 12922929764805838333087325)
              ·
                refine ⟨4846098661802189374907747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12922929764805838333087325 4846098661802189374907747)
                ·
                  refine ⟨7269147992703284062361621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846098661802189374907747 7269147992703284062361621)
                  ·
                    refine ⟨340741312157966440423201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7269147992703284062361621 340741312157966440423201)
                    ·
                      rfl

theorem cell23_1990774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1990774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990774 prefixEnd_1990774 := by exact prefixLift 1990774
  have htrace : WordTrace (prefixWord ++ tailWord_1990774) baseStart_1990774 baseEnd_1990774 := by
    simpa [prefixWord, tailWord_1990774, baseEnd_1990774] using wordTrace_append hprefix tailTrace_1990774
  have hstable : (prefixWord ++ tailWord_1990774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990774).length < 2 ^ (prefixWord ++ tailWord_1990774).sum := by decide
  have hdescent : baseEnd_1990774 < baseStart_1990774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990781 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 5, 2, 2]
def baseStart_1990781 : Nat := 118140960795 + 1990781 * 2 ^ 59
def prefixEnd_1990781 : Nat := 4983230072969 + 3 ^ 40 * 1990781 * 2
def baseEnd_1990781 : Nat := 1022227530838480793882071

theorem tailTrace_1990781 : CollatzResearch.WordTrace tailWord_1990781 prefixEnd_1990781 1022227530838480793882071 := by
  unfold tailWord_1990781
  simp only [CollatzResearch.WordTrace]
  refine ⟨72609748200747910171260197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48406498800498606780840131 72609748200747910171260197)
  ·
    refine ⟨13614327787640233157111287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72609748200747910171260197 13614327787640233157111287)
    ·
      refine ⟨20421491681460349735666931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13614327787640233157111287 20421491681460349735666931)
      ·
        refine ⟨30632237522190524603500397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20421491681460349735666931 30632237522190524603500397)
        ·
          refine ⟨11487089070821446726312649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30632237522190524603500397 11487089070821446726312649)
          ·
            refine ⟨8615316803116085044734487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11487089070821446726312649 8615316803116085044734487)
            ·
              refine ⟨12922975204674127567101731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8615316803116085044734487 12922975204674127567101731)
              ·
                refine ⟨19384462807011191350652597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12922975204674127567101731 19384462807011191350652597)
                ·
                  refine ⟨1817293388157299189123681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19384462807011191350652597 1817293388157299189123681)
                  ·
                    refine ⟨1362970041117974391842761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1817293388157299189123681 1362970041117974391842761)
                    ·
                      refine ⟨1022227530838480793882071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1362970041117974391842761 1022227530838480793882071)
                      ·
                        rfl

theorem cell23_1990781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_1990781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990781 prefixEnd_1990781 := by exact prefixLift 1990781
  have htrace : WordTrace (prefixWord ++ tailWord_1990781) baseStart_1990781 baseEnd_1990781 := by
    simpa [prefixWord, tailWord_1990781, baseEnd_1990781] using wordTrace_append hprefix tailTrace_1990781
  have hstable : (prefixWord ++ tailWord_1990781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990781).length < 2 ^ (prefixWord ++ tailWord_1990781).sum := by decide
  have hdescent : baseEnd_1990781 < baseStart_1990781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990784 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 3]
def baseStart_1990784 : Nat := 118140960795 + 1990784 * 2 ^ 59
def prefixEnd_1990784 : Nat := 4983230072969 + 3 ^ 40 * 1990784 * 2
def baseEnd_1990784 : Nat := 1022229071280444282144557

theorem tailTrace_1990784 : CollatzResearch.WordTrace tailWord_1990784 prefixEnd_1990784 1022229071280444282144557 := by
  unfold tailWord_1990784
  simp only [CollatzResearch.WordTrace]
  refine ⟨36304928809868520841809703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48406571746491361122412937 36304928809868520841809703)
  ·
    refine ⟨54457393214802781262714555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36304928809868520841809703 54457393214802781262714555)
    ·
      refine ⟨81686089822204171894071833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54457393214802781262714555 81686089822204171894071833)
      ·
        refine ⟨61264567366653128920553875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81686089822204171894071833 61264567366653128920553875)
        ·
          refine ⟨91896851049979693380830813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61264567366653128920553875 91896851049979693380830813)
          ·
            refine ⟨34461319143742385017811555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91896851049979693380830813 34461319143742385017811555)
            ·
              refine ⟨51691978715613577526717333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34461319143742385017811555 51691978715613577526717333)
              ·
                refine ⟨2423061502294386446564875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51691978715613577526717333 2423061502294386446564875)
                ·
                  refine ⟨3634592253441579669847313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423061502294386446564875 3634592253441579669847313)
                  ·
                    refine ⟨2725944190081184752385485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3634592253441579669847313 2725944190081184752385485)
                    ·
                      refine ⟨1022229071280444282144557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2725944190081184752385485 1022229071280444282144557)
                      ·
                        rfl

theorem cell23_1990784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_1990784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990784 prefixEnd_1990784 := by exact prefixLift 1990784
  have htrace : WordTrace (prefixWord ++ tailWord_1990784) baseStart_1990784 baseEnd_1990784 := by
    simpa [prefixWord, tailWord_1990784, baseEnd_1990784] using wordTrace_append hprefix tailTrace_1990784
  have hstable : (prefixWord ++ tailWord_1990784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990784).length < 2 ^ (prefixWord ++ tailWord_1990784).sum := by decide
  have hdescent : baseEnd_1990784 < baseStart_1990784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990785 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_1990785 : Nat := 118140960795 + 1990785 * 2 ^ 59
def prefixEnd_1990785 : Nat := 4983230072969 + 3 ^ 40 * 1990785 * 2
def baseEnd_1990785 : Nat := 1022229584761098778232053

theorem tailTrace_1990785 : CollatzResearch.WordTrace tailWord_1990785 prefixEnd_1990785 1022229584761098778232053 := by
  unfold tailWord_1990785
  simp only [CollatzResearch.WordTrace]
  refine ⟨72609894092733418854405809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48406596061822279236270539 72609894092733418854405809)
  ·
    refine ⟨54457420569550064140804357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72609894092733418854405809 54457420569550064140804357)
    ·
      refine ⟨10210766356790637026400817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54457420569550064140804357 10210766356790637026400817)
      ·
        refine ⟨7658074767592977769800613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10210766356790637026400817 7658074767592977769800613)
        ·
          refine ⟨1435889018923683331837615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7658074767592977769800613 1435889018923683331837615)
          ·
            refine ⟨2153833528385524997756423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435889018923683331837615 2153833528385524997756423)
            ·
              refine ⟨3230750292578287496634635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153833528385524997756423 3230750292578287496634635)
              ·
                refine ⟨4846125438867431244951953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230750292578287496634635 4846125438867431244951953)
                ·
                  refine ⟨3634594079150573433713965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4846125438867431244951953 3634594079150573433713965)
                  ·
                    refine ⟨1362972779681465037642737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3634594079150573433713965 1362972779681465037642737)
                    ·
                      refine ⟨1022229584761098778232053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1362972779681465037642737 1022229584761098778232053)
                      ·
                        rfl

theorem cell23_1990785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_1990785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990785 prefixEnd_1990785 := by exact prefixLift 1990785
  have htrace : WordTrace (prefixWord ++ tailWord_1990785) baseStart_1990785 baseEnd_1990785 := by
    simpa [prefixWord, tailWord_1990785, baseEnd_1990785] using wordTrace_append hprefix tailTrace_1990785
  have hstable : (prefixWord ++ tailWord_1990785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990785).length < 2 ^ (prefixWord ++ tailWord_1990785).sum := by decide
  have hdescent : baseEnd_1990785 < baseStart_1990785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990794 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1990794 : Nat := 118140960795 + 1990794 * 2 ^ 59
def prefixEnd_1990794 : Nat := 4983230072969 + 3 ^ 40 * 1990794 * 2
def baseEnd_1990794 : Nat := 1022234206086989243019511

theorem tailTrace_1990794 : CollatzResearch.WordTrace tailWord_1990794 prefixEnd_1990794 1022234206086989243019511 := by
  unfold tailWord_1990794
  simp only [CollatzResearch.WordTrace]
  refine ⟨18152555587425203347870859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48406814899800542260988957 18152555587425203347870859)
  ·
    refine ⟨27228833381137805021806289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18152555587425203347870859 27228833381137805021806289)
    ·
      refine ⟨20421625035853353766354717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27228833381137805021806289 20421625035853353766354717)
      ·
        refine ⟨7658109388445007662383019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20421625035853353766354717 7658109388445007662383019)
        ·
          refine ⟨11487164082667511493574529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658109388445007662383019 11487164082667511493574529)
          ·
            refine ⟨8615373062000633620180897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11487164082667511493574529 8615373062000633620180897)
            ·
              refine ⟨6461529796500475215135673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8615373062000633620180897 6461529796500475215135673)
              ·
                refine ⟨4846147347375356411351755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6461529796500475215135673 4846147347375356411351755)
                ·
                  refine ⟨7269221021063034617027633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846147347375356411351755 7269221021063034617027633)
                  ·
                    refine ⟨5451915765797275962770725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7269221021063034617027633 5451915765797275962770725)
                    ·
                      refine ⟨1022234206086989243019511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5451915765797275962770725 1022234206086989243019511)
                      ·
                        rfl

theorem cell23_1990794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1990794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990794 prefixEnd_1990794 := by exact prefixLift 1990794
  have htrace : WordTrace (prefixWord ++ tailWord_1990794) baseStart_1990794 baseEnd_1990794 := by
    simpa [prefixWord, tailWord_1990794, baseEnd_1990794] using wordTrace_append hprefix tailTrace_1990794
  have hstable : (prefixWord ++ tailWord_1990794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990794).length < 2 ^ (prefixWord ++ tailWord_1990794).sum := by decide
  have hdescent : baseEnd_1990794 < baseStart_1990794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990808 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 2, 4]
def baseStart_1990808 : Nat := 118140960795 + 1990808 * 2 ^ 59
def prefixEnd_1990808 : Nat := 4983230072969 + 3 ^ 40 * 1990808 * 2
def baseEnd_1990808 : Nat := 340747131605384062748149

theorem tailTrace_1990808 : CollatzResearch.WordTrace tailWord_1990808 prefixEnd_1990808 340747131605384062748149 := by
  unfold tailWord_1990808
  simp only [CollatzResearch.WordTrace]
  refine ⟨36305366485825046891246539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48407155314433395854995385 36305366485825046891246539)
  ·
    refine ⟨54458049728737570336869809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36305366485825046891246539 54458049728737570336869809)
    ·
      refine ⟨40843537296553177752652357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54458049728737570336869809 40843537296553177752652357)
      ·
        refine ⟨7658163243103720828622317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40843537296553177752652357 7658163243103720828622317)
        ·
          refine ⟨2871811216163895310733369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7658163243103720828622317 2871811216163895310733369)
          ·
            refine ⟨2153858412122921483050027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2871811216163895310733369 2153858412122921483050027)
            ·
              refine ⟨3230787618184382224575041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153858412122921483050027 3230787618184382224575041)
              ·
                refine ⟨2423090713638286668431281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230787618184382224575041 2423090713638286668431281)
                ·
                  refine ⟨1817318035228715001323461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2423090713638286668431281 1817318035228715001323461)
                  ·
                    refine ⟨340747131605384062748149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1817318035228715001323461 340747131605384062748149)
                    ·
                      rfl

theorem cell23_1990808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_1990808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990808 prefixEnd_1990808 := by exact prefixLift 1990808
  have htrace : WordTrace (prefixWord ++ tailWord_1990808) baseStart_1990808 baseEnd_1990808 := by
    simpa [prefixWord, tailWord_1990808, baseEnd_1990808] using wordTrace_append hprefix tailTrace_1990808
  have hstable : (prefixWord ++ tailWord_1990808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990808).length < 2 ^ (prefixWord ++ tailWord_1990808).sum := by decide
  have hdescent : baseEnd_1990808 < baseStart_1990808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990815 : List Nat := [1, 1, 2, 6, 1, 1, 2, 4, 1, 2, 2]
def baseStart_1990815 : Nat := 118140960795 + 1990815 * 2 ^ 59
def prefixEnd_1990815 : Nat := 4983230072969 + 3 ^ 40 * 1990815 * 2
def baseEnd_1990815 : Nat := 1022244989180733660856915

theorem tailTrace_1990815 : CollatzResearch.WordTrace tailWord_1990815 prefixEnd_1990815 1022244989180733660856915 := by
  unfold tailWord_1990815
  simp only [CollatzResearch.WordTrace]
  refine ⟨72610988282624733977997899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48407325521749822651998599 72610988282624733977997899)
  ·
    refine ⟨108916482423937100966996849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72610988282624733977997899 108916482423937100966996849)
    ·
      refine ⟨81687361817952825725247637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108916482423937100966996849 81687361817952825725247637)
      ·
        refine ⟨3829095085216538705870983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81687361817952825725247637 3829095085216538705870983)
        ·
          refine ⟨5743642627824808058806475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3829095085216538705870983 5743642627824808058806475)
          ·
            refine ⟨8615463941737212088209713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743642627824808058806475 8615463941737212088209713)
            ·
              refine ⟨6461597956302909066157285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8615463941737212088209713 6461597956302909066157285)
              ·
                refine ⟨1211549616806795449904491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6461597956302909066157285 1211549616806795449904491)
                ·
                  refine ⟨1817324425210193174856737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211549616806795449904491 1817324425210193174856737)
                  ·
                    refine ⟨1362993318907644881142553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1817324425210193174856737 1362993318907644881142553)
                    ·
                      refine ⟨1022244989180733660856915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1362993318907644881142553 1022244989180733660856915)
                      ·
                        rfl

theorem cell23_1990815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_1990815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990815 prefixEnd_1990815 := by exact prefixLift 1990815
  have htrace : WordTrace (prefixWord ++ tailWord_1990815) baseStart_1990815 baseEnd_1990815 := by
    simpa [prefixWord, tailWord_1990815, baseEnd_1990815] using wordTrace_append hprefix tailTrace_1990815
  have hstable : (prefixWord ++ tailWord_1990815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990815).length < 2 ^ (prefixWord ++ tailWord_1990815).sum := by decide
  have hdescent : baseEnd_1990815 < baseStart_1990815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990849 : List Nat := [1, 2, 6, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_1990849 : Nat := 118140960795 + 1990849 * 2 ^ 59
def prefixEnd_1990849 : Nat := 4983230072969 + 3 ^ 40 * 1990849 * 2
def baseEnd_1990849 : Nat := 1022262447522986527831759

theorem tailTrace_1990849 : CollatzResearch.WordTrace tailWord_1990849 prefixEnd_1990849 1022262447522986527831759 := by
  unfold tailWord_1990849
  simp only [CollatzResearch.WordTrace]
  refine ⟨72612228364501557784735601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48408152243001038523157067 72612228364501557784735601)
  ·
    refine ⟨54459171273376168338551701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72612228364501557784735601 54459171273376168338551701)
    ·
      refine ⟨2552773653439507890869611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54459171273376168338551701 2552773653439507890869611)
      ·
        refine ⟨3829160480159261836304417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2552773653439507890869611 3829160480159261836304417)
        ·
          refine ⟨2871870360119446377228313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3829160480159261836304417 2871870360119446377228313)
          ·
            refine ⟨2153902770089584782921235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2871870360119446377228313 2153902770089584782921235)
            ·
              refine ⟨3230854155134377174381853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153902770089584782921235 3230854155134377174381853)
              ·
                refine ⟨1211570308175391440393195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3230854155134377174381853 1211570308175391440393195)
                ·
                  refine ⟨1817355462263087160589793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211570308175391440393195 1817355462263087160589793)
                  ·
                    refine ⟨1363016596697315370442345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1817355462263087160589793 1363016596697315370442345)
                    ·
                      refine ⟨1022262447522986527831759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1363016596697315370442345 1022262447522986527831759)
                      ·
                        rfl

theorem cell23_1990849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_1990849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990849 prefixEnd_1990849 := by exact prefixLift 1990849
  have htrace : WordTrace (prefixWord ++ tailWord_1990849) baseStart_1990849 baseEnd_1990849 := by
    simpa [prefixWord, tailWord_1990849, baseEnd_1990849] using wordTrace_append hprefix tailTrace_1990849
  have hstable : (prefixWord ++ tailWord_1990849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990849).length < 2 ^ (prefixWord ++ tailWord_1990849).sum := by decide
  have hdescent : baseEnd_1990849 < baseStart_1990849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990924 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_1990924 : Nat := 118140960795 + 1990924 * 2 ^ 59
def prefixEnd_1990924 : Nat := 4983230072969 + 3 ^ 40 * 1990924 * 2
def baseEnd_1990924 : Nat := 340766986190691244797971

theorem tailTrace_1990924 : CollatzResearch.WordTrace tailWord_1990924 prefixEnd_1990924 340766986190691244797971 := by
  unfold tailWord_1990924
  simp only [CollatzResearch.WordTrace]
  refine ⟨36307481919614922796857913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48409975892819897062477217 36307481919614922796857913)
  ·
    refine ⟨27230611439711192097643435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36307481919614922796857913 27230611439711192097643435)
    ·
      refine ⟨40845917159566788146465153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27230611439711192097643435 40845917159566788146465153)
      ·
        refine ⟨30634437869675091109848865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40845917159566788146465153 30634437869675091109848865)
        ·
          refine ⟨22975828402256318332386649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30634437869675091109848865 22975828402256318332386649)
          ·
            refine ⟨17231871301692238749289987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22975828402256318332386649 17231871301692238749289987)
            ·
              refine ⟨25847806952538358123934981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17231871301692238749289987 25847806952538358123934981)
              ·
                refine ⟨4846463803600942148237809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25847806952538358123934981 4846463803600942148237809)
                ·
                  refine ⟨3634847852700706611178357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4846463803600942148237809 3634847852700706611178357)
                  ·
                    refine ⟨340766986190691244797971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3634847852700706611178357 340766986190691244797971)
                    ·
                      rfl

theorem cell23_1990924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_1990924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990924 prefixEnd_1990924 := by exact prefixLift 1990924
  have htrace : WordTrace (prefixWord ++ tailWord_1990924) baseStart_1990924 baseEnd_1990924 := by
    simpa [prefixWord, tailWord_1990924, baseEnd_1990924] using wordTrace_append hprefix tailTrace_1990924
  have hstable : (prefixWord ++ tailWord_1990924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990924).length < 2 ^ (prefixWord ++ tailWord_1990924).sum := by decide
  have hdescent : baseEnd_1990924 < baseStart_1990924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990958 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_1990958 : Nat := 118140960795 + 1990958 * 2 ^ 59
def prefixEnd_1990958 : Nat := 4983230072969 + 3 ^ 40 * 1990958 * 2
def baseEnd_1990958 : Nat := 340772805638108867122919

theorem tailTrace_1990958 : CollatzResearch.WordTrace tailWord_1990958 prefixEnd_1990958 340772805638108867122919 := by
  unfold tailWord_1990958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9077025490138333675056691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48410802614071112933635685 9077025490138333675056691)
  ·
    refine ⟨13615538235207500512585037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9077025490138333675056691 13615538235207500512585037)
    ·
      refine ⟨5105826838202812692219389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13615538235207500512585037 5105826838202812692219389)
      ·
        refine ⟨1914685064326054759582271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5105826838202812692219389 1914685064326054759582271)
        ·
          refine ⟨2872027596489082139373407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914685064326054759582271 2872027596489082139373407)
          ·
            refine ⟨4308041394733623209060111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2872027596489082139373407 4308041394733623209060111)
            ·
              refine ⟨6462062092100434813590167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4308041394733623209060111 6462062092100434813590167)
              ·
                refine ⟨9693093138150652220385251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6462062092100434813590167 9693093138150652220385251)
                ·
                  refine ⟨14539639707225978330577877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9693093138150652220385251 14539639707225978330577877)
                  ·
                    refine ⟨340772805638108867122919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14539639707225978330577877 340772805638108867122919)
                    ·
                      rfl

theorem cell23_1990958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_1990958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990958 prefixEnd_1990958 := by exact prefixLift 1990958
  have htrace : WordTrace (prefixWord ++ tailWord_1990958) baseStart_1990958 baseEnd_1990958 := by
    simpa [prefixWord, tailWord_1990958, baseEnd_1990958] using wordTrace_append hprefix tailTrace_1990958
  have hstable : (prefixWord ++ tailWord_1990958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990958).length < 2 ^ (prefixWord ++ tailWord_1990958).sum := by decide
  have hdescent : baseEnd_1990958 < baseStart_1990958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990961 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 4]
def baseStart_1990961 : Nat := 118140960795 + 1990961 * 2 ^ 59
def prefixEnd_1990961 : Nat := 4983230072969 + 3 ^ 40 * 1990961 * 2
def baseEnd_1990961 : Nat := 1022319957356290089631243

theorem tailTrace_1990961 : CollatzResearch.WordTrace tailWord_1990961 prefixEnd_1990961 1022319957356290089631243 := by
  unfold tailWord_1990961
  simp only [CollatzResearch.WordTrace]
  refine ⟨72616313340095800912812737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48410875560063867275208491 72616313340095800912812737)
  ·
    refine ⟨54462235005071850684609553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72616313340095800912812737 54462235005071850684609553)
    ·
      refine ⟨40846676253803888013457165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54462235005071850684609553 40846676253803888013457165)
      ·
        refine ⟨15317503595176458005046437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40846676253803888013457165 15317503595176458005046437)
        ·
          refine ⟨2872031924095585875946207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15317503595176458005046437 2872031924095585875946207)
          ·
            refine ⟨4308047886143378813919311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2872031924095585875946207 4308047886143378813919311)
            ·
              refine ⟨6462071829215068220878967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4308047886143378813919311 6462071829215068220878967)
              ·
                refine ⟨9693107743822602331318451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6462071829215068220878967 9693107743822602331318451)
                ·
                  refine ⟨14539661615733903496977677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9693107743822602331318451 14539661615733903496977677)
                  ·
                    refine ⟨5452373105900213811366629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14539661615733903496977677 5452373105900213811366629)
                    ·
                      refine ⟨1022319957356290089631243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5452373105900213811366629 1022319957356290089631243)
                      ·
                        rfl

theorem cell23_1990961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_1990961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990961 prefixEnd_1990961 := by exact prefixLift 1990961
  have htrace : WordTrace (prefixWord ++ tailWord_1990961) baseStart_1990961 baseEnd_1990961 := by
    simpa [prefixWord, tailWord_1990961, baseEnd_1990961] using wordTrace_append hprefix tailTrace_1990961
  have hstable : (prefixWord ++ tailWord_1990961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990961).length < 2 ^ (prefixWord ++ tailWord_1990961).sum := by decide
  have hdescent : baseEnd_1990961 < baseStart_1990961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990988 : List Nat := [2, 2, 1, 3, 2, 1, 1, 6, 1, 4]
def baseStart_1990988 : Nat := 118140960795 + 1990988 * 2 ^ 59
def prefixEnd_1990988 : Nat := 4983230072969 + 3 ^ 40 * 1990988 * 2
def baseEnd_1990988 : Nat := 340777940444653827997873

theorem tailTrace_1990988 : CollatzResearch.WordTrace tailWord_1990988 prefixEnd_1990988 340777940444653827997873 := by
  unfold tailWord_1990988
  simp only [CollatzResearch.WordTrace]
  refine ⟨36308649055498992262022809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48411532073998656349363745 36308649055498992262022809)
  ·
    refine ⟨27231486791624244196517107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36308649055498992262022809 27231486791624244196517107)
    ·
      refine ⟨40847230187436366294775661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27231486791624244196517107 40847230187436366294775661)
      ·
        refine ⟨15317711320288637360540873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40847230187436366294775661 15317711320288637360540873)
        ·
          refine ⟨11488283490216478020405655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15317711320288637360540873 11488283490216478020405655)
          ·
            refine ⟨17232425235324717030608483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11488283490216478020405655 17232425235324717030608483)
            ·
              refine ⟨25848637852987075545912725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17232425235324717030608483 25848637852987075545912725)
              ·
                refine ⟨1211654899358769166214659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25848637852987075545912725 1211654899358769166214659)
                ·
                  refine ⟨1817482349038153749321989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211654899358769166214659 1817482349038153749321989)
                  ·
                    refine ⟨340777940444653827997873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1817482349038153749321989 340777940444653827997873)
                    ·
                      rfl

theorem cell23_1990988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_1990988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1990988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1990988 prefixEnd_1990988 := by exact prefixLift 1990988
  have htrace : WordTrace (prefixWord ++ tailWord_1990988) baseStart_1990988 baseEnd_1990988 := by
    simpa [prefixWord, tailWord_1990988, baseEnd_1990988] using wordTrace_append hprefix tailTrace_1990988
  have hstable : (prefixWord ++ tailWord_1990988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990988).length < 2 ^ (prefixWord ++ tailWord_1990988).sum := by decide
  have hdescent : baseEnd_1990988 < baseStart_1990988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991118 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_1991118 : Nat := 118140960795 + 1991118 * 2 ^ 59
def prefixEnd_1991118 : Nat := 4983230072969 + 3 ^ 40 * 1991118 * 2
def baseEnd_1991118 : Nat := 1022400573819045975368021

theorem tailTrace_1991118 : CollatzResearch.WordTrace tailWord_1991118 prefixEnd_1991118 1022400573819045975368021 := by
  unfold tailWord_1991118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9077754950065877090784751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48414693067018011150852005 9077754950065877090784751)
  ·
    refine ⟨13616632425098815636177127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9077754950065877090784751 13616632425098815636177127)
    ·
      refine ⟨20424948637648223454265691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13616632425098815636177127 20424948637648223454265691)
      ·
        refine ⟨30637422956472335181398537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20424948637648223454265691 30637422956472335181398537)
        ·
          refine ⟨22978067217354251386048903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30637422956472335181398537 22978067217354251386048903)
          ·
            refine ⟨34467100826031377079073355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22978067217354251386048903 34467100826031377079073355)
            ·
              refine ⟨51700651239047065618610033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34467100826031377079073355 51700651239047065618610033)
              ·
                refine ⟨38775488429285299213957525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51700651239047065618610033 38775488429285299213957525)
                ·
                  refine ⟨1817601020122748400654259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38775488429285299213957525 1817601020122748400654259)
                  ·
                    refine ⟨2726401530184122600981389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1817601020122748400654259 2726401530184122600981389)
                    ·
                      refine ⟨1022400573819045975368021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2726401530184122600981389 1022400573819045975368021)
                      ·
                        rfl

theorem cell23_1991118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_1991118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991118 prefixEnd_1991118 := by exact prefixLift 1991118
  have htrace : WordTrace (prefixWord ++ tailWord_1991118) baseStart_1991118 baseEnd_1991118 := by
    simpa [prefixWord, tailWord_1991118, baseEnd_1991118] using wordTrace_append hprefix tailTrace_1991118
  have hstable : (prefixWord ++ tailWord_1991118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991118).length < 2 ^ (prefixWord ++ tailWord_1991118).sum := by decide
  have hdescent : baseEnd_1991118 < baseStart_1991118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991139 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 1, 2, 3]
def baseStart_1991139 : Nat := 118140960795 + 1991139 * 2 ^ 59
def prefixEnd_1991139 : Nat := 4983230072969 + 3 ^ 40 * 1991139 * 2
def baseEnd_1991139 : Nat := 1022411356912790393205425

theorem tailTrace_1991139 : CollatzResearch.WordTrace tailWord_1991139 prefixEnd_1991139 1022411356912790393205425 := by
  unfold tailWord_1991139
  simp only [CollatzResearch.WordTrace]
  refine ⟨72622805533450937312792471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48415203688967291541861647 72622805533450937312792471)
  ·
    refine ⟨108934208300176405969188707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72622805533450937312792471 108934208300176405969188707)
    ·
      refine ⟨163401312450264608953783061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108934208300176405969188707 163401312450264608953783061)
      ·
        refine ⟨7659436521106153544708581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163401312450264608953783061 7659436521106153544708581)
        ·
          refine ⟨1436144347707403789632859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7659436521106153544708581 1436144347707403789632859)
          ·
            refine ⟨2154216521561105684449289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436144347707403789632859 2154216521561105684449289)
            ·
              refine ⟨1615662391170829263336967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154216521561105684449289 1615662391170829263336967)
              ·
                refine ⟨2423493586756243895005451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615662391170829263336967 2423493586756243895005451)
                ·
                  refine ⟨3635240380134365842508177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423493586756243895005451 3635240380134365842508177)
                  ·
                    refine ⟨2726430285100774381881133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3635240380134365842508177 2726430285100774381881133)
                    ·
                      refine ⟨1022411356912790393205425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2726430285100774381881133 1022411356912790393205425)
                      ·
                        rfl

theorem cell23_1991139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_1991139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991139 prefixEnd_1991139 := by exact prefixLift 1991139
  have htrace : WordTrace (prefixWord ++ tailWord_1991139) baseStart_1991139 baseEnd_1991139 := by
    simpa [prefixWord, tailWord_1991139, baseEnd_1991139] using wordTrace_append hprefix tailTrace_1991139
  have hstable : (prefixWord ++ tailWord_1991139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991139).length < 2 ^ (prefixWord ++ tailWord_1991139).sum := by decide
  have hdescent : baseEnd_1991139 < baseStart_1991139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991161 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 1, 6, 3]
def baseStart_1991161 : Nat := 118140960795 + 1991161 * 2 ^ 59
def prefixEnd_1991161 : Nat := 4983230072969 + 3 ^ 40 * 1991161 * 2
def baseEnd_1991161 : Nat := 1022422653487189307130323

theorem tailTrace_1991161 : CollatzResearch.WordTrace tailWord_1991161 prefixEnd_1991161 1022422653487189307130323 := by
  unfold tailWord_1991161
  simp only [CollatzResearch.WordTrace]
  refine ⟨72623607939371235070093337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48415738626247490046728891 72623607939371235070093337)
  ·
    refine ⟨54467705954528426302570003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72623607939371235070093337 54467705954528426302570003)
    ·
      refine ⟨81701558931792639453855005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54467705954528426302570003 81701558931792639453855005)
      ·
        refine ⟨30638084599422239795195627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81701558931792639453855005 30638084599422239795195627)
        ·
          refine ⟨45957126899133359692793441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30638084599422239795195627 45957126899133359692793441)
          ·
            refine ⟨34467845174350019769595081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45957126899133359692793441 34467845174350019769595081)
            ·
              refine ⟨25850883880762514827196311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34467845174350019769595081 25850883880762514827196311)
              ·
                refine ⟨38776325821143772240794467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25850883880762514827196311 38776325821143772240794467)
                ·
                  refine ⟨58164488731715658361191701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38776325821143772240794467 58164488731715658361191701)
                  ·
                    refine ⟨2726460409299171485680861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58164488731715658361191701 2726460409299171485680861)
                    ·
                      refine ⟨1022422653487189307130323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2726460409299171485680861 1022422653487189307130323)
                      ·
                        rfl

theorem cell23_1991161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1991161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991161 prefixEnd_1991161 := by exact prefixLift 1991161
  have htrace : WordTrace (prefixWord ++ tailWord_1991161) baseStart_1991161 baseEnd_1991161 := by
    simpa [prefixWord, tailWord_1991161, baseEnd_1991161] using wordTrace_append hprefix tailTrace_1991161
  have hstable : (prefixWord ++ tailWord_1991161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991161).length < 2 ^ (prefixWord ++ tailWord_1991161).sum := by decide
  have hdescent : baseEnd_1991161 < baseStart_1991161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991171 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 4]
def baseStart_1991171 : Nat := 118140960795 + 1991171 * 2 ^ 59
def prefixEnd_1991171 : Nat := 4983230072969 + 3 ^ 40 * 1991171 * 2
def baseEnd_1991171 : Nat := 1022427788293734268005277

theorem tailTrace_1991171 : CollatzResearch.WordTrace tailWord_1991171 prefixEnd_1991171 1022427788293734268005277 := by
  unfold tailWord_1991171
  simp only [CollatzResearch.WordTrace]
  refine ⟨72623972669335006777957367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48415981779556671185304911 72623972669335006777957367)
  ·
    refine ⟨108935959004002510166936051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72623972669335006777957367 108935959004002510166936051)
    ·
      refine ⟨163403938506003765250404077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108935959004002510166936051 163403938506003765250404077)
      ·
        refine ⟨61276476939751411968901529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163403938506003765250404077 61276476939751411968901529)
        ·
          refine ⟨45957357704813558976676147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61276476939751411968901529 45957357704813558976676147)
          ·
            refine ⟨68936036557220338465014221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45957357704813558976676147 68936036557220338465014221)
            ·
              refine ⟨25851013708957626924380333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68936036557220338465014221 25851013708957626924380333)
              ·
                refine ⟨9694130140859110096642625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25851013708957626924380333 9694130140859110096642625)
                ·
                  refine ⟨7270597605644332572481969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9694130140859110096642625 7270597605644332572481969)
                  ·
                    refine ⟨5452948204233249429361477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7270597605644332572481969 5452948204233249429361477)
                    ·
                      refine ⟨1022427788293734268005277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5452948204233249429361477 1022427788293734268005277)
                      ·
                        rfl

theorem cell23_1991171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_1991171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991171 prefixEnd_1991171 := by exact prefixLift 1991171
  have htrace : WordTrace (prefixWord ++ tailWord_1991171) baseStart_1991171 baseEnd_1991171 := by
    simpa [prefixWord, tailWord_1991171, baseEnd_1991171] using wordTrace_append hprefix tailTrace_1991171
  have hstable : (prefixWord ++ tailWord_1991171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991171).length < 2 ^ (prefixWord ++ tailWord_1991171).sum := by decide
  have hdescent : baseEnd_1991171 < baseStart_1991171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991245 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1991245 : Nat := 118140960795 + 1991245 * 2 ^ 59
def prefixEnd_1991245 : Nat := 4983230072969 + 3 ^ 40 * 1991245 * 2
def baseEnd_1991245 : Nat := 340821928620722326159979

theorem tailTrace_1991245 : CollatzResearch.WordTrace tailWord_1991245 prefixEnd_1991245 340821928620722326159979 := by
  unfold tailWord_1991245
  simp only [CollatzResearch.WordTrace]
  refine ⟨72626671671066917416151189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48417781114044611610767459 72626671671066917416151189)
  ·
    refine ⟨3404375234581261753882087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72626671671066917416151189 3404375234581261753882087)
    ·
      refine ⟨5106562851871892630823131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3404375234581261753882087 5106562851871892630823131)
      ·
        refine ⟨7659844277807838946234697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5106562851871892630823131 7659844277807838946234697)
        ·
          refine ⟨5744883208355879209676023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7659844277807838946234697 5744883208355879209676023)
          ·
            refine ⟨8617324812533818814514035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5744883208355879209676023 8617324812533818814514035)
            ·
              refine ⟨12925987218800728221771053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8617324812533818814514035 12925987218800728221771053)
              ·
                refine ⟨4847245207050273083164145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12925987218800728221771053 4847245207050273083164145)
                ·
                  refine ⟨3635433905287704812373109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4847245207050273083164145 3635433905287704812373109)
                  ·
                    refine ⟨340821928620722326159979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3635433905287704812373109 340821928620722326159979)
                    ·
                      rfl

theorem cell23_1991245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1991245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991245 prefixEnd_1991245 := by exact prefixLift 1991245
  have htrace : WordTrace (prefixWord ++ tailWord_1991245) baseStart_1991245 baseEnd_1991245 := by
    simpa [prefixWord, tailWord_1991245, baseEnd_1991245] using wordTrace_append hprefix tailTrace_1991245
  have hstable : (prefixWord ++ tailWord_1991245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991245).length < 2 ^ (prefixWord ++ tailWord_1991245).sum := by decide
  have hdescent : baseEnd_1991245 < baseStart_1991245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991248 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 3, 6, 2]
def baseStart_1991248 : Nat := 118140960795 + 1991248 * 2 ^ 59
def prefixEnd_1991248 : Nat := 4983230072969 + 3 ^ 40 * 1991248 * 2
def baseEnd_1991248 : Nat := 1022467326304130466742423

theorem tailTrace_1991248 : CollatzResearch.WordTrace tailWord_1991248 prefixEnd_1991248 1022467326304130466742423 := by
  unfold tailWord_1991248
  simp only [CollatzResearch.WordTrace]
  refine ⟨36313390545028024464255199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48417854060037365952340265 36313390545028024464255199)
  ·
    refine ⟨54470085817542036696382799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36313390545028024464255199 54470085817542036696382799)
    ·
      refine ⟨81705128726313055044574199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54470085817542036696382799 81705128726313055044574199)
      ·
        refine ⟨122557693089469582566861299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81705128726313055044574199 122557693089469582566861299)
        ·
          refine ⟨183836539634204373850291949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122557693089469582566861299 183836539634204373850291949)
          ·
            refine ⟨68938702362826640193859481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183836539634204373850291949 68938702362826640193859481)
            ·
              refine ⟨51704026772119980145394611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68938702362826640193859481 51704026772119980145394611)
              ·
                refine ⟨77556040158179970218091917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51704026772119980145394611 77556040158179970218091917)
                ·
                  refine ⟨29083515059317488831784469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77556040158179970218091917 29083515059317488831784469)
                  ·
                    refine ⟨1363289768405507288989897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29083515059317488831784469 1363289768405507288989897)
                    ·
                      refine ⟨1022467326304130466742423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1363289768405507288989897 1022467326304130466742423)
                      ·
                        rfl

theorem cell23_1991248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 6, 2].length) (baseStart_1991248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991248 prefixEnd_1991248 := by exact prefixLift 1991248
  have htrace : WordTrace (prefixWord ++ tailWord_1991248) baseStart_1991248 baseEnd_1991248 := by
    simpa [prefixWord, tailWord_1991248, baseEnd_1991248] using wordTrace_append hprefix tailTrace_1991248
  have hstable : (prefixWord ++ tailWord_1991248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991248).length < 2 ^ (prefixWord ++ tailWord_1991248).sum := by decide
  have hdescent : baseEnd_1991248 < baseStart_1991248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991266 : List Nat := [3, 3, 2, 3, 1, 2, 2, 2, 5]
def baseStart_1991266 : Nat := 118140960795 + 1991266 * 2 ^ 59
def prefixEnd_1991266 : Nat := 4983230072969 + 3 ^ 40 * 1991266 * 2
def baseEnd_1991266 : Nat := 113608507661767932924149

theorem tailTrace_1991266 : CollatzResearch.WordTrace tailWord_1991266 prefixEnd_1991266 113608507661767932924149 := by
  unfold tailWord_1991266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18156859400997709500666413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48418291735993892001777101 18156859400997709500666413)
  ·
    refine ⟨6808822275374141062749905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18156859400997709500666413 6808822275374141062749905)
    ·
      refine ⟨5106616706530605797062429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6808822275374141062749905 5106616706530605797062429)
      ·
        refine ⟨1914981264948977173898411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5106616706530605797062429 1914981264948977173898411)
        ·
          refine ⟨2872471897423465760847617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914981264948977173898411 2872471897423465760847617)
          ·
            refine ⟨2154353923067599320635713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2872471897423465760847617 2154353923067599320635713)
            ·
              refine ⟨1615765442300699490476785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154353923067599320635713 1615765442300699490476785)
              ·
                refine ⟨1211824081725524617857589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615765442300699490476785 1211824081725524617857589)
                ·
                  refine ⟨113608507661767932924149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1211824081725524617857589 113608507661767932924149)
                  ·
                    rfl

theorem cell23_1991266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_1991266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991266 prefixEnd_1991266 := by exact prefixLift 1991266
  have htrace : WordTrace (prefixWord ++ tailWord_1991266) baseStart_1991266 baseEnd_1991266 := by
    simpa [prefixWord, tailWord_1991266, baseEnd_1991266] using wordTrace_append hprefix tailTrace_1991266
  have hstable : (prefixWord ++ tailWord_1991266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991266).length < 2 ^ (prefixWord ++ tailWord_1991266).sum := by decide
  have hdescent : baseEnd_1991266 < baseStart_1991266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991282 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 2, 4, 2]
def baseStart_1991282 : Nat := 118140960795 + 1991282 * 2 ^ 59
def prefixEnd_1991282 : Nat := 4983230072969 + 3 ^ 40 * 1991282 * 2
def baseEnd_1991282 : Nat := 1022484784646383333717267

theorem tailTrace_1991282 : CollatzResearch.WordTrace tailWord_1991282 prefixEnd_1991282 1022484784646383333717267 := by
  unfold tailWord_1991282
  simp only [CollatzResearch.WordTrace]
  refine ⟨18157005292983218183812025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48418680781288581823498733 18157005292983218183812025)
  ·
    refine ⟨13617753969737413637859019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18157005292983218183812025 13617753969737413637859019)
    ·
      refine ⟨20426630954606120456788529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13617753969737413637859019 20426630954606120456788529)
      ·
        refine ⟨15319973215954590342591397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20426630954606120456788529 15319973215954590342591397)
        ·
          refine ⟨2872494977991485689235887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15319973215954590342591397 2872494977991485689235887)
          ·
            refine ⟨4308742466987228533853831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2872494977991485689235887 4308742466987228533853831)
            ·
              refine ⟨6463113700480842800780747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4308742466987228533853831 6463113700480842800780747)
              ·
                refine ⟨9694670550721264201171121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6463113700480842800780747 9694670550721264201171121)
                ·
                  refine ⟨7271002913040948150878341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9694670550721264201171121 7271002913040948150878341)
                  ·
                    refine ⟨1363313046195177778289689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271002913040948150878341 1363313046195177778289689)
                    ·
                      refine ⟨1022484784646383333717267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1363313046195177778289689 1022484784646383333717267)
                      ·
                        rfl

theorem cell23_1991282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_1991282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991282 prefixEnd_1991282 := by exact prefixLift 1991282
  have htrace : WordTrace (prefixWord ++ tailWord_1991282) baseStart_1991282 baseEnd_1991282 := by
    simpa [prefixWord, tailWord_1991282, baseEnd_1991282] using wordTrace_append hprefix tailTrace_1991282
  have hstable : (prefixWord ++ tailWord_1991282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991282).length < 2 ^ (prefixWord ++ tailWord_1991282).sum := by decide
  have hdescent : baseEnd_1991282 < baseStart_1991282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991291 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 6]
def baseStart_1991291 : Nat := 118140960795 + 1991291 * 2 ^ 59
def prefixEnd_1991291 : Nat := 4983230072969 + 3 ^ 40 * 1991291 * 2
def baseEnd_1991291 : Nat := 1022489405972273798504725

theorem tailTrace_1991291 : CollatzResearch.WordTrace tailWord_1991291 prefixEnd_1991291 1022489405972273798504725 := by
  unfold tailWord_1991291
  simp only [CollatzResearch.WordTrace]
  refine ⟨72628349428900267272325727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48418899619266844848217151 72628349428900267272325727)
  ·
    refine ⟨108942524143350400908488591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72628349428900267272325727 108942524143350400908488591)
    ·
      refine ⟨163413786215025601362732887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108942524143350400908488591 163413786215025601362732887)
      ·
        refine ⟨245120679322538402044099331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163413786215025601362732887 245120679322538402044099331)
        ·
          refine ⟨367681018983807603066148997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245120679322538402044099331 367681018983807603066148997)
          ·
            refine ⟨68940191059463925574902937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367681018983807603066148997 68940191059463925574902937)
            ·
              refine ⟨51705143294597944181177203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68940191059463925574902937 51705143294597944181177203)
              ·
                refine ⟨77557714941896916271765805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51705143294597944181177203 77557714941896916271765805)
                ·
                  refine ⟨29084143103211343601912177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77557714941896916271765805 29084143103211343601912177)
                  ·
                    refine ⟨21813107327408507701434133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29084143103211343601912177 21813107327408507701434133)
                    ·
                      refine ⟨1022489405972273798504725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21813107327408507701434133 1022489405972273798504725)
                      ·
                        rfl

theorem cell23_1991291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_1991291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991291 prefixEnd_1991291 := by exact prefixLift 1991291
  have htrace : WordTrace (prefixWord ++ tailWord_1991291) baseStart_1991291 baseEnd_1991291 := by
    simpa [prefixWord, tailWord_1991291, baseEnd_1991291] using wordTrace_append hprefix tailTrace_1991291
  have hstable : (prefixWord ++ tailWord_1991291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991291).length < 2 ^ (prefixWord ++ tailWord_1991291).sum := by decide
  have hdescent : baseEnd_1991291 < baseStart_1991291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991311 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_1991311 : Nat := 118140960795 + 1991311 * 2 ^ 59
def prefixEnd_1991311 : Nat := 4983230072969 + 3 ^ 40 * 1991311 * 2
def baseEnd_1991311 : Nat := 1022499675585363720254633

theorem tailTrace_1991311 : CollatzResearch.WordTrace tailWord_1991311 prefixEnd_1991311 1022499675585363720254633 := by
  unfold tailWord_1991311
  simp only [CollatzResearch.WordTrace]
  refine ⟨72629078888827810688053787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48419385925885207125369191 72629078888827810688053787)
  ·
    refine ⟨108943618333241716032080681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72629078888827810688053787 108943618333241716032080681)
    ·
      refine ⟨81707713749931287024060511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108943618333241716032080681 81707713749931287024060511)
      ·
        refine ⟨122561570624896930536090767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81707713749931287024060511 122561570624896930536090767)
        ·
          refine ⟨183842355937345395804136151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122561570624896930536090767 183842355937345395804136151)
          ·
            refine ⟨275763533906018093706204227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183842355937345395804136151 275763533906018093706204227)
            ·
              refine ⟨413645300859027140559306341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275763533906018093706204227 413645300859027140559306341)
              ·
                refine ⟨77558493911067588854869939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413645300859027140559306341 77558493911067588854869939)
                ·
                  refine ⟨116337740866601383282304909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77558493911067588854869939 116337740866601383282304909)
                  ·
                    refine ⟨43626652824975518730864341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116337740866601383282304909 43626652824975518730864341)
                    ·
                      refine ⟨1022499675585363720254633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43626652824975518730864341 1022499675585363720254633)
                      ·
                        rfl

theorem cell23_1991311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_1991311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991311 prefixEnd_1991311 := by exact prefixLift 1991311
  have htrace : WordTrace (prefixWord ++ tailWord_1991311) baseStart_1991311 baseEnd_1991311 := by
    simpa [prefixWord, tailWord_1991311, baseEnd_1991311] using wordTrace_append hprefix tailTrace_1991311
  have hstable : (prefixWord ++ tailWord_1991311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991311).length < 2 ^ (prefixWord ++ tailWord_1991311).sum := by decide
  have hdescent : baseEnd_1991311 < baseStart_1991311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991332 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_1991332 : Nat := 118140960795 + 1991332 * 2 ^ 59
def prefixEnd_1991332 : Nat := 4983230072969 + 3 ^ 40 * 1991332 * 2
def baseEnd_1991332 : Nat := 1022510458679108138092037

theorem tailTrace_1991332 : CollatzResearch.WordTrace tailWord_1991332 prefixEnd_1991332 1022510458679108138092037 := by
  unfold tailWord_1991332
  simp only [CollatzResearch.WordTrace]
  refine ⟨36314922410875865637284125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48419896547834487516378833 36314922410875865637284125)
  ·
    refine ⟨13618095904078449613981547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36314922410875865637284125 13618095904078449613981547)
    ·
      refine ⟨20427143856117674420972321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13618095904078449613981547 20427143856117674420972321)
      ·
        refine ⟨15320357892088255815729241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20427143856117674420972321 15320357892088255815729241)
        ·
          refine ⟨11490268419066191861796931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15320357892088255815729241 11490268419066191861796931)
          ·
            refine ⟨17235402628599287792695397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11490268419066191861796931 17235402628599287792695397)
            ·
              refine ⟨3231637992862366461130387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17235402628599287792695397 3231637992862366461130387)
              ·
                refine ⟨4847456989293549691695581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3231637992862366461130387 4847456989293549691695581)
                ·
                  refine ⟨1817796370985081134385843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4847456989293549691695581 1817796370985081134385843)
                  ·
                    refine ⟨2726694556477621701578765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1817796370985081134385843 2726694556477621701578765)
                    ·
                      refine ⟨1022510458679108138092037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2726694556477621701578765 1022510458679108138092037)
                      ·
                        rfl

theorem cell23_1991332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_1991332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991332 prefixEnd_1991332 := by exact prefixLift 1991332
  have htrace : WordTrace (prefixWord ++ tailWord_1991332) baseStart_1991332 baseEnd_1991332 := by
    simpa [prefixWord, tailWord_1991332, baseEnd_1991332] using wordTrace_append hprefix tailTrace_1991332
  have hstable : (prefixWord ++ tailWord_1991332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991332).length < 2 ^ (prefixWord ++ tailWord_1991332).sum := by decide
  have hdescent : baseEnd_1991332 < baseStart_1991332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991372 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1991372 : Nat := 118140960795 + 1991372 * 2 ^ 59
def prefixEnd_1991372 : Nat := 4983230072969 + 3 ^ 40 * 1991372 * 2
def baseEnd_1991372 : Nat := 1022530997905287981591853

theorem tailTrace_1991372 : CollatzResearch.WordTrace tailWord_1991372 prefixEnd_1991372 1022530997905287981591853 := by
  unfold tailWord_1991372
  simp only [CollatzResearch.WordTrace]
  refine ⟨36315651870803409053012185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48420869161071212070682913 36315651870803409053012185)
  ·
    refine ⟨27236738903102556789759139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36315651870803409053012185 27236738903102556789759139)
    ·
      refine ⟨40855108354653835184638709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27236738903102556789759139 40855108354653835184638709)
      ·
        refine ⟨3830166408248797048559879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40855108354653835184638709 3830166408248797048559879)
        ·
          refine ⟨5745249612373195572839819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3830166408248797048559879 5745249612373195572839819)
          ·
            refine ⟨8617874418559793359259729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745249612373195572839819 8617874418559793359259729)
            ·
              refine ⟨6463405813919845019444797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8617874418559793359259729 6463405813919845019444797)
              ·
                refine ⟨2423777180219941882291799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6463405813919845019444797 2423777180219941882291799)
                ·
                  refine ⟨3635665770329912823437699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423777180219941882291799 3635665770329912823437699)
                  ·
                    refine ⟨5453498655494869235156549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3635665770329912823437699 5453498655494869235156549)
                    ·
                      refine ⟨1022530997905287981591853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5453498655494869235156549 1022530997905287981591853)
                      ·
                        rfl

theorem cell23_1991372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1991372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991372 prefixEnd_1991372 := by exact prefixLift 1991372
  have htrace : WordTrace (prefixWord ++ tailWord_1991372) baseStart_1991372 baseEnd_1991372 := by
    simpa [prefixWord, tailWord_1991372, baseEnd_1991372] using wordTrace_append hprefix tailTrace_1991372
  have hstable : (prefixWord ++ tailWord_1991372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991372).length < 2 ^ (prefixWord ++ tailWord_1991372).sum := by decide
  have hdescent : baseEnd_1991372 < baseStart_1991372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991395 : List Nat := [1, 1, 1, 7, 1, 2, 2, 8]
def baseStart_1991395 : Nat := 118140960795 + 1991395 * 2 ^ 59
def prefixEnd_1991395 : Nat := 4983230072969 + 3 ^ 40 * 1991395 * 2
def baseEnd_1991395 : Nat := 37871955850383014503861

theorem tailTrace_1991395 : CollatzResearch.WordTrace tailWord_1991395 prefixEnd_1991395 37871955850383014503861 := by
  unfold tailWord_1991395
  simp only [CollatzResearch.WordTrace]
  refine ⟨72632142620523493034111639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48421428413682328689407759 72632142620523493034111639)
  ·
    refine ⟨108948213930785239551167459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72632142620523493034111639 108948213930785239551167459)
    ·
      refine ⟨163422320896177859326751189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108948213930785239551167459 163422320896177859326751189)
      ·
        refine ⟨3830210646004168577970731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 163422320896177859326751189 3830210646004168577970731)
        ·
          refine ⟨5745315969006252866956097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3830210646004168577970731 5745315969006252866956097)
          ·
            refine ⟨4308986976754689650217073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5745315969006252866956097 4308986976754689650217073)
            ·
              refine ⟨3231740232566017237662805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4308986976754689650217073 3231740232566017237662805)
              ·
                refine ⟨37871955850383014503861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3231740232566017237662805 37871955850383014503861)
                ·
                  rfl

theorem cell23_1991395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 8].length) (baseStart_1991395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991395 prefixEnd_1991395 := by exact prefixLift 1991395
  have htrace : WordTrace (prefixWord ++ tailWord_1991395) baseStart_1991395 baseEnd_1991395 := by
    simpa [prefixWord, tailWord_1991395, baseEnd_1991395] using wordTrace_append hprefix tailTrace_1991395
  have hstable : (prefixWord ++ tailWord_1991395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991395).length < 2 ^ (prefixWord ++ tailWord_1991395).sum := by decide
  have hdescent : baseEnd_1991395 < baseStart_1991395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991418 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_1991418 : Nat := 118140960795 + 1991418 * 2 ^ 59
def prefixEnd_1991418 : Nat := 4983230072969 + 3 ^ 40 * 1991418 * 2
def baseEnd_1991418 : Nat := 1022554618015394801616641

theorem tailTrace_1991418 : CollatzResearch.WordTrace tailWord_1991418 prefixEnd_1991418 1022554618015394801616641 := by
  unfold tailWord_1991418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18158245374860041990549727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48421987666293445308132605 18158245374860041990549727)
  ·
    refine ⟨27237368062290062985824591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18158245374860041990549727 27237368062290062985824591)
    ·
      refine ⟨40856052093435094478736887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27237368062290062985824591 40856052093435094478736887)
      ·
        refine ⟨61284078140152641718105331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40856052093435094478736887 61284078140152641718105331)
        ·
          refine ⟨91926117210228962577157997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61284078140152641718105331 91926117210228962577157997)
          ·
            refine ⟨34472293953835860966434249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91926117210228962577157997 34472293953835860966434249)
            ·
              refine ⟨25854220465376895724825687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34472293953835860966434249 25854220465376895724825687)
              ·
                refine ⟨38781330698065343587238531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25854220465376895724825687 38781330698065343587238531)
                ·
                  refine ⟨58171996047098015380857797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38781330698065343587238531 58171996047098015380857797)
                  ·
                    refine ⟨10907249258830877883910837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58171996047098015380857797 10907249258830877883910837)
                    ·
                      refine ⟨1022554618015394801616641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10907249258830877883910837 1022554618015394801616641)
                      ·
                        rfl

theorem cell23_1991418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_1991418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991418 prefixEnd_1991418 := by exact prefixLift 1991418
  have htrace : WordTrace (prefixWord ++ tailWord_1991418) baseStart_1991418 baseEnd_1991418 := by
    simpa [prefixWord, tailWord_1991418, baseEnd_1991418] using wordTrace_append hprefix tailTrace_1991418
  have hstable : (prefixWord ++ tailWord_1991418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991418).length < 2 ^ (prefixWord ++ tailWord_1991418).sum := by decide
  have hdescent : baseEnd_1991418 < baseStart_1991418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991422 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1991422 : Nat := 118140960795 + 1991422 * 2 ^ 59
def prefixEnd_1991422 : Nat := 4983230072969 + 3 ^ 40 * 1991422 * 2
def baseEnd_1991422 : Nat := 1022556671938012785966623

theorem tailTrace_1991422 : CollatzResearch.WordTrace tailWord_1991422 prefixEnd_1991422 1022556671938012785966623 := by
  unfold tailWord_1991422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079140923928209580668065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48422084927617117763563013 9079140923928209580668065)
  ·
    refine ⟨6809355692946157185501049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9079140923928209580668065 6809355692946157185501049)
    ·
      refine ⟨5107016769709617889125787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6809355692946157185501049 5107016769709617889125787)
      ·
        refine ⟨7660525154564426833688681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5107016769709617889125787 7660525154564426833688681)
        ·
          refine ⟨5745393865923320125266511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7660525154564426833688681 5745393865923320125266511)
          ·
            refine ⟨8618090798884980187899767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745393865923320125266511 8618090798884980187899767)
            ·
              refine ⟨12927136198327470281849651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8618090798884980187899767 12927136198327470281849651)
              ·
                refine ⟨19390704297491205422774477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12927136198327470281849651 19390704297491205422774477)
                ·
                  refine ⟨7271514111559202033540429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19390704297491205422774477 7271514111559202033540429)
                  ·
                    refine ⟨2726817791834700762577661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7271514111559202033540429 2726817791834700762577661)
                    ·
                      refine ⟨1022556671938012785966623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2726817791834700762577661 1022556671938012785966623)
                      ·
                        rfl

theorem cell23_1991422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1991422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991422 prefixEnd_1991422 := by exact prefixLift 1991422
  have htrace : WordTrace (prefixWord ++ tailWord_1991422) baseStart_1991422 baseEnd_1991422 := by
    simpa [prefixWord, tailWord_1991422, baseEnd_1991422] using wordTrace_append hprefix tailTrace_1991422
  have hstable : (prefixWord ++ tailWord_1991422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991422).length < 2 ^ (prefixWord ++ tailWord_1991422).sum := by decide
  have hdescent : baseEnd_1991422 < baseStart_1991422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991426 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_1991426 : Nat := 118140960795 + 1991426 * 2 ^ 59
def prefixEnd_1991426 : Nat := 4983230072969 + 3 ^ 40 * 1991426 * 2
def baseEnd_1991426 : Nat := 1022558725860630770316605

theorem tailTrace_1991426 : CollatzResearch.WordTrace tailWord_1991426 prefixEnd_1991426 1022558725860630770316605 := by
  unfold tailWord_1991426
  simp only [CollatzResearch.WordTrace]
  refine ⟨18158318320852796332122533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48422182188940790218993421 18158318320852796332122533)
  ·
    refine ⟨3404684685159899312272975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18158318320852796332122533 3404684685159899312272975)
    ·
      refine ⟨5107027027739848968409463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3404684685159899312272975 5107027027739848968409463)
      ·
        refine ⟨7660540541609773452614195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5107027027739848968409463 7660540541609773452614195)
        ·
          refine ⟨11490810812414660178921293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7660540541609773452614195 11490810812414660178921293)
          ·
            refine ⟨4309054054655497567095485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11490810812414660178921293 4309054054655497567095485)
            ·
              refine ⟨1615895270495811587660807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4309054054655497567095485 1615895270495811587660807)
              ·
                refine ⟨2423842905743717381491211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615895270495811587660807 2423842905743717381491211)
                ·
                  refine ⟨3635764358615576072236817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423842905743717381491211 3635764358615576072236817)
                  ·
                    refine ⟨2726823268961682054177613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3635764358615576072236817 2726823268961682054177613)
                    ·
                      refine ⟨1022558725860630770316605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2726823268961682054177613 1022558725860630770316605)
                      ·
                        rfl

theorem cell23_1991426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_1991426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991426 prefixEnd_1991426 := by exact prefixLift 1991426
  have htrace : WordTrace (prefixWord ++ tailWord_1991426) baseStart_1991426 baseEnd_1991426 := by
    simpa [prefixWord, tailWord_1991426, baseEnd_1991426] using wordTrace_append hprefix tailTrace_1991426
  have hstable : (prefixWord ++ tailWord_1991426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991426).length < 2 ^ (prefixWord ++ tailWord_1991426).sum := by decide
  have hdescent : baseEnd_1991426 < baseStart_1991426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991455 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 2, 6]
def baseStart_1991455 : Nat := 118140960795 + 1991455 * 2 ^ 59
def prefixEnd_1991455 : Nat := 4983230072969 + 3 ^ 40 * 1991455 * 2
def baseEnd_1991455 : Nat := 340857872266537052284657

theorem tailTrace_1991455 : CollatzResearch.WordTrace tailWord_1991455 prefixEnd_1991455 340857872266537052284657 := by
  unfold tailWord_1991455
  simp only [CollatzResearch.WordTrace]
  refine ⟨72634331000306123281295819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48422887333537415520863879 72634331000306123281295819)
  ·
    refine ⟨108951496500459184921943729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72634331000306123281295819 108951496500459184921943729)
    ·
      refine ⟨81713622375344388691457797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108951496500459184921943729 81713622375344388691457797)
      ·
        refine ⟨15321304195377072879648337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81713622375344388691457797 15321304195377072879648337)
        ·
          refine ⟨11490978146532804659736253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15321304195377072879648337 11490978146532804659736253)
          ·
            refine ⟨4309116804949801747401095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11490978146532804659736253 4309116804949801747401095)
            ·
              refine ⟨6463675207424702621101643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4309116804949801747401095 6463675207424702621101643)
              ·
                refine ⟨9695512811137053931652465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6463675207424702621101643 9695512811137053931652465)
                ·
                  refine ⟨7271634608352790448739349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9695512811137053931652465 7271634608352790448739349)
                  ·
                    refine ⟨340857872266537052284657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7271634608352790448739349 340857872266537052284657)
                    ·
                      rfl

theorem cell23_1991455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_1991455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991455 prefixEnd_1991455 := by exact prefixLift 1991455
  have htrace : WordTrace (prefixWord ++ tailWord_1991455) baseStart_1991455 baseEnd_1991455 := by
    simpa [prefixWord, tailWord_1991455, baseEnd_1991455] using wordTrace_append hprefix tailTrace_1991455
  have hstable : (prefixWord ++ tailWord_1991455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991455).length < 2 ^ (prefixWord ++ tailWord_1991455).sum := by decide
  have hdescent : baseEnd_1991455 < baseStart_1991455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991535 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 4]
def baseStart_1991535 : Nat := 118140960795 + 1991535 * 2 ^ 59
def prefixEnd_1991535 : Nat := 4983230072969 + 3 ^ 40 * 1991535 * 2
def baseEnd_1991535 : Nat := 1022614695251970843853603

theorem tailTrace_1991535 : CollatzResearch.WordTrace tailWord_1991535 prefixEnd_1991535 1022614695251970843853603 := by
  unfold tailWord_1991535
  simp only [CollatzResearch.WordTrace]
  refine ⟨72637248840016296944208059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48424832560010864629472039 72637248840016296944208059)
  ·
    refine ⟨108955873260024445416312089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72637248840016296944208059 108955873260024445416312089)
    ·
      refine ⟨81716904945018334062234067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108955873260024445416312089 81716904945018334062234067)
      ·
        refine ⟨122575357417527501093351101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81716904945018334062234067 122575357417527501093351101)
        ·
          refine ⟨45965759031572812910006663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122575357417527501093351101 45965759031572812910006663)
          ·
            refine ⟨68948638547359219365009995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45965759031572812910006663 68948638547359219365009995)
            ·
              refine ⟨103422957821038829047514993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68948638547359219365009995 103422957821038829047514993)
              ·
                refine ⟨77567218365779121785636245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103422957821038829047514993 77567218365779121785636245)
                ·
                  refine ⟨3635963360895896333701699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77567218365779121785636245 3635963360895896333701699)
                  ·
                    refine ⟨5453945041343844500552549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3635963360895896333701699 5453945041343844500552549)
                    ·
                      refine ⟨1022614695251970843853603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5453945041343844500552549 1022614695251970843853603)
                      ·
                        rfl

theorem cell23_1991535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_1991535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991535 prefixEnd_1991535 := by exact prefixLift 1991535
  have htrace : WordTrace (prefixWord ++ tailWord_1991535) baseStart_1991535 baseEnd_1991535 := by
    simpa [prefixWord, tailWord_1991535, baseEnd_1991535] using wordTrace_append hprefix tailTrace_1991535
  have hstable : (prefixWord ++ tailWord_1991535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991535).length < 2 ^ (prefixWord ++ tailWord_1991535).sum := by decide
  have hdescent : baseEnd_1991535 < baseStart_1991535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991552 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 2, 4, 2]
def baseStart_1991552 : Nat := 118140960795 + 1991552 * 2 ^ 59
def prefixEnd_1991552 : Nat := 4983230072969 + 3 ^ 40 * 1991552 * 2
def baseEnd_1991552 : Nat := 1022623424423097277341025

theorem tailTrace_1991552 : CollatzResearch.WordTrace tailWord_1991552 prefixEnd_1991552 1022623424423097277341025 := by
  unfold tailWord_1991552
  simp only [CollatzResearch.WordTrace]
  refine ⟨36318934440477354423788455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48425245920636472565051273 36318934440477354423788455)
  ·
    refine ⟨54478401660716031635682683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36318934440477354423788455 54478401660716031635682683)
    ·
      refine ⟨81717602491074047453524025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54478401660716031635682683 81717602491074047453524025)
      ·
        refine ⟨61288201868305535590143019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81717602491074047453524025 61288201868305535590143019)
        ·
          refine ⟨91932302802458303385214529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61288201868305535590143019 91932302802458303385214529)
          ·
            refine ⟨68949227101843727538910897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91932302802458303385214529 68949227101843727538910897)
            ·
              refine ⟨51711920326382795654183173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68949227101843727538910897 51711920326382795654183173)
              ·
                refine ⟨9695985061196774185159345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51711920326382795654183173 9695985061196774185159345)
                ·
                  refine ⟨7271988795897580638869509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9695985061196774185159345 7271988795897580638869509)
                  ·
                    refine ⟨1363497899230796369788033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271988795897580638869509 1363497899230796369788033)
                    ·
                      refine ⟨1022623424423097277341025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1363497899230796369788033 1022623424423097277341025)
                      ·
                        rfl

theorem cell23_1991552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 4, 2].length) (baseStart_1991552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991552 prefixEnd_1991552 := by exact prefixLift 1991552
  have htrace : WordTrace (prefixWord ++ tailWord_1991552) baseStart_1991552 baseEnd_1991552 := by
    simpa [prefixWord, tailWord_1991552, baseEnd_1991552] using wordTrace_append hprefix tailTrace_1991552
  have hstable : (prefixWord ++ tailWord_1991552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991552).length < 2 ^ (prefixWord ++ tailWord_1991552).sum := by decide
  have hdescent : baseEnd_1991552 < baseStart_1991552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991625 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 4]
def baseStart_1991625 : Nat := 118140960795 + 1991625 * 2 ^ 59
def prefixEnd_1991625 : Nat := 4983230072969 + 3 ^ 40 * 1991625 * 2
def baseEnd_1991625 : Nat := 1022660908510875491728189

theorem tailTrace_1991625 : CollatzResearch.WordTrace tailWord_1991625 prefixEnd_1991625 1022660908510875491728189 := by
  unfold tailWord_1991625
  simp only [CollatzResearch.WordTrace]
  refine ⟨72640531409690242314984329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48427020939793494876656219 72640531409690242314984329)
  ·
    refine ⟨54480398557267681736238247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72640531409690242314984329 54480398557267681736238247)
    ·
      refine ⟨81720597835901522604357371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54480398557267681736238247 81720597835901522604357371)
      ·
        refine ⟨122580896753852283906536057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81720597835901522604357371 122580896753852283906536057)
        ·
          refine ⟨91935672565389212929902043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122580896753852283906536057 91935672565389212929902043)
          ·
            refine ⟨137903508848083819394853065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91935672565389212929902043 137903508848083819394853065)
            ·
              refine ⟨103427631636062864546139799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137903508848083819394853065 103427631636062864546139799)
              ·
                refine ⟨155141447454094296819209699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103427631636062864546139799 155141447454094296819209699)
                ·
                  refine ⟨232712171181141445228814549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155141447454094296819209699 232712171181141445228814549)
                  ·
                    refine ⟨5454191512058002622550341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 232712171181141445228814549 5454191512058002622550341)
                    ·
                      refine ⟨1022660908510875491728189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5454191512058002622550341 1022660908510875491728189)
                      ·
                        rfl

theorem cell23_1991625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_1991625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991625 prefixEnd_1991625 := by exact prefixLift 1991625
  have htrace : WordTrace (prefixWord ++ tailWord_1991625) baseStart_1991625 baseEnd_1991625 := by
    simpa [prefixWord, tailWord_1991625, baseEnd_1991625] using wordTrace_append hprefix tailTrace_1991625
  have hstable : (prefixWord ++ tailWord_1991625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991625).length < 2 ^ (prefixWord ++ tailWord_1991625).sum := by decide
  have hdescent : baseEnd_1991625 < baseStart_1991625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991636 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_1991636 : Nat := 118140960795 + 1991636 * 2 ^ 59
def prefixEnd_1991636 : Nat := 4983230072969 + 3 ^ 40 * 1991636 * 2
def baseEnd_1991636 : Nat := 1022666556798074948690639

theorem tailTrace_1991636 : CollatzResearch.WordTrace tailWord_1991636 prefixEnd_1991636 1022666556798074948690639 := by
  unfold tailWord_1991636
  simp only [CollatzResearch.WordTrace]
  refine ⟨36320466306325195596817381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48427288408433594129089841 36320466306325195596817381)
  ·
    refine ⟨6810087432435974174403259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36320466306325195596817381 6810087432435974174403259)
    ·
      refine ⟨10215131148653961261604889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6810087432435974174403259 10215131148653961261604889)
      ·
        refine ⟨7661348361490470946203667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10215131148653961261604889 7661348361490470946203667)
        ·
          refine ⟨11492022542235706419305501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661348361490470946203667 11492022542235706419305501)
          ·
            refine ⟨4309508453338389907239563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11492022542235706419305501 4309508453338389907239563)
            ·
              refine ⟨6464262680007584860859345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4309508453338389907239563 6464262680007584860859345)
              ·
                refine ⟨4848197010005688645644509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6464262680007584860859345 4848197010005688645644509)
                ·
                  refine ⟨1818073878752133242116691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4848197010005688645644509 1818073878752133242116691)
                  ·
                    refine ⟨2727110818128199863175037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1818073878752133242116691 2727110818128199863175037)
                    ·
                      refine ⟨1022666556798074948690639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2727110818128199863175037 1022666556798074948690639)
                      ·
                        rfl

theorem cell23_1991636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_1991636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991636 prefixEnd_1991636 := by exact prefixLift 1991636
  have htrace : WordTrace (prefixWord ++ tailWord_1991636) baseStart_1991636 baseEnd_1991636 := by
    simpa [prefixWord, tailWord_1991636, baseEnd_1991636] using wordTrace_append hprefix tailTrace_1991636
  have hstable : (prefixWord ++ tailWord_1991636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991636).length < 2 ^ (prefixWord ++ tailWord_1991636).sum := by decide
  have hdescent : baseEnd_1991636 < baseStart_1991636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991675 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 7]
def baseStart_1991675 : Nat := 118140960795 + 1991675 * 2 ^ 59
def prefixEnd_1991675 : Nat := 4983230072969 + 3 ^ 40 * 1991675 * 2
def baseEnd_1991675 : Nat := 1022686582543600296102959

theorem tailTrace_1991675 : CollatzResearch.WordTrace tailWord_1991675 prefixEnd_1991675 1022686582543600296102959 := by
  unfold tailWord_1991675
  simp only [CollatzResearch.WordTrace]
  refine ⟨72642355059509100854304479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48428236706339400569536319 72642355059509100854304479)
  ·
    refine ⟨108963532589263651281456719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72642355059509100854304479 108963532589263651281456719)
    ·
      refine ⟨163445298883895476922185079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108963532589263651281456719 163445298883895476922185079)
      ·
        refine ⟨245167948325843215383277619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163445298883895476922185079 245167948325843215383277619)
        ·
          refine ⟨367751922488764823074916429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245167948325843215383277619 367751922488764823074916429)
          ·
            refine ⟨137906970933286808653093661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367751922488764823074916429 137906970933286808653093661)
            ·
              refine ⟨51715114099982553244910123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137906970933286808653093661 51715114099982553244910123)
              ·
                refine ⟨77572671149973829867365185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51715114099982553244910123 77572671149973829867365185)
                ·
                  refine ⟨58179503362480372400523889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77572671149973829867365185 58179503362480372400523889)
                  ·
                    refine ⟨43634627521860279300392917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58179503362480372400523889 43634627521860279300392917)
                    ·
                      refine ⟨1022686582543600296102959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43634627521860279300392917 1022686582543600296102959)
                      ·
                        rfl

theorem cell23_1991675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_1991675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991675 prefixEnd_1991675 := by exact prefixLift 1991675
  have htrace : WordTrace (prefixWord ++ tailWord_1991675) baseStart_1991675 baseEnd_1991675 := by
    simpa [prefixWord, tailWord_1991675, baseEnd_1991675] using wordTrace_append hprefix tailTrace_1991675
  have hstable : (prefixWord ++ tailWord_1991675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991675).length < 2 ^ (prefixWord ++ tailWord_1991675).sum := by decide
  have hdescent : baseEnd_1991675 < baseStart_1991675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991676 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 3, 2, 2]
def baseStart_1991676 : Nat := 118140960795 + 1991676 * 2 ^ 59
def prefixEnd_1991676 : Nat := 4983230072969 + 3 ^ 40 * 1991676 * 2
def baseEnd_1991676 : Nat := 1022687096024254792190455

theorem tailTrace_1991676 : CollatzResearch.WordTrace tailWord_1991676 prefixEnd_1991676 1022687096024254792190455 := by
  unfold tailWord_1991676
  simp only [CollatzResearch.WordTrace]
  refine ⟨36321195766252739012545441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48428261021670318683393921 36321195766252739012545441)
  ·
    refine ⟨27240896824689554259409081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36321195766252739012545441 27240896824689554259409081)
    ·
      refine ⟨20430672618517165694556811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27240896824689554259409081 20430672618517165694556811)
      ·
        refine ⟨30646008927775748541835217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20430672618517165694556811 30646008927775748541835217)
        ·
          refine ⟨22984506695831811406376413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30646008927775748541835217 22984506695831811406376413)
          ·
            refine ⟨8619190010936929277391155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22984506695831811406376413 8619190010936929277391155)
            ·
              refine ⟨12928785016405393916086733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8619190010936929277391155 12928785016405393916086733)
              ·
                refine ⟨4848294381152022718532525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12928785016405393916086733 4848294381152022718532525)
                ·
                  refine ⟨1818110392932008519449697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4848294381152022718532525 1818110392932008519449697)
                  ·
                    refine ⟨1363582794699006389587273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1818110392932008519449697 1363582794699006389587273)
                    ·
                      refine ⟨1022687096024254792190455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1363582794699006389587273 1022687096024254792190455)
                      ·
                        rfl

theorem cell23_1991676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_1991676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991676 prefixEnd_1991676 := by exact prefixLift 1991676
  have htrace : WordTrace (prefixWord ++ tailWord_1991676) baseStart_1991676 baseEnd_1991676 := by
    simpa [prefixWord, tailWord_1991676, baseEnd_1991676] using wordTrace_append hprefix tailTrace_1991676
  have hstable : (prefixWord ++ tailWord_1991676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991676).length < 2 ^ (prefixWord ++ tailWord_1991676).sum := by decide
  have hdescent : baseEnd_1991676 < baseStart_1991676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991726 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_1991726 : Nat := 118140960795 + 1991726 * 2 ^ 59
def prefixEnd_1991726 : Nat := 4983230072969 + 3 ^ 40 * 1991726 * 2
def baseEnd_1991726 : Nat := 1022712770056979596565225

theorem tailTrace_1991726 : CollatzResearch.WordTrace tailWord_1991726 prefixEnd_1991726 1022712770056979596565225 := by
  unfold tailWord_1991726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080526897790542070551379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48429476788216224376274021 9080526897790542070551379)
  ·
    refine ⟨13620790346685813105827069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9080526897790542070551379 13620790346685813105827069)
    ·
      refine ⟨5107796380007179914685151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13620790346685813105827069 5107796380007179914685151)
      ·
        refine ⟨7661694570010769872027727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5107796380007179914685151 7661694570010769872027727)
        ·
          refine ⟨11492541855016154808041591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661694570010769872027727 11492541855016154808041591)
          ·
            refine ⟨17238812782524232212062387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11492541855016154808041591 17238812782524232212062387)
            ·
              refine ⟨25858219173786348318093581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17238812782524232212062387 25858219173786348318093581)
              ·
                refine ⟨9696832190169880619285093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25858219173786348318093581 9696832190169880619285093)
                ·
                  refine ⟨1818156035656852616115955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9696832190169880619285093 1818156035656852616115955)
                  ·
                    refine ⟨2727234053485278924173933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1818156035656852616115955 2727234053485278924173933)
                    ·
                      refine ⟨1022712770056979596565225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2727234053485278924173933 1022712770056979596565225)
                      ·
                        rfl

theorem cell23_1991726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_1991726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991726 prefixEnd_1991726 := by exact prefixLift 1991726
  have htrace : WordTrace (prefixWord ++ tailWord_1991726) baseStart_1991726 baseEnd_1991726 := by
    simpa [prefixWord, tailWord_1991726, baseEnd_1991726] using wordTrace_append hprefix tailTrace_1991726
  have hstable : (prefixWord ++ tailWord_1991726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991726).length < 2 ^ (prefixWord ++ tailWord_1991726).sum := by decide
  have hdescent : baseEnd_1991726 < baseStart_1991726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991752 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_1991752 : Nat := 118140960795 + 1991752 * 2 ^ 59
def prefixEnd_1991752 : Nat := 4983230072969 + 3 ^ 40 * 1991752 * 2
def baseEnd_1991752 : Nat := 1022726120553996494840105

theorem tailTrace_1991752 : CollatzResearch.WordTrace tailWord_1991752 prefixEnd_1991752 1022726120553996494840105 := by
  unfold tailWord_1991752
  simp only [CollatzResearch.WordTrace]
  refine ⟨36322581740115071502428755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48430108986820095336571673 36322581740115071502428755)
  ·
    refine ⟨54483872610172607253643133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36322581740115071502428755 54483872610172607253643133)
    ·
      refine ⟨20431452228814727720116175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54483872610172607253643133 20431452228814727720116175)
      ·
        refine ⟨30647178343222091580174263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20431452228814727720116175 30647178343222091580174263)
        ·
          refine ⟨45970767514833137370261395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30647178343222091580174263 45970767514833137370261395)
          ·
            refine ⟨68956151272249706055392093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45970767514833137370261395 68956151272249706055392093)
            ·
              refine ⟨25858556727093639770772035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68956151272249706055392093 25858556727093639770772035)
              ·
                refine ⟨38787835090640459656158053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25858556727093639770772035 38787835090640459656158053)
                ·
                  refine ⟨7272719079495086185529635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38787835090640459656158053 7272719079495086185529635)
                  ·
                    refine ⟨10909078619242629278294453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7272719079495086185529635 10909078619242629278294453)
                    ·
                      refine ⟨1022726120553996494840105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10909078619242629278294453 1022726120553996494840105)
                      ·
                        rfl

theorem cell23_1991752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_1991752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991752 prefixEnd_1991752 := by exact prefixLift 1991752
  have htrace : WordTrace (prefixWord ++ tailWord_1991752) baseStart_1991752 baseEnd_1991752 := by
    simpa [prefixWord, tailWord_1991752, baseEnd_1991752] using wordTrace_append hprefix tailTrace_1991752
  have hstable : (prefixWord ++ tailWord_1991752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991752).length < 2 ^ (prefixWord ++ tailWord_1991752).sum := by decide
  have hdescent : baseEnd_1991752 < baseStart_1991752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991783 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_1991783 : Nat := 118140960795 + 1991783 * 2 ^ 59
def prefixEnd_1991783 : Nat := 4983230072969 + 3 ^ 40 * 1991783 * 2
def baseEnd_1991783 : Nat := 1022742038454285873552463

theorem tailTrace_1991783 : CollatzResearch.WordTrace tailWord_1991783 prefixEnd_1991783 1022742038454285873552463 := by
  unfold tailWord_1991783
  simp only [CollatzResearch.WordTrace]
  refine ⟨72646294143117835299236003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48430862762078556866157335 72646294143117835299236003)
  ·
    refine ⟨108969441214676752948854005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72646294143117835299236003 108969441214676752948854005)
    ·
      refine ⟨10215885113875945588955063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108969441214676752948854005 10215885113875945588955063)
      ·
        refine ⟨15323827670813918383432595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10215885113875945588955063 15323827670813918383432595)
        ·
          refine ⟨22985741506220877575148893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15323827670813918383432595 22985741506220877575148893)
          ·
            refine ⟨8619653064832829090680835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22985741506220877575148893 8619653064832829090680835)
            ·
              refine ⟨12929479597249243636021253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8619653064832829090680835 12929479597249243636021253)
              ·
                refine ⟨2424277424484233181753985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12929479597249243636021253 2424277424484233181753985)
                ·
                  refine ⟨1818208068363174886315489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2424277424484233181753985 1818208068363174886315489)
                  ·
                    refine ⟨1363656051272381164736617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1818208068363174886315489 1363656051272381164736617)
                    ·
                      refine ⟨1022742038454285873552463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1363656051272381164736617 1022742038454285873552463)
                      ·
                        rfl

theorem cell23_1991783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_1991783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991783 prefixEnd_1991783 := by exact prefixLift 1991783
  have htrace : WordTrace (prefixWord ++ tailWord_1991783) baseStart_1991783 baseEnd_1991783 := by
    simpa [prefixWord, tailWord_1991783, baseEnd_1991783] using wordTrace_append hprefix tailTrace_1991783
  have hstable : (prefixWord ++ tailWord_1991783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991783).length < 2 ^ (prefixWord ++ tailWord_1991783).sum := by decide
  have hdescent : baseEnd_1991783 < baseStart_1991783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991799 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 3]
def baseStart_1991799 : Nat := 118140960795 + 1991799 * 2 ^ 59
def prefixEnd_1991799 : Nat := 4983230072969 + 3 ^ 40 * 1991799 * 2
def baseEnd_1991799 : Nat := 1022750254144757810952389

theorem tailTrace_1991799 : CollatzResearch.WordTrace tailWord_1991799 prefixEnd_1991799 1022750254144757810952389 := by
  unfold tailWord_1991799
  simp only [CollatzResearch.WordTrace]
  refine ⟨72646877711059870031818451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48431251807373246687878967 72646877711059870031818451)
  ·
    refine ⟨108970316566589805047727677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72646877711059870031818451 108970316566589805047727677)
    ·
      refine ⟨40863868712471176892897879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108970316566589805047727677 40863868712471176892897879)
      ·
        refine ⟨61295803068706765339346819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40863868712471176892897879 61295803068706765339346819)
        ·
          refine ⟨91943704603060148009020229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61295803068706765339346819 91943704603060148009020229)
          ·
            refine ⟨17239444613073777751691293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91943704603060148009020229 17239444613073777751691293)
            ·
              refine ⟨6464791729902666656884235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17239444613073777751691293 6464791729902666656884235)
              ·
                refine ⟨9697187594853999985326353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6464791729902666656884235 9697187594853999985326353)
                ·
                  refine ⟨7272890696140499988994765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9697187594853999985326353 7272890696140499988994765)
                  ·
                    refine ⟨2727334011052687495873037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7272890696140499988994765 2727334011052687495873037)
                    ·
                      refine ⟨1022750254144757810952389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2727334011052687495873037 1022750254144757810952389)
                      ·
                        rfl

theorem cell23_1991799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_1991799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991799 prefixEnd_1991799 := by exact prefixLift 1991799
  have htrace : WordTrace (prefixWord ++ tailWord_1991799) baseStart_1991799 baseEnd_1991799 := by
    simpa [prefixWord, tailWord_1991799, baseEnd_1991799] using wordTrace_append hprefix tailTrace_1991799
  have hstable : (prefixWord ++ tailWord_1991799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991799).length < 2 ^ (prefixWord ++ tailWord_1991799).sum := by decide
  have hdescent : baseEnd_1991799 < baseStart_1991799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991859 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 3]
def baseStart_1991859 : Nat := 118140960795 + 1991859 * 2 ^ 59
def prefixEnd_1991859 : Nat := 4983230072969 + 3 ^ 40 * 1991859 * 2
def baseEnd_1991859 : Nat := 1022781062984027576202113

theorem tailTrace_1991859 : CollatzResearch.WordTrace tailWord_1991859 prefixEnd_1991859 1022781062984027576202113 := by
  unfold tailWord_1991859
  simp only [CollatzResearch.WordTrace]
  refine ⟨72649066090842500279002631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48432710727228333519335087 72649066090842500279002631)
  ·
    refine ⟨108973599136263750418503947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72649066090842500279002631 108973599136263750418503947)
    ·
      refine ⟨163460398704395625627755921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108973599136263750418503947 163460398704395625627755921)
      ·
        refine ⟨122595299028296719220816941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163460398704395625627755921 122595299028296719220816941)
        ·
          refine ⟨45973237135611269707806353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122595299028296719220816941 45973237135611269707806353)
          ·
            refine ⟨34479927851708452280854765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45973237135611269707806353 34479927851708452280854765)
            ·
              refine ⟨12929972944390669605320537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34479927851708452280854765 12929972944390669605320537)
              ·
                refine ⟨9697479708293002203990403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12929972944390669605320537 9697479708293002203990403)
                ·
                  refine ⟨14546219562439503305985605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9697479708293002203990403 14546219562439503305985605)
                  ·
                    refine ⟨2727416167957406869872301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14546219562439503305985605 2727416167957406869872301)
                    ·
                      refine ⟨1022781062984027576202113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2727416167957406869872301 1022781062984027576202113)
                      ·
                        rfl

theorem cell23_1991859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 3].length) (baseStart_1991859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991859 prefixEnd_1991859 := by exact prefixLift 1991859
  have htrace : WordTrace (prefixWord ++ tailWord_1991859) baseStart_1991859 baseEnd_1991859 := by
    simpa [prefixWord, tailWord_1991859, baseEnd_1991859] using wordTrace_append hprefix tailTrace_1991859
  have hstable : (prefixWord ++ tailWord_1991859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991859).length < 2 ^ (prefixWord ++ tailWord_1991859).sum := by decide
  have hdescent : baseEnd_1991859 < baseStart_1991859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991874 : List Nat := [3, 5, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1991874 : Nat := 118140960795 + 1991874 * 2 ^ 59
def prefixEnd_1991874 : Nat := 4983230072969 + 3 ^ 40 * 1991874 * 2
def baseEnd_1991874 : Nat := 113643196132649446390505

theorem tailTrace_1991874 : CollatzResearch.WordTrace tailWord_1991874 prefixEnd_1991874 113643196132649446390505 := by
  unfold tailWord_1991874
  simp only [CollatzResearch.WordTrace]
  refine ⟨18162403296447039460199669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48433075457192105227199117 18162403296447039460199669)
  ·
    refine ⟨1702725309041909949393719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18162403296447039460199669 1702725309041909949393719)
    ·
      refine ⟨2554087963562864924090579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702725309041909949393719 2554087963562864924090579)
      ·
        refine ⟨3831131945344297386135869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554087963562864924090579 3831131945344297386135869)
        ·
          refine ⟨1436674479504111519800951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3831131945344297386135869 1436674479504111519800951)
          ·
            refine ⟨2155011719256167279701427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436674479504111519800951 2155011719256167279701427)
            ·
              refine ⟨3232517578884250919552141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155011719256167279701427 3232517578884250919552141)
              ·
                refine ⟨1212194092081594094832053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3232517578884250919552141 1212194092081594094832053)
                ·
                  refine ⟨113643196132649446390505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1212194092081594094832053 113643196132649446390505)
                  ·
                    rfl

theorem cell23_1991874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1991874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991874 prefixEnd_1991874 := by exact prefixLift 1991874
  have htrace : WordTrace (prefixWord ++ tailWord_1991874) baseStart_1991874 baseEnd_1991874 := by
    simpa [prefixWord, tailWord_1991874, baseEnd_1991874] using wordTrace_append hprefix tailTrace_1991874
  have hstable : (prefixWord ++ tailWord_1991874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991874).length < 2 ^ (prefixWord ++ tailWord_1991874).sum := by decide
  have hdescent : baseEnd_1991874 < baseStart_1991874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991893 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1991893 : Nat := 118140960795 + 1991893 * 2 ^ 59
def prefixEnd_1991893 : Nat := 4983230072969 + 3 ^ 40 * 1991893 * 2
def baseEnd_1991893 : Nat := 1022798521326280443176957

theorem tailTrace_1991893 : CollatzResearch.WordTrace tailWord_1991893 prefixEnd_1991893 1022798521326280443176957 := by
  unfold tailWord_1991893
  simp only [CollatzResearch.WordTrace]
  refine ⟨72650306172719324085740333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48433537448479549390493555 72650306172719324085740333)
  ·
    refine ⟨27243864814769746532152625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72650306172719324085740333 27243864814769746532152625)
    ·
      refine ⟨20432898611077309899114469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27243864814769746532152625 20432898611077309899114469)
      ·
        refine ⟨3831168489576995606083963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20432898611077309899114469 3831168489576995606083963)
        ·
          refine ⟨5746752734365493409125945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831168489576995606083963 5746752734365493409125945)
          ·
            refine ⟨4310064550774120056844459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5746752734365493409125945 4310064550774120056844459)
            ·
              refine ⟨6465096826161180085266689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310064550774120056844459 6465096826161180085266689)
              ·
                refine ⟨4848822619620885063950017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6465096826161180085266689 4848822619620885063950017)
                ·
                  refine ⟨3636616964715663797962513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4848822619620885063950017 3636616964715663797962513)
                  ·
                    refine ⟨2727462723536747848471885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3636616964715663797962513 2727462723536747848471885)
                    ·
                      refine ⟨1022798521326280443176957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2727462723536747848471885 1022798521326280443176957)
                      ·
                        rfl

theorem cell23_1991893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1991893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991893 prefixEnd_1991893 := by exact prefixLift 1991893
  have htrace : WordTrace (prefixWord ++ tailWord_1991893) baseStart_1991893 baseEnd_1991893 := by
    simpa [prefixWord, tailWord_1991893, baseEnd_1991893] using wordTrace_append hprefix tailTrace_1991893
  have hstable : (prefixWord ++ tailWord_1991893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991893).length < 2 ^ (prefixWord ++ tailWord_1991893).sum := by decide
  have hdescent : baseEnd_1991893 < baseStart_1991893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991939 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 3, 6]
def baseStart_1991939 : Nat := 118140960795 + 1991939 * 2 ^ 59
def prefixEnd_1991939 : Nat := 4983230072969 + 3 ^ 40 * 1991939 * 2
def baseEnd_1991939 : Nat := 340940713812129087733915

theorem tailTrace_1991939 : CollatzResearch.WordTrace tailWord_1991939 prefixEnd_1991939 340940713812129087733915 := by
  unfold tailWord_1991939
  simp only [CollatzResearch.WordTrace]
  refine ⟨72651983930552673941914871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48434655953701782627943247 72651983930552673941914871)
  ·
    refine ⟨108977975895829010912872307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72651983930552673941914871 108977975895829010912872307)
    ·
      refine ⟨163466963843743516369308461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108977975895829010912872307 163466963843743516369308461)
      ·
        refine ⟨61300111441403818638490673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163466963843743516369308461 61300111441403818638490673)
        ·
          refine ⟨45975083581052863978868005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61300111441403818638490673 45975083581052863978868005)
          ·
            refine ⟨8620328171447411996037751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45975083581052863978868005 8620328171447411996037751)
            ·
              refine ⟨12930492257171117994056627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8620328171447411996037751 12930492257171117994056627)
              ·
                refine ⟨19395738385756676991084941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12930492257171117994056627 19395738385756676991084941)
                ·
                  refine ⟨7273401894658753871656853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19395738385756676991084941 7273401894658753871656853)
                  ·
                    refine ⟨340940713812129087733915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7273401894658753871656853 340940713812129087733915)
                    ·
                      rfl

theorem cell23_1991939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 6].length) (baseStart_1991939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991939 prefixEnd_1991939 := by exact prefixLift 1991939
  have htrace : WordTrace (prefixWord ++ tailWord_1991939) baseStart_1991939 baseEnd_1991939 := by
    simpa [prefixWord, tailWord_1991939, baseEnd_1991939] using wordTrace_append hprefix tailTrace_1991939
  have hstable : (prefixWord ++ tailWord_1991939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991939).length < 2 ^ (prefixWord ++ tailWord_1991939).sum := by decide
  have hdescent : baseEnd_1991939 < baseStart_1991939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991963 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 3, 2, 2]
def baseStart_1991963 : Nat := 118140960795 + 1991963 * 2 ^ 59
def prefixEnd_1991963 : Nat := 4983230072969 + 3 ^ 40 * 1991963 * 2
def baseEnd_1991963 : Nat := 1022834464972095169301635

theorem tailTrace_1991963 : CollatzResearch.WordTrace tailWord_1991963 prefixEnd_1991963 1022834464972095169301635 := by
  unfold tailWord_1991963
  simp only [CollatzResearch.WordTrace]
  refine ⟨72652859282465726040788543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48435239521643817360525695 72652859282465726040788543)
  ·
    refine ⟨108979288923698589061182815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72652859282465726040788543 108979288923698589061182815)
    ·
      refine ⟨163468933385547883591774223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108979288923698589061182815 163468933385547883591774223)
      ·
        refine ⟨245203400078321825387661335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163468933385547883591774223 245203400078321825387661335)
        ·
          refine ⟨367805100117482738081492003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245203400078321825387661335 367805100117482738081492003)
          ·
            refine ⟨551707650176224107122238005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367805100117482738081492003 551707650176224107122238005)
            ·
              refine ⟨51722592204021010042709813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 551707650176224107122238005 51722592204021010042709813)
              ·
                refine ⟨4848993019126969691504045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51722592204021010042709813 4848993019126969691504045)
                ·
                  refine ⟨1818372382172613634314017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4848993019126969691504045 1818372382172613634314017)
                  ·
                    refine ⟨1363779286629460225735513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1818372382172613634314017 1363779286629460225735513)
                    ·
                      refine ⟨1022834464972095169301635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1363779286629460225735513 1022834464972095169301635)
                      ·
                        rfl

theorem cell23_1991963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 2, 2].length) (baseStart_1991963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991963 prefixEnd_1991963 := by exact prefixLift 1991963
  have htrace : WordTrace (prefixWord ++ tailWord_1991963) baseStart_1991963 baseEnd_1991963 := by
    simpa [prefixWord, tailWord_1991963, baseEnd_1991963] using wordTrace_append hprefix tailTrace_1991963
  have hstable : (prefixWord ++ tailWord_1991963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991963).length < 2 ^ (prefixWord ++ tailWord_1991963).sum := by decide
  have hdescent : baseEnd_1991963 < baseStart_1991963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991973 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 2, 4]
def baseStart_1991973 : Nat := 118140960795 + 1991973 * 2 ^ 59
def prefixEnd_1991973 : Nat := 4983230072969 + 3 ^ 40 * 1991973 * 2
def baseEnd_1991973 : Nat := 340946533259546710058863

theorem tailTrace_1991973 : CollatzResearch.WordTrace tailWord_1991973 prefixEnd_1991973 340946533259546710058863 := by
  unfold tailWord_1991973
  simp only [CollatzResearch.WordTrace]
  refine ⟨72653224012429497748652573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48435482674952998499101715 72653224012429497748652573)
  ·
    refine ⟨27244959004661061655744715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72653224012429497748652573 27244959004661061655744715)
    ·
      refine ⟨40867438506991592483617073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27244959004661061655744715 40867438506991592483617073)
      ·
        refine ⟨30650578880243694362712805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40867438506991592483617073 30650578880243694362712805)
        ·
          refine ⟨5746983540045692693008651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30650578880243694362712805 5746983540045692693008651)
          ·
            refine ⟨8620475310068539039512977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746983540045692693008651 8620475310068539039512977)
            ·
              refine ⟨6465356482551404279634733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8620475310068539039512977 6465356482551404279634733)
              ·
                refine ⟨2424508680956776604863025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6465356482551404279634733 2424508680956776604863025)
                ·
                  refine ⟨1818381510717582453647269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2424508680956776604863025 1818381510717582453647269)
                  ·
                    refine ⟨340946533259546710058863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1818381510717582453647269 340946533259546710058863)
                    ·
                      rfl

theorem cell23_1991973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_1991973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1991973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1991973 prefixEnd_1991973 := by exact prefixLift 1991973
  have htrace : WordTrace (prefixWord ++ tailWord_1991973) baseStart_1991973 baseEnd_1991973 := by
    simpa [prefixWord, tailWord_1991973, baseEnd_1991973] using wordTrace_append hprefix tailTrace_1991973
  have hstable : (prefixWord ++ tailWord_1991973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991973).length < 2 ^ (prefixWord ++ tailWord_1991973).sum := by decide
  have hdescent : baseEnd_1991973 < baseStart_1991973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992143 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 1, 6, 2]
def baseStart_1992143 : Nat := 118140960795 + 1992143 * 2 ^ 59
def prefixEnd_1992143 : Nat := 4983230072969 + 3 ^ 40 * 1992143 * 2
def baseEnd_1992143 : Nat := 1022926891489904465050807

theorem tailTrace_1992143 : CollatzResearch.WordTrace tailWord_1992143 prefixEnd_1992143 1022926891489904465050807 := by
  unfold tailWord_1992143
  simp only [CollatzResearch.WordTrace]
  refine ⟨72659424421813616782341083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48439616281209077854894055 72659424421813616782341083)
  ·
    refine ⟨108989136632720425173511625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72659424421813616782341083 108989136632720425173511625)
    ·
      refine ⟨81741852474540318880133719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108989136632720425173511625 81741852474540318880133719)
      ·
        refine ⟨122612778711810478320200579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81741852474540318880133719 122612778711810478320200579)
        ·
          refine ⟨183919168067715717480300869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122612778711810478320200579 183919168067715717480300869)
          ·
            refine ⟨34484844012696697027556413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183919168067715717480300869 34484844012696697027556413)
            ·
              refine ⟨12931816504761261385333655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34484844012696697027556413 12931816504761261385333655)
              ·
                refine ⟨19397724757141892078000483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12931816504761261385333655 19397724757141892078000483)
                ·
                  refine ⟨29096587135712838117000725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19397724757141892078000483 29096587135712838117000725)
                  ·
                    refine ⟨1363902521986539286734409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29096587135712838117000725 1363902521986539286734409)
                    ·
                      refine ⟨1022926891489904465050807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1363902521986539286734409 1022926891489904465050807)
                      ·
                        rfl

theorem cell23_1992143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 6, 2].length) (baseStart_1992143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992143 prefixEnd_1992143 := by exact prefixLift 1992143
  have htrace : WordTrace (prefixWord ++ tailWord_1992143) baseStart_1992143 baseEnd_1992143 := by
    simpa [prefixWord, tailWord_1992143, baseEnd_1992143] using wordTrace_append hprefix tailTrace_1992143
  have hstable : (prefixWord ++ tailWord_1992143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992143).length < 2 ^ (prefixWord ++ tailWord_1992143).sum := by decide
  have hdescent : baseEnd_1992143 < baseStart_1992143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992153 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 5, 4]
def baseStart_1992153 : Nat := 118140960795 + 1992153 * 2 ^ 59
def prefixEnd_1992153 : Nat := 4983230072969 + 3 ^ 40 * 1992153 * 2
def baseEnd_1992153 : Nat := 340977342098816475308587

theorem tailTrace_1992153 : CollatzResearch.WordTrace tailWord_1992153 prefixEnd_1992153 340977342098816475308587 := by
  unfold tailWord_1992153
  simp only [CollatzResearch.WordTrace]
  refine ⟨72659789151777388490205113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48439859434518258993470075 72659789151777388490205113)
  ·
    refine ⟨54494841863833041367653835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72659789151777388490205113 54494841863833041367653835)
    ·
      refine ⟨81742262795749562051480753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54494841863833041367653835 81742262795749562051480753)
      ·
        refine ⟨61306697096812171538610565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81742262795749562051480753 61306697096812171538610565)
        ·
          refine ⟨11495005705652282163489481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61306697096812171538610565 11495005705652282163489481)
          ·
            refine ⟨8621254279239211622617111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11495005705652282163489481 8621254279239211622617111)
            ·
              refine ⟨12931881418858817433925667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8621254279239211622617111 12931881418858817433925667)
              ·
                refine ⟨19397822128288226150888501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12931881418858817433925667 19397822128288226150888501)
                ·
                  refine ⟨1818545824527021201645797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19397822128288226150888501 1818545824527021201645797)
                  ·
                    refine ⟨340977342098816475308587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1818545824527021201645797 340977342098816475308587)
                    ·
                      rfl

theorem cell23_1992153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 4].length) (baseStart_1992153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992153 prefixEnd_1992153 := by exact prefixLift 1992153
  have htrace : WordTrace (prefixWord ++ tailWord_1992153) baseStart_1992153 baseEnd_1992153 := by
    simpa [prefixWord, tailWord_1992153, baseEnd_1992153] using wordTrace_append hprefix tailTrace_1992153
  have hstable : (prefixWord ++ tailWord_1992153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992153).length < 2 ^ (prefixWord ++ tailWord_1992153).sum := by decide
  have hdescent : baseEnd_1992153 < baseStart_1992153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992186 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_1992186 : Nat := 118140960795 + 1992186 * 2 ^ 59
def prefixEnd_1992186 : Nat := 4983230072969 + 3 ^ 40 * 1992186 * 2
def baseEnd_1992186 : Nat := 1022948971158047796813109

theorem tailTrace_1992186 : CollatzResearch.WordTrace tailWord_1992186 prefixEnd_1992186 1022948971158047796813109 := by
  unfold tailWord_1992186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18165248190164458781539103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48440661840438556750770941 18165248190164458781539103)
  ·
    refine ⟨27247872285246688172308655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18165248190164458781539103 27247872285246688172308655)
    ·
      refine ⟨40871808427870032258462983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27247872285246688172308655 40871808427870032258462983)
      ·
        refine ⟨61307712641805048387694475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40871808427870032258462983 61307712641805048387694475)
        ·
          refine ⟨91961568962707572581541713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61307712641805048387694475 91961568962707572581541713)
          ·
            refine ⟨68971176722030679436156285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91961568962707572581541713 68971176722030679436156285)
            ·
              refine ⟨25864191270761504788558607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68971176722030679436156285 25864191270761504788558607)
              ·
                refine ⟨38796286906142257182837911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25864191270761504788558607 38796286906142257182837911)
                ·
                  refine ⟨58194430359213385774256867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38796286906142257182837911 58194430359213385774256867)
                  ·
                    refine ⟨87291645538820078661385301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58194430359213385774256867 87291645538820078661385301)
                    ·
                      refine ⟨1022948971158047796813109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 87291645538820078661385301 1022948971158047796813109)
                      ·
                        rfl

theorem cell23_1992186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_1992186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992186 prefixEnd_1992186 := by exact prefixLift 1992186
  have htrace : WordTrace (prefixWord ++ tailWord_1992186) baseStart_1992186 baseEnd_1992186 := by
    simpa [prefixWord, tailWord_1992186, baseEnd_1992186] using wordTrace_append hprefix tailTrace_1992186
  have hstable : (prefixWord ++ tailWord_1992186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992186).length < 2 ^ (prefixWord ++ tailWord_1992186).sum := by decide
  have hdescent : baseEnd_1992186 < baseStart_1992186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992220 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_1992220 : Nat := 118140960795 + 1992220 * 2 ^ 59
def prefixEnd_1992220 : Nat := 4983230072969 + 3 ^ 40 * 1992220 * 2
def baseEnd_1992220 : Nat := 1022966429500300663787953

theorem tailTrace_1992220 : CollatzResearch.WordTrace tailWord_1992220 prefixEnd_1992220 1022966429500300663787953 := by
  unfold tailWord_1992220
  simp only [CollatzResearch.WordTrace]
  refine ⟨36331116421267329466447057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48441488561689772621929409 36331116421267329466447057)
  ·
    refine ⟨27248337315950497099835293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36331116421267329466447057 27248337315950497099835293)
    ·
      refine ⟨10218126493481436412438235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27248337315950497099835293 10218126493481436412438235)
      ·
        refine ⟨15327189740222154618657353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10218126493481436412438235 15327189740222154618657353)
        ·
          refine ⟨11495392305166615963993015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15327189740222154618657353 11495392305166615963993015)
          ·
            refine ⟨17243088457749923945989523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11495392305166615963993015 17243088457749923945989523)
            ·
              refine ⟨25864632686624885918984285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17243088457749923945989523 25864632686624885918984285)
              ·
                refine ⟨9699237257484332219619107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25864632686624885918984285 9699237257484332219619107)
                ·
                  refine ⟨14548855886226498329428661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9699237257484332219619107 14548855886226498329428661)
                  ·
                    refine ⟨1363955239333734218383937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14548855886226498329428661 1363955239333734218383937)
                    ·
                      refine ⟨1022966429500300663787953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1363955239333734218383937 1022966429500300663787953)
                      ·
                        rfl

theorem cell23_1992220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_1992220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992220 prefixEnd_1992220 := by exact prefixLift 1992220
  have htrace : WordTrace (prefixWord ++ tailWord_1992220) baseStart_1992220 baseEnd_1992220 := by
    simpa [prefixWord, tailWord_1992220, baseEnd_1992220] using wordTrace_append hprefix tailTrace_1992220
  have hstable : (prefixWord ++ tailWord_1992220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992220).length < 2 ^ (prefixWord ++ tailWord_1992220).sum := by decide
  have hdescent : baseEnd_1992220 < baseStart_1992220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992284 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_1992284 : Nat := 118140960795 + 1992284 * 2 ^ 59
def prefixEnd_1992284 : Nat := 4983230072969 + 3 ^ 40 * 1992284 * 2
def baseEnd_1992284 : Nat := 1022999292262188413387659

theorem tailTrace_1992284 : CollatzResearch.WordTrace tailWord_1992284 prefixEnd_1992284 1022999292262188413387659 := by
  unfold tailWord_1992284
  simp only [CollatzResearch.WordTrace]
  refine ⟨36332283557151398931611953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48443044742868531908815937 36332283557151398931611953)
  ·
    refine ⟨27249212667863549198708965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36332283557151398931611953 27249212667863549198708965)
    ·
      refine ⟨5109227375224415474757931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27249212667863549198708965 5109227375224415474757931)
      ·
        refine ⟨7663841062836623212136897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5109227375224415474757931 7663841062836623212136897)
        ·
          refine ⟨5747880797127467409102673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7663841062836623212136897 5747880797127467409102673)
          ·
            refine ⟨4310910597845600556827005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5747880797127467409102673 4310910597845600556827005)
            ·
              refine ⟨1616591474192100208810127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4310910597845600556827005 1616591474192100208810127)
              ·
                refine ⟨2424887211288150313215191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616591474192100208810127 2424887211288150313215191)
                ·
                  refine ⟨3637330816932225469822787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424887211288150313215191 3637330816932225469822787)
                  ·
                    refine ⟨5455996225398338204734181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3637330816932225469822787 5455996225398338204734181)
                    ·
                      refine ⟨1022999292262188413387659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5455996225398338204734181 1022999292262188413387659)
                      ·
                        rfl

theorem cell23_1992284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_1992284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992284 prefixEnd_1992284 := by exact prefixLift 1992284
  have htrace : WordTrace (prefixWord ++ tailWord_1992284) baseStart_1992284 baseEnd_1992284 := by
    simpa [prefixWord, tailWord_1992284, baseEnd_1992284] using wordTrace_append hprefix tailTrace_1992284
  have hstable : (prefixWord ++ tailWord_1992284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992284).length < 2 ^ (prefixWord ++ tailWord_1992284).sum := by decide
  have hdescent : baseEnd_1992284 < baseStart_1992284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992317 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_1992317 : Nat := 118140960795 + 1992317 * 2 ^ 59
def prefixEnd_1992317 : Nat := 4983230072969 + 3 ^ 40 * 1992317 * 2
def baseEnd_1992317 : Nat := 1023016237123786784275007

theorem tailTrace_1992317 : CollatzResearch.WordTrace tailWord_1992317 prefixEnd_1992317 1023016237123786784275007 := by
  unfold tailWord_1992317
  simp only [CollatzResearch.WordTrace]
  refine ⟨72665770723183244499175205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48443847148788829666116803 72665770723183244499175205)
  ·
    refine ⟨13624832010596858343595351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72665770723183244499175205 13624832010596858343595351)
    ·
      refine ⟨20437248015895287515393027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13624832010596858343595351 20437248015895287515393027)
      ·
        refine ⟨30655872023842931273089541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20437248015895287515393027 30655872023842931273089541)
        ·
          refine ⟨5747976004470549613704289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30655872023842931273089541 5747976004470549613704289)
          ·
            refine ⟨4310982003352912210278217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5747976004470549613704289 4310982003352912210278217)
            ·
              refine ⟨3233236502514684157708663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4310982003352912210278217 3233236502514684157708663)
              ·
                refine ⟨4849854753772026236562995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233236502514684157708663 4849854753772026236562995)
                ·
                  refine ⟨7274782130658039354844493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4849854753772026236562995 7274782130658039354844493)
                  ·
                    refine ⟨2728043298996764758066685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7274782130658039354844493 2728043298996764758066685)
                    ·
                      refine ⟨1023016237123786784275007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2728043298996764758066685 1023016237123786784275007)
                      ·
                        rfl

theorem cell23_1992317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_1992317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992317 prefixEnd_1992317 := by exact prefixLift 1992317
  have htrace : WordTrace (prefixWord ++ tailWord_1992317) baseStart_1992317 baseEnd_1992317 := by
    simpa [prefixWord, tailWord_1992317, baseEnd_1992317] using wordTrace_append hprefix tailTrace_1992317
  have hstable : (prefixWord ++ tailWord_1992317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992317).length < 2 ^ (prefixWord ++ tailWord_1992317).sum := by decide
  have hdescent : baseEnd_1992317 < baseStart_1992317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992323 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 4]
def baseStart_1992323 : Nat := 118140960795 + 1992323 * 2 ^ 59
def prefixEnd_1992323 : Nat := 4983230072969 + 3 ^ 40 * 1992323 * 2
def baseEnd_1992323 : Nat := 1023019318007713760799979

theorem tailTrace_1992323 : CollatzResearch.WordTrace tailWord_1992323 prefixEnd_1992323 1023019318007713760799979 := by
  unfold tailWord_1992323
  simp only [CollatzResearch.WordTrace]
  refine ⟨72665989561161507523893623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48443993040774338349262415 72665989561161507523893623)
  ·
    refine ⟨108998984341742261285840435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72665989561161507523893623 108998984341742261285840435)
    ·
      refine ⟨163498476512613391928760653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108998984341742261285840435 163498476512613391928760653)
      ·
        refine ⟨61311928692230021973285245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163498476512613391928760653 61311928692230021973285245)
        ·
          refine ⟨22991973259586258239981967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61311928692230021973285245 22991973259586258239981967)
          ·
            refine ⟨34487959889379387359972951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22991973259586258239981967 34487959889379387359972951)
            ·
              refine ⟨51731939834069081039959427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34487959889379387359972951 51731939834069081039959427)
              ·
                refine ⟨77597909751103621559939141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51731939834069081039959427 77597909751103621559939141)
                ·
                  refine ⟨14549608078331929042488589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77597909751103621559939141 14549608078331929042488589)
                  ·
                    refine ⟨5456103029374473390933221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14549608078331929042488589 5456103029374473390933221)
                    ·
                      refine ⟨1023019318007713760799979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5456103029374473390933221 1023019318007713760799979)
                      ·
                        rfl

theorem cell23_1992323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_1992323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992323 prefixEnd_1992323 := by exact prefixLift 1992323
  have htrace : WordTrace (prefixWord ++ tailWord_1992323) baseStart_1992323 baseEnd_1992323 := by
    simpa [prefixWord, tailWord_1992323, baseEnd_1992323] using wordTrace_append hprefix tailTrace_1992323
  have hstable : (prefixWord ++ tailWord_1992323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992323).length < 2 ^ (prefixWord ++ tailWord_1992323).sum := by decide
  have hdescent : baseEnd_1992323 < baseStart_1992323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992327 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 3, 3, 2]
def baseStart_1992327 : Nat := 118140960795 + 1992327 * 2 ^ 59
def prefixEnd_1992327 : Nat := 4983230072969 + 3 ^ 40 * 1992327 * 2
def baseEnd_1992327 : Nat := 1023021371930331745149961

theorem tailTrace_1992327 : CollatzResearch.WordTrace tailWord_1992327 prefixEnd_1992327 1023021371930331745149961 := by
  unfold tailWord_1992327
  simp only [CollatzResearch.WordTrace]
  refine ⟨72666135453147016207039235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48444090302098010804692823 72666135453147016207039235)
  ·
    refine ⟨108999203179720524310558853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72666135453147016207039235 108999203179720524310558853)
    ·
      refine ⟨20437350596197598308229785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108999203179720524310558853 20437350596197598308229785)
      ·
        refine ⟨15328012947148198731172339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20437350596197598308229785 15328012947148198731172339)
        ·
          refine ⟨22992019420722298096758509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15328012947148198731172339 22992019420722298096758509)
          ·
            refine ⟨8622007282770861786284441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22992019420722298096758509 8622007282770861786284441)
            ·
              refine ⟨6466505462078146339713331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8622007282770861786284441 6466505462078146339713331)
              ·
                refine ⟨9699758193117219509569997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466505462078146339713331 9699758193117219509569997)
                ·
                  refine ⟨3637409322418957316088749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9699758193117219509569997 3637409322418957316088749)
                  ·
                    refine ⟨1364028495907108993533281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637409322418957316088749 1364028495907108993533281)
                    ·
                      refine ⟨1023021371930331745149961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1364028495907108993533281 1023021371930331745149961)
                      ·
                        rfl

theorem cell23_1992327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_1992327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992327 prefixEnd_1992327 := by exact prefixLift 1992327
  have htrace : WordTrace (prefixWord ++ tailWord_1992327) baseStart_1992327 baseEnd_1992327 := by
    simpa [prefixWord, tailWord_1992327, baseEnd_1992327] using wordTrace_append hprefix tailTrace_1992327
  have hstable : (prefixWord ++ tailWord_1992327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992327).length < 2 ^ (prefixWord ++ tailWord_1992327).sum := by decide
  have hdescent : baseEnd_1992327 < baseStart_1992327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992338 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_1992338 : Nat := 118140960795 + 1992338 * 2 ^ 59
def prefixEnd_1992338 : Nat := 4983230072969 + 3 ^ 40 * 1992338 * 2
def baseEnd_1992338 : Nat := 1023027020217531202112411

theorem tailTrace_1992338 : CollatzResearch.WordTrace tailWord_1992338 prefixEnd_1992338 1023027020217531202112411 := by
  unfold tailWord_1992338
  simp only [CollatzResearch.WordTrace]
  refine ⟨18166634164026791271422417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48444357770738110057126445 18166634164026791271422417)
  ·
    refine ⟨13624975623020093453566813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18166634164026791271422417 13624975623020093453566813)
    ·
      refine ⟨5109365858632535045087555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13624975623020093453566813 5109365858632535045087555)
      ·
        refine ⟨7664048787948802567631333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5109365858632535045087555 7664048787948802567631333)
        ·
          refine ⟨1437009147740400481430875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7664048787948802567631333 1437009147740400481430875)
          ·
            refine ⟨2155513721610600722146313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437009147740400481430875 2155513721610600722146313)
            ·
              refine ⟨1616635291207950541609735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2155513721610600722146313 1616635291207950541609735)
              ·
                refine ⟨2424952936811925812414603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616635291207950541609735 2424952936811925812414603)
                ·
                  refine ⟨3637429405217888718621905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424952936811925812414603 3637429405217888718621905)
                  ·
                    refine ⟨2728072053913416538966429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3637429405217888718621905 2728072053913416538966429)
                    ·
                      refine ⟨1023027020217531202112411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2728072053913416538966429 1023027020217531202112411)
                      ·
                        rfl

theorem cell23_1992338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_1992338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992338 prefixEnd_1992338 := by exact prefixLift 1992338
  have htrace : WordTrace (prefixWord ++ tailWord_1992338) baseStart_1992338 baseEnd_1992338 := by
    simpa [prefixWord, tailWord_1992338, baseEnd_1992338] using wordTrace_append hprefix tailTrace_1992338
  have hstable : (prefixWord ++ tailWord_1992338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992338).length < 2 ^ (prefixWord ++ tailWord_1992338).sum := by decide
  have hdescent : baseEnd_1992338 < baseStart_1992338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992344 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 1, 3, 2]
def baseStart_1992344 : Nat := 118140960795 + 1992344 * 2 ^ 59
def prefixEnd_1992344 : Nat := 4983230072969 + 3 ^ 40 * 1992344 * 2
def baseEnd_1992344 : Nat := 1023030101101458178637383

theorem tailTrace_1992344 : CollatzResearch.WordTrace tailWord_1992344 prefixEnd_1992344 1023030101101458178637383 := by
  unfold tailWord_1992344
  simp only [CollatzResearch.WordTrace]
  refine ⟨36333377747042714055204043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48444503662723618740272057 36333377747042714055204043)
  ·
    refine ⟨54500066620564071082806065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36333377747042714055204043 54500066620564071082806065)
    ·
      refine ⟨40875049965423053312104549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54500066620564071082806065 40875049965423053312104549)
      ·
        refine ⟨7664071868516822496019603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40875049965423053312104549 7664071868516822496019603)
        ·
          refine ⟨11496107802775233744029405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664071868516822496019603 11496107802775233744029405)
          ·
            refine ⟨4311040426040712654011027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11496107802775233744029405 4311040426040712654011027)
            ·
              refine ⟨6466560639061068981016541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4311040426040712654011027 6466560639061068981016541)
              ·
                refine ⟨2424960239647900867881203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6466560639061068981016541 2424960239647900867881203)
                ·
                  refine ⟨3637440359471851301821805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424960239647900867881203 3637440359471851301821805)
                  ·
                    refine ⟨1364040134801944238183177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637440359471851301821805 1364040134801944238183177)
                    ·
                      refine ⟨1023030101101458178637383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1364040134801944238183177 1023030101101458178637383)
                      ·
                        rfl

theorem cell23_1992344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_1992344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992344 prefixEnd_1992344 := by exact prefixLift 1992344
  have htrace : WordTrace (prefixWord ++ tailWord_1992344) baseStart_1992344 baseEnd_1992344 := by
    simpa [prefixWord, tailWord_1992344, baseEnd_1992344] using wordTrace_append hprefix tailTrace_1992344
  have hstable : (prefixWord ++ tailWord_1992344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992344).length < 2 ^ (prefixWord ++ tailWord_1992344).sum := by decide
  have hdescent : baseEnd_1992344 < baseStart_1992344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992370 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_1992370 : Nat := 118140960795 + 1992370 * 2 ^ 59
def prefixEnd_1992370 : Nat := 4983230072969 + 3 ^ 40 * 1992370 * 2
def baseEnd_1992370 : Nat := 1023043451598475076912263

theorem tailTrace_1992370 : CollatzResearch.WordTrace tailWord_1992370 prefixEnd_1992370 1023043451598475076912263 := by
  unfold tailWord_1992370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18166925947997808637713641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48445135861327489700569709 18166925947997808637713641)
  ·
    refine ⟨13625194460998356478285231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18166925947997808637713641 13625194460998356478285231)
    ·
      refine ⟨20437791691497534717427847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13625194460998356478285231 20437791691497534717427847)
      ·
        refine ⟨30656687537246302076141771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20437791691497534717427847 30656687537246302076141771)
        ·
          refine ⟨45985031305869453114212657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30656687537246302076141771 45985031305869453114212657)
          ·
            refine ⟨34488773479402089835659493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45985031305869453114212657 34488773479402089835659493)
            ·
              refine ⟨6466645027387891844186155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34488773479402089835659493 6466645027387891844186155)
              ·
                refine ⟨9699967541081837766279233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466645027387891844186155 9699967541081837766279233)
                ·
                  refine ⟨7274975655811378324709425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9699967541081837766279233 7274975655811378324709425)
                  ·
                    refine ⟨5456231741858533743532069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7274975655811378324709425 5456231741858533743532069)
                    ·
                      refine ⟨1023043451598475076912263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5456231741858533743532069 1023043451598475076912263)
                      ·
                        rfl

theorem cell23_1992370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_1992370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992370 prefixEnd_1992370 := by exact prefixLift 1992370
  have htrace : WordTrace (prefixWord ++ tailWord_1992370) baseStart_1992370 baseEnd_1992370 := by
    simpa [prefixWord, tailWord_1992370, baseEnd_1992370] using wordTrace_append hprefix tailTrace_1992370
  have hstable : (prefixWord ++ tailWord_1992370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992370).length < 2 ^ (prefixWord ++ tailWord_1992370).sum := by decide
  have hdescent : baseEnd_1992370 < baseStart_1992370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992380 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 7]
def baseStart_1992380 : Nat := 118140960795 + 1992380 * 2 ^ 59
def prefixEnd_1992380 : Nat := 4983230072969 + 3 ^ 40 * 1992380 * 2
def baseEnd_1992380 : Nat := 113672065156113337531913

theorem tailTrace_1992380 : CollatzResearch.WordTrace tailWord_1992380 prefixEnd_1992380 113672065156113337531913 := by
  unfold tailWord_1992380
  simp only [CollatzResearch.WordTrace]
  refine ⟨36334034260977503129359297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48445379014636670839145729 36334034260977503129359297)
  ·
    refine ⟨27250525695733127347019473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36334034260977503129359297 27250525695733127347019473)
    ·
      refine ⟨20437894271799845510264605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27250525695733127347019473 20437894271799845510264605)
      ·
        refine ⟨7664210351924942066349227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20437894271799845510264605 7664210351924942066349227)
        ·
          refine ⟨11496315527887413099523841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664210351924942066349227 11496315527887413099523841)
          ·
            refine ⟨8622236645915559824642881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11496315527887413099523841 8622236645915559824642881)
            ·
              refine ⟨6466677484436669868482161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8622236645915559824642881 6466677484436669868482161)
              ·
                refine ⟨4850008113327502401361621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6466677484436669868482161 4850008113327502401361621)
                ·
                  refine ⟨113672065156113337531913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4850008113327502401361621 113672065156113337531913)
                  ·
                    rfl

theorem cell23_1992380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_1992380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992380 prefixEnd_1992380 := by exact prefixLift 1992380
  have htrace : WordTrace (prefixWord ++ tailWord_1992380) baseStart_1992380 baseEnd_1992380 := by
    simpa [prefixWord, tailWord_1992380, baseEnd_1992380] using wordTrace_append hprefix tailTrace_1992380
  have hstable : (prefixWord ++ tailWord_1992380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992380).length < 2 ^ (prefixWord ++ tailWord_1992380).sum := by decide
  have hdescent : baseEnd_1992380 < baseStart_1992380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992403 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 5]
def baseStart_1992403 : Nat := 118140960795 + 1992403 * 2 ^ 59
def prefixEnd_1992403 : Nat := 4983230072969 + 3 ^ 40 * 1992403 * 2
def baseEnd_1992403 : Nat := 1023060396460073447799611

theorem tailTrace_1992403 : CollatzResearch.WordTrace tailWord_1992403 prefixEnd_1992403 1023060396460073447799611 := by
  unfold tailWord_1992403
  simp only [CollatzResearch.WordTrace]
  refine ⟨72668907400871681186805863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48445938267247787457870575 72668907400871681186805863)
  ·
    refine ⟨109003361101307521780208795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72668907400871681186805863 109003361101307521780208795)
    ·
      refine ⟨163505041651961282670313193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109003361101307521780208795 163505041651961282670313193)
      ·
        refine ⟨122628781238970962002734895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163505041651961282670313193 122628781238970962002734895)
        ·
          refine ⟨183943171858456443004102343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122628781238970962002734895 183943171858456443004102343)
          ·
            refine ⟨275914757787684664506153515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183943171858456443004102343 275914757787684664506153515)
            ·
              refine ⟨413872136681526996759230273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275914757787684664506153515 413872136681526996759230273)
              ·
                refine ⟨310404102511145247569422705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413872136681526996759230273 310404102511145247569422705)
                ·
                  refine ⟨232803076883358935677067029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310404102511145247569422705 232803076883358935677067029)
                  ·
                    refine ⟨10912644228907450109862517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 232803076883358935677067029 10912644228907450109862517)
                    ·
                      refine ⟨1023060396460073447799611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10912644228907450109862517 1023060396460073447799611)
                      ·
                        rfl

theorem cell23_1992403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_1992403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992403 prefixEnd_1992403 := by exact prefixLift 1992403
  have htrace : WordTrace (prefixWord ++ tailWord_1992403) baseStart_1992403 baseEnd_1992403 := by
    simpa [prefixWord, tailWord_1992403, baseEnd_1992403] using wordTrace_append hprefix tailTrace_1992403
  have hstable : (prefixWord ++ tailWord_1992403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992403).length < 2 ^ (prefixWord ++ tailWord_1992403).sum := by decide
  have hdescent : baseEnd_1992403 < baseStart_1992403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992410 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_1992410 : Nat := 118140960795 + 1992410 * 2 ^ 59
def prefixEnd_1992410 : Nat := 4983230072969 + 3 ^ 40 * 1992410 * 2
def baseEnd_1992410 : Nat := 341021330274884973470693

theorem tailTrace_1992410 : CollatzResearch.WordTrace tailWord_1992410 prefixEnd_1992410 341021330274884973470693 := by
  unfold tailWord_1992410
  simp only [CollatzResearch.WordTrace]
  refine ⟨18167290677961580345577671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48446108474564214254873789 18167290677961580345577671)
  ·
    refine ⟨27250936016942370518366507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18167290677961580345577671 27250936016942370518366507)
    ·
      refine ⟨40876404025413555777549761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27250936016942370518366507 40876404025413555777549761)
      ·
        refine ⟨30657303019060166833162321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40876404025413555777549761 30657303019060166833162321)
        ·
          refine ⟨22992977264295125124871741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30657303019060166833162321 22992977264295125124871741)
          ·
            refine ⟨8622366474110671921826903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22992977264295125124871741 8622366474110671921826903)
            ·
              refine ⟨12933549711166007882740355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622366474110671921826903 12933549711166007882740355)
              ·
                refine ⟨19400324566749011824110533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12933549711166007882740355 19400324566749011824110533)
                ·
                  refine ⟨3637560856265439717020725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19400324566749011824110533 3637560856265439717020725)
                  ·
                    refine ⟨341021330274884973470693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3637560856265439717020725 341021330274884973470693)
                    ·
                      rfl

theorem cell23_1992410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_1992410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992410 prefixEnd_1992410 := by exact prefixLift 1992410
  have htrace : WordTrace (prefixWord ++ tailWord_1992410) baseStart_1992410 baseEnd_1992410 := by
    simpa [prefixWord, tailWord_1992410, baseEnd_1992410] using wordTrace_append hprefix tailTrace_1992410
  have hstable : (prefixWord ++ tailWord_1992410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992410).length < 2 ^ (prefixWord ++ tailWord_1992410).sum := by decide
  have hdescent : baseEnd_1992410 < baseStart_1992410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992420 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_1992420 : Nat := 118140960795 + 1992420 * 2 ^ 59
def prefixEnd_1992420 : Nat := 4983230072969 + 3 ^ 40 * 1992420 * 2
def baseEnd_1992420 : Nat := 1023069125631199881287033

theorem tailTrace_1992420 : CollatzResearch.WordTrace tailWord_1992420 prefixEnd_1992420 1023069125631199881287033 := by
  unfold tailWord_1992420
  simp only [CollatzResearch.WordTrace]
  refine ⟨36334763720905046545087357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48446351627873395393449809 36334763720905046545087357)
  ·
    refine ⟨13625536395339392454407759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36334763720905046545087357 13625536395339392454407759)
    ·
      refine ⟨20438304593009088681611639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13625536395339392454407759 20438304593009088681611639)
      ·
        refine ⟨30657456889513633022417459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20438304593009088681611639 30657456889513633022417459)
        ·
          refine ⟨45986185334270449533626189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30657456889513633022417459 45986185334270449533626189)
          ·
            refine ⟨17244819500351418575109821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45986185334270449533626189 17244819500351418575109821)
            ·
              refine ⟨6466807312631781965666183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17244819500351418575109821 6466807312631781965666183)
              ·
                refine ⟨9700210968947672948499275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466807312631781965666183 9700210968947672948499275)
                ·
                  refine ⟨14550316453421509422748913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9700210968947672948499275 14550316453421509422748913)
                  ·
                    refine ⟨10912737340066132067061685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14550316453421509422748913 10912737340066132067061685)
                    ·
                      refine ⟨1023069125631199881287033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10912737340066132067061685 1023069125631199881287033)
                      ·
                        rfl

theorem cell23_1992420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_1992420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992420 prefixEnd_1992420 := by exact prefixLift 1992420
  have htrace : WordTrace (prefixWord ++ tailWord_1992420) baseStart_1992420 baseEnd_1992420 := by
    simpa [prefixWord, tailWord_1992420, baseEnd_1992420] using wordTrace_append hprefix tailTrace_1992420
  have hstable : (prefixWord ++ tailWord_1992420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992420).length < 2 ^ (prefixWord ++ tailWord_1992420).sum := by decide
  have hdescent : baseEnd_1992420 < baseStart_1992420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992501 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_1992501 : Nat := 118140960795 + 1992501 * 2 ^ 59
def prefixEnd_1992501 : Nat := 4983230072969 + 3 ^ 40 * 1992501 * 2
def baseEnd_1992501 : Nat := 1023110717564214064374161

theorem tailTrace_1992501 : CollatzResearch.WordTrace tailWord_1992501 prefixEnd_1992501 1023110717564214064374161 := by
  unfold tailWord_1992501
  simp only [CollatzResearch.WordTrace]
  refine ⟨72672481754516643923873357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48448321169677762615915571 72672481754516643923873357)
  ·
    refine ⟨27252180657943741471452509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72672481754516643923873357 27252180657943741471452509)
    ·
      refine ⟨10219567746728903051794691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27252180657943741471452509 10219567746728903051794691)
      ·
        refine ⟨15329351620093354577692037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10219567746728903051794691 15329351620093354577692037)
        ·
          refine ⟨2874253428767503983317257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15329351620093354577692037 2874253428767503983317257)
          ·
            refine ⟨2155690071575627987487943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2874253428767503983317257 2155690071575627987487943)
            ·
              refine ⟨3233535107363441981231915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155690071575627987487943 3233535107363441981231915)
              ·
                refine ⟨4850302661045162971847873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233535107363441981231915 4850302661045162971847873)
                ·
                  refine ⟨3637726995783872228885905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4850302661045162971847873 3637726995783872228885905)
                  ·
                    refine ⟨2728295246837904171664429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3637726995783872228885905 2728295246837904171664429)
                    ·
                      refine ⟨1023110717564214064374161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2728295246837904171664429 1023110717564214064374161)
                      ·
                        rfl

theorem cell23_1992501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_1992501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992501 prefixEnd_1992501 := by exact prefixLift 1992501
  have htrace : WordTrace (prefixWord ++ tailWord_1992501) baseStart_1992501 baseEnd_1992501 := by
    simpa [prefixWord, tailWord_1992501, baseEnd_1992501] using wordTrace_append hprefix tailTrace_1992501
  have hstable : (prefixWord ++ tailWord_1992501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992501).length < 2 ^ (prefixWord ++ tailWord_1992501).sum := by decide
  have hdescent : baseEnd_1992501 < baseStart_1992501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992517 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 1, 5]
def baseStart_1992517 : Nat := 118140960795 + 1992517 * 2 ^ 59
def prefixEnd_1992517 : Nat := 4983230072969 + 3 ^ 40 * 1992517 * 2
def baseEnd_1992517 : Nat := 341039644418228667258029

theorem tailTrace_1992517 : CollatzResearch.WordTrace tailWord_1992517 prefixEnd_1992517 341039644418228667258029 := by
  unfold tailWord_1992517
  simp only [CollatzResearch.WordTrace]
  refine ⟨72673065322458678656455805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48448710214972452437637203 72673065322458678656455805)
  ·
    refine ⟨27252399495922004496170927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72673065322458678656455805 27252399495922004496170927)
    ·
      refine ⟨40878599243883006744256391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27252399495922004496170927 40878599243883006744256391)
      ·
        refine ⟨61317898865824510116384587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40878599243883006744256391 61317898865824510116384587)
        ·
          refine ⟨91976848298736765174576881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61317898865824510116384587 91976848298736765174576881)
          ·
            refine ⟨68982636224052573880932661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91976848298736765174576881 68982636224052573880932661)
            ·
              refine ⟨6467122146004928801337437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68982636224052573880932661 6467122146004928801337437)
              ·
                refine ⟨2425170804751848300501539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6467122146004928801337437 2425170804751848300501539)
                ·
                  refine ⟨3637756207127772450752309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425170804751848300501539 3637756207127772450752309)
                  ·
                    refine ⟨341039644418228667258029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3637756207127772450752309 341039644418228667258029)
                    ·
                      rfl

theorem cell23_1992517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_1992517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992517 prefixEnd_1992517 := by exact prefixLift 1992517
  have htrace : WordTrace (prefixWord ++ tailWord_1992517) baseStart_1992517 baseEnd_1992517 := by
    simpa [prefixWord, tailWord_1992517, baseEnd_1992517] using wordTrace_append hprefix tailTrace_1992517
  have hstable : (prefixWord ++ tailWord_1992517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992517).length < 2 ^ (prefixWord ++ tailWord_1992517).sum := by decide
  have hdescent : baseEnd_1992517 < baseStart_1992517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992594 : List Nat := [3, 2, 3, 2, 1, 2, 2, 8]
def baseStart_1992594 : Nat := 118140960795 + 1992594 * 2 ^ 59
def prefixEnd_1992594 : Nat := 4983230072969 + 3 ^ 40 * 1992594 * 2
def baseEnd_1992594 : Nat := 37894758195003044463379

theorem tailTrace_1992594 : CollatzResearch.WordTrace tailWord_1992594 prefixEnd_1992594 37894758195003044463379 := by
  unfold tailWord_1992594
  simp only [CollatzResearch.WordTrace]
  refine ⟨18168968435794930201752209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48450582495453147204672557 18168968435794930201752209)
  ·
    refine ⟨13626726326846197651314157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18168968435794930201752209 13626726326846197651314157)
    ·
      refine ⟨5110022372567324119242809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13626726326846197651314157 5110022372567324119242809)
      ·
        refine ⟨3832516779425493089432107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5110022372567324119242809 3832516779425493089432107)
        ·
          refine ⟨5748775169138239634148161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3832516779425493089432107 5748775169138239634148161)
          ·
            refine ⟨4311581376853679725611121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5748775169138239634148161 4311581376853679725611121)
            ·
              refine ⟨3233686032640259794208341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4311581376853679725611121 3233686032640259794208341)
              ·
                refine ⟨37894758195003044463379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3233686032640259794208341 37894758195003044463379)
                ·
                  rfl

theorem cell23_1992594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 8].length) (baseStart_1992594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992594 prefixEnd_1992594 := by exact prefixLift 1992594
  have htrace : WordTrace (prefixWord ++ tailWord_1992594) baseStart_1992594 baseEnd_1992594 := by
    simpa [prefixWord, tailWord_1992594, baseEnd_1992594] using wordTrace_append hprefix tailTrace_1992594
  have hstable : (prefixWord ++ tailWord_1992594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992594).length < 2 ^ (prefixWord ++ tailWord_1992594).sum := by decide
  have hdescent : baseEnd_1992594 < baseStart_1992594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992622 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1992622 : Nat := 118140960795 + 1992622 * 2 ^ 59
def prefixEnd_1992622 : Nat := 4983230072969 + 3 ^ 40 * 1992622 * 2
def baseEnd_1992622 : Nat := 1023172848723408090961105

theorem tailTrace_1992622 : CollatzResearch.WordTrace tailWord_1992622 prefixEnd_1992622 1023172848723408090961105 := by
  unfold tailWord_1992622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084611873384785198628515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48451263324718854392685413 9084611873384785198628515)
  ·
    refine ⟨13626917810077177797942773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9084611873384785198628515 13626917810077177797942773)
    ·
      refine ⟨1277523544694735418557135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13626917810077177797942773 1277523544694735418557135)
      ·
        refine ⟨1916285317042103127835703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277523544694735418557135 1916285317042103127835703)
        ·
          refine ⟨2874427975563154691753555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916285317042103127835703 2874427975563154691753555)
          ·
            refine ⟨4311641963344732037630333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2874427975563154691753555 4311641963344732037630333)
            ·
              refine ⟨1616865736254274514111375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4311641963344732037630333 1616865736254274514111375)
              ·
                refine ⟨2425298604381411771167063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616865736254274514111375 2425298604381411771167063)
                ·
                  refine ⟨3637947906572117656750595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425298604381411771167063 3637947906572117656750595)
                  ·
                    refine ⟨5456921859858176485125893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3637947906572117656750595 5456921859858176485125893)
                    ·
                      refine ⟨1023172848723408090961105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5456921859858176485125893 1023172848723408090961105)
                      ·
                        rfl

theorem cell23_1992622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1992622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992622 prefixEnd_1992622 := by exact prefixLift 1992622
  have htrace : WordTrace (prefixWord ++ tailWord_1992622) baseStart_1992622 baseEnd_1992622 := by
    simpa [prefixWord, tailWord_1992622, baseEnd_1992622] using wordTrace_append hprefix tailTrace_1992622
  have hstable : (prefixWord ++ tailWord_1992622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992622).length < 2 ^ (prefixWord ++ tailWord_1992622).sum := by decide
  have hdescent : baseEnd_1992622 < baseStart_1992622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992638 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_1992638 : Nat := 118140960795 + 1992638 * 2 ^ 59
def prefixEnd_1992638 : Nat := 4983230072969 + 3 ^ 40 * 1992638 * 2
def baseEnd_1992638 : Nat := 1023181064413880028361031

theorem tailTrace_1992638 : CollatzResearch.WordTrace tailWord_1992638 prefixEnd_1992638 1023181064413880028361031 := by
  unfold tailWord_1992638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084684819377539540201321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48451652370013544214407045 9084684819377539540201321)
  ·
    refine ⟨6813513614533154655150991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9084684819377539540201321 6813513614533154655150991)
    ·
      refine ⟨10220270421799731982726487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6813513614533154655150991 10220270421799731982726487)
      ·
        refine ⟨15330405632699597974089731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10220270421799731982726487 15330405632699597974089731)
        ·
          refine ⟨22995608449049396961134597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15330405632699597974089731 22995608449049396961134597)
          ·
            refine ⟨4311676584196761930212737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22995608449049396961134597 4311676584196761930212737)
            ·
              refine ⟨3233757438147571447659553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4311676584196761930212737 3233757438147571447659553)
              ·
                refine ⟨2425318078610678585744665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3233757438147571447659553 2425318078610678585744665)
                ·
                  refine ⟨1818988558958008939308499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2425318078610678585744665 1818988558958008939308499)
                  ·
                    refine ⟨2728482838437013408962749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1818988558958008939308499 2728482838437013408962749)
                    ·
                      refine ⟨1023181064413880028361031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2728482838437013408962749 1023181064413880028361031)
                      ·
                        rfl

theorem cell23_1992638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_1992638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992638 prefixEnd_1992638 := by exact prefixLift 1992638
  have htrace : WordTrace (prefixWord ++ tailWord_1992638) baseStart_1992638 baseEnd_1992638 := by
    simpa [prefixWord, tailWord_1992638, baseEnd_1992638] using wordTrace_append hprefix tailTrace_1992638
  have hstable : (prefixWord ++ tailWord_1992638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992638).length < 2 ^ (prefixWord ++ tailWord_1992638).sum := by decide
  have hdescent : baseEnd_1992638 < baseStart_1992638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992661 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 1, 4, 2]
def baseStart_1992661 : Nat := 118140960795 + 1992661 * 2 ^ 59
def prefixEnd_1992661 : Nat := 4983230072969 + 3 ^ 40 * 1992661 * 2
def baseEnd_1992661 : Nat := 1023192874468933438373425

theorem tailTrace_1992661 : CollatzResearch.WordTrace tailWord_1992661 prefixEnd_1992661 1023192874468933438373425 := by
  unfold tailWord_1992661
  simp only [CollatzResearch.WordTrace]
  refine ⟨72678317433936991249697837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48452211622624660833131891 72678317433936991249697837)
  ·
    refine ⟨27254369037726371718636689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72678317433936991249697837 27254369037726371718636689)
    ·
      refine ⟨20440776778294778788977517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27254369037726371718636689 20440776778294778788977517)
      ·
        refine ⟨7665291291860542045866569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20440776778294778788977517 7665291291860542045866569)
        ·
          refine ⟨5748968468895406534399927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7665291291860542045866569 5748968468895406534399927)
          ·
            refine ⟨8623452703343109801599891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5748968468895406534399927 8623452703343109801599891)
            ·
              refine ⟨12935179055014664702399837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623452703343109801599891 12935179055014664702399837)
              ·
                refine ⟨4850692145630499263399939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12935179055014664702399837 4850692145630499263399939)
                ·
                  refine ⟨7276038218445748895099909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850692145630499263399939 7276038218445748895099909)
                  ·
                    refine ⟨1364257165958577917831233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7276038218445748895099909 1364257165958577917831233)
                    ·
                      refine ⟨1023192874468933438373425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1364257165958577917831233 1023192874468933438373425)
                      ·
                        rfl

theorem cell23_1992661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_1992661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992661 prefixEnd_1992661 := by exact prefixLift 1992661
  have htrace : WordTrace (prefixWord ++ tailWord_1992661) baseStart_1992661 baseEnd_1992661 := by
    simpa [prefixWord, tailWord_1992661, baseEnd_1992661] using wordTrace_append hprefix tailTrace_1992661
  have hstable : (prefixWord ++ tailWord_1992661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992661).length < 2 ^ (prefixWord ++ tailWord_1992661).sum := by decide
  have hdescent : baseEnd_1992661 < baseStart_1992661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992704 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 2, 5, 2]
def baseStart_1992704 : Nat := 118140960795 + 1992704 * 2 ^ 59
def prefixEnd_1992704 : Nat := 4983230072969 + 3 ^ 40 * 1992704 * 2
def baseEnd_1992704 : Nat := 1023214954137076770135727

theorem tailTrace_1992704 : CollatzResearch.WordTrace tailWord_1992704 prefixEnd_1992704 1023214954137076770135727 := by
  unfold tailWord_1992704
  simp only [CollatzResearch.WordTrace]
  refine ⟨36339942886390604796756583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48453257181854139729008777 36339942886390604796756583)
  ·
    refine ⟨54509914329585907195134875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36339942886390604796756583 54509914329585907195134875)
    ·
      refine ⟨81764871494378860792702313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54509914329585907195134875 81764871494378860792702313)
      ·
        refine ⟨61323653620784145594526735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81764871494378860792702313 61323653620784145594526735)
        ·
          refine ⟨91985480431176218391790103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61323653620784145594526735 91985480431176218391790103)
          ·
            refine ⟨137978220646764327587685155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91985480431176218391790103 137978220646764327587685155)
            ·
              refine ⟨206967330970146491381527733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137978220646764327587685155 206967330970146491381527733)
              ·
                refine ⟨19403187278451233567018225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206967330970146491381527733 19403187278451233567018225)
                ·
                  refine ⟨14552390458838425175263669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19403187278451233567018225 14552390458838425175263669)
                  ·
                    refine ⟨1364286605516102360180969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14552390458838425175263669 1364286605516102360180969)
                    ·
                      refine ⟨1023214954137076770135727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1364286605516102360180969 1023214954137076770135727)
                      ·
                        rfl

theorem cell23_1992704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 5, 2].length) (baseStart_1992704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992704 prefixEnd_1992704 := by exact prefixLift 1992704
  have htrace : WordTrace (prefixWord ++ tailWord_1992704) baseStart_1992704 baseEnd_1992704 := by
    simpa [prefixWord, tailWord_1992704, baseEnd_1992704] using wordTrace_append hprefix tailTrace_1992704
  have hstable : (prefixWord ++ tailWord_1992704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992704).length < 2 ^ (prefixWord ++ tailWord_1992704).sum := by decide
  have hdescent : baseEnd_1992704 < baseStart_1992704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992707 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 5]
def baseStart_1992707 : Nat := 118140960795 + 1992707 * 2 ^ 59
def prefixEnd_1992707 : Nat := 4983230072969 + 3 ^ 40 * 1992707 * 2
def baseEnd_1992707 : Nat := 1023216494579040258398213

theorem tailTrace_1992707 : CollatzResearch.WordTrace tailWord_1992707 prefixEnd_1992707 1023216494579040258398213 := by
  unfold tailWord_1992707
  simp only [CollatzResearch.WordTrace]
  refine ⟨72679995191770341105872375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48453330127846894070581583 72679995191770341105872375)
  ·
    refine ⟨109019992787655511658808563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72679995191770341105872375 109019992787655511658808563)
    ·
      refine ⟨163529989181483267488212845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109019992787655511658808563 163529989181483267488212845)
      ·
        refine ⟨61323745943056225308079817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163529989181483267488212845 61323745943056225308079817)
        ·
          refine ⟨45992809457292168981059863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61323745943056225308079817 45992809457292168981059863)
          ·
            refine ⟨68989214185938253471589795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45992809457292168981059863 68989214185938253471589795)
            ·
              refine ⟨103483821278907380207384693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68989214185938253471589795 103483821278907380207384693)
              ·
                refine ⟨9701608244897566894442315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103483821278907380207384693 9701608244897566894442315)
                ·
                  refine ⟨14552412367346350341663473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9701608244897566894442315 14552412367346350341663473)
                  ·
                    refine ⟨10914309275509762756247605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14552412367346350341663473 10914309275509762756247605)
                    ·
                      refine ⟨1023216494579040258398213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10914309275509762756247605 1023216494579040258398213)
                      ·
                        rfl

theorem cell23_1992707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_1992707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992707 prefixEnd_1992707 := by exact prefixLift 1992707
  have htrace : WordTrace (prefixWord ++ tailWord_1992707) baseStart_1992707 baseEnd_1992707 := by
    simpa [prefixWord, tailWord_1992707, baseEnd_1992707] using wordTrace_append hprefix tailTrace_1992707
  have hstable : (prefixWord ++ tailWord_1992707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992707).length < 2 ^ (prefixWord ++ tailWord_1992707).sum := by decide
  have hdescent : baseEnd_1992707 < baseStart_1992707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992747 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 6]
def baseStart_1992747 : Nat := 118140960795 + 1992747 * 2 ^ 59
def prefixEnd_1992747 : Nat := 4983230072969 + 3 ^ 40 * 1992747 * 2
def baseEnd_1992747 : Nat := 1023237033805220101898029

theorem tailTrace_1992747 : CollatzResearch.WordTrace tailWord_1992747 prefixEnd_1992747 1023237033805220101898029 := by
  unfold tailWord_1992747
  simp only [CollatzResearch.WordTrace]
  refine ⟨72681454111625427937328495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48454302741083618624885663 72681454111625427937328495)
  ·
    refine ⟨109022181167438141905992743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72681454111625427937328495 109022181167438141905992743)
    ·
      refine ⟨163533271751157212858989115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109022181167438141905992743 163533271751157212858989115)
      ·
        refine ⟨245299907626735819288483673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163533271751157212858989115 245299907626735819288483673)
        ·
          refine ⟨183974930720051864466362755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245299907626735819288483673 183974930720051864466362755)
          ·
            refine ⟨275962396080077796699544133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183974930720051864466362755 275962396080077796699544133)
            ·
              refine ⟨51742949265014586881164525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275962396080077796699544133 51742949265014586881164525)
              ·
                refine ⟨19403605974380470080436697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51742949265014586881164525 19403605974380470080436697)
                ·
                  refine ⟨14552704480785352560327523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19403605974380470080436697 14552704480785352560327523)
                  ·
                    refine ⟨21829056721178028840491285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14552704480785352560327523 21829056721178028840491285)
                    ·
                      refine ⟨1023237033805220101898029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21829056721178028840491285 1023237033805220101898029)
                      ·
                        rfl

theorem cell23_1992747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_1992747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992747 prefixEnd_1992747 := by exact prefixLift 1992747
  have htrace : WordTrace (prefixWord ++ tailWord_1992747) baseStart_1992747 baseEnd_1992747 := by
    simpa [prefixWord, tailWord_1992747, baseEnd_1992747] using wordTrace_append hprefix tailTrace_1992747
  have hstable : (prefixWord ++ tailWord_1992747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992747).length < 2 ^ (prefixWord ++ tailWord_1992747).sum := by decide
  have hdescent : baseEnd_1992747 < baseStart_1992747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992841 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 4]
def baseStart_1992841 : Nat := 118140960795 + 1992841 * 2 ^ 59
def prefixEnd_1992841 : Nat := 4983230072969 + 3 ^ 40 * 1992841 * 2
def baseEnd_1992841 : Nat := 1023285300986742734122597

theorem tailTrace_1992841 : CollatzResearch.WordTrace tailWord_1992841 prefixEnd_1992841 1023285300986742734122597 := by
  unfold tailWord_1992841
  simp only [CollatzResearch.WordTrace]
  refine ⟨72684882573284881991250377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48456588382189921327500251 72684882573284881991250377)
  ·
    refine ⟨54513661929963661493437783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72684882573284881991250377 54513661929963661493437783)
    ·
      refine ⟨81770492894945492240156675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54513661929963661493437783 81770492894945492240156675)
      ·
        refine ⟨122655739342418238360235013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81770492894945492240156675 122655739342418238360235013)
        ·
          refine ⟨22997951126703419692544065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122655739342418238360235013 22997951126703419692544065)
          ·
            refine ⟨17248463345027564769408049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22997951126703419692544065 17248463345027564769408049)
            ·
              refine ⟨12936347508770673577056037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17248463345027564769408049 12936347508770673577056037)
              ·
                refine ⟨2425565157894501295698007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12936347508770673577056037 2425565157894501295698007)
                ·
                  refine ⟨3638347736841751943547011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425565157894501295698007 3638347736841751943547011)
                  ·
                    refine ⟨5457521605262627915320517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3638347736841751943547011 5457521605262627915320517)
                    ·
                      refine ⟨1023285300986742734122597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5457521605262627915320517 1023285300986742734122597)
                      ·
                        rfl

theorem cell23_1992841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 4].length) (baseStart_1992841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992841 prefixEnd_1992841 := by exact prefixLift 1992841
  have htrace : WordTrace (prefixWord ++ tailWord_1992841) baseStart_1992841 baseEnd_1992841 := by
    simpa [prefixWord, tailWord_1992841, baseEnd_1992841] using wordTrace_append hprefix tailTrace_1992841
  have hstable : (prefixWord ++ tailWord_1992841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992841).length < 2 ^ (prefixWord ++ tailWord_1992841).sum := by decide
  have hdescent : baseEnd_1992841 < baseStart_1992841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992855 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 1, 5]
def baseStart_1992855 : Nat := 118140960795 + 1992855 * 2 ^ 59
def prefixEnd_1992855 : Nat := 4983230072969 + 3 ^ 40 * 1992855 * 2
def baseEnd_1992855 : Nat := 341097496571968559782511

theorem tailTrace_1992855 : CollatzResearch.WordTrace tailWord_1992855 prefixEnd_1992855 341097496571968559782511 := by
  unfold tailWord_1992855
  simp only [CollatzResearch.WordTrace]
  refine ⟨72685393195234162382260019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48456928796822774921506679 72685393195234162382260019)
  ·
    refine ⟨109028089792851243573390029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72685393195234162382260019 109028089792851243573390029)
    ·
      refine ⟨40885533672319216340021261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109028089792851243573390029 40885533672319216340021261)
      ·
        refine ⟨15332075127119706127507973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40885533672319216340021261 15332075127119706127507973)
        ·
          refine ⟨2874764086334944898907745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15332075127119706127507973 2874764086334944898907745)
          ·
            refine ⟨2156073064751208674180809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2874764086334944898907745 2156073064751208674180809)
            ·
              refine ⟨1617054798563406505635607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156073064751208674180809 1617054798563406505635607)
              ·
                refine ⟨2425582197845109758453411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617054798563406505635607 2425582197845109758453411)
                ·
                  refine ⟨3638373296767664637680117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425582197845109758453411 3638373296767664637680117)
                  ·
                    refine ⟨341097496571968559782511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3638373296767664637680117 341097496571968559782511)
                    ·
                      rfl

theorem cell23_1992855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_1992855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992855 prefixEnd_1992855 := by exact prefixLift 1992855
  have htrace : WordTrace (prefixWord ++ tailWord_1992855) baseStart_1992855 baseEnd_1992855 := by
    simpa [prefixWord, tailWord_1992855, baseEnd_1992855] using wordTrace_append hprefix tailTrace_1992855
  have hstable : (prefixWord ++ tailWord_1992855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992855).length < 2 ^ (prefixWord ++ tailWord_1992855).sum := by decide
  have hdescent : baseEnd_1992855 < baseStart_1992855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992864 : List Nat := [2, 1, 1, 4, 2, 3, 10]
def baseStart_1992864 : Nat := 118140960795 + 1992864 * 2 ^ 59
def prefixEnd_1992864 : Nat := 4983230072969 + 3 ^ 40 * 1992864 * 2
def baseEnd_1992864 : Nat := 12633297667182668446111

theorem tailTrace_1992864 : CollatzResearch.WordTrace tailWord_1992864 prefixEnd_1992864 12633297667182668446111 := by
  unfold tailWord_1992864
  simp only [CollatzResearch.WordTrace]
  refine ⟨36342860726100778459668823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48457147634801037946225097 36342860726100778459668823)
  ·
    refine ⟨54514291089151167689503235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36342860726100778459668823 54514291089151167689503235)
    ·
      refine ⟨81771436633726751534254853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54514291089151167689503235 81771436633726751534254853)
      ·
        refine ⟨15332144368823765912672785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81771436633726751534254853 15332144368823765912672785)
        ·
          refine ⟨11499108276617824434504589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15332144368823765912672785 11499108276617824434504589)
          ·
            refine ⟨4312165603731684162939221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11499108276617824434504589 4312165603731684162939221)
            ·
              refine ⟨12633297667182668446111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4312165603731684162939221 12633297667182668446111)
              ·
                rfl

theorem cell23_1992864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 10].length) (baseStart_1992864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992864 prefixEnd_1992864 := by exact prefixLift 1992864
  have htrace : WordTrace (prefixWord ++ tailWord_1992864) baseStart_1992864 baseEnd_1992864 := by
    simpa [prefixWord, tailWord_1992864, baseEnd_1992864] using wordTrace_append hprefix tailTrace_1992864
  have hstable : (prefixWord ++ tailWord_1992864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992864).length < 2 ^ (prefixWord ++ tailWord_1992864).sum := by decide
  have hdescent : baseEnd_1992864 < baseStart_1992864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992868 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_1992868 : Nat := 118140960795 + 1992868 * 2 ^ 59
def prefixEnd_1992868 : Nat := 4983230072969 + 3 ^ 40 * 1992868 * 2
def baseEnd_1992868 : Nat := 341099721654804709494991

theorem tailTrace_1992868 : CollatzResearch.WordTrace tailWord_1992868 prefixEnd_1992868 341099721654804709494991 := by
  unfold tailWord_1992868
  simp only [CollatzResearch.WordTrace]
  refine ⟨36342933672093532801241629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48457244896124710401655505 36342933672093532801241629)
  ·
    refine ⟨13628600127035074800465611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36342933672093532801241629 13628600127035074800465611)
    ·
      refine ⟨20442900190552612200698417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13628600127035074800465611 20442900190552612200698417)
      ·
        refine ⟨15332175142914459150523813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20442900190552612200698417 15332175142914459150523813)
        ·
          refine ⟨2874782839296461090723215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15332175142914459150523813 2874782839296461090723215)
          ·
            refine ⟨4312174258944691636084823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2874782839296461090723215 4312174258944691636084823)
            ·
              refine ⟨6468261388417037454127235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312174258944691636084823 6468261388417037454127235)
              ·
                refine ⟨9702392082625556181190853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6468261388417037454127235 9702392082625556181190853)
                ·
                  refine ⟨1819198515492291783973285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9702392082625556181190853 1819198515492291783973285)
                  ·
                    refine ⟨341099721654804709494991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1819198515492291783973285 341099721654804709494991)
                    ·
                      rfl

theorem cell23_1992868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_1992868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992868 prefixEnd_1992868 := by exact prefixLift 1992868
  have htrace : WordTrace (prefixWord ++ tailWord_1992868) baseStart_1992868 baseEnd_1992868 := by
    simpa [prefixWord, tailWord_1992868, baseEnd_1992868] using wordTrace_append hprefix tailTrace_1992868
  have hstable : (prefixWord ++ tailWord_1992868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992868).length < 2 ^ (prefixWord ++ tailWord_1992868).sum := by decide
  have hdescent : baseEnd_1992868 < baseStart_1992868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992885 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 1, 6]
def baseStart_1992885 : Nat := 118140960795 + 1992885 * 2 ^ 59
def prefixEnd_1992885 : Nat := 4983230072969 + 3 ^ 40 * 1992885 * 2
def baseEnd_1992885 : Nat := 341102631378513520657465

theorem tailTrace_1992885 : CollatzResearch.WordTrace tailWord_1992885 prefixEnd_1992885 341102631378513520657465 := by
  unfold tailWord_1992885
  simp only [CollatzResearch.WordTrace]
  refine ⟨72686487385125477505852109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48457658256750318337234739 72686487385125477505852109)
  ·
    refine ⟨27257432769422054064694541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72686487385125477505852109 27257432769422054064694541)
    ·
      refine ⟨10221537288533270274260453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27257432769422054064694541 10221537288533270274260453)
      ·
        refine ⟨1916538241599988176423835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10221537288533270274260453 1916538241599988176423835)
        ·
          refine ⟨2874807362399982264635753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916538241599988176423835 2874807362399982264635753)
          ·
            refine ⟨2156105521799986698476815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2874807362399982264635753 2156105521799986698476815)
            ·
              refine ⟨3234158282699980047715223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2156105521799986698476815 3234158282699980047715223)
              ·
                refine ⟨4851237424049970071572835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234158282699980047715223 4851237424049970071572835)
                ·
                  refine ⟨7276856136074955107359253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4851237424049970071572835 7276856136074955107359253)
                  ·
                    refine ⟨341102631378513520657465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7276856136074955107359253 341102631378513520657465)
                    ·
                      rfl

theorem cell23_1992885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_1992885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992885 prefixEnd_1992885 := by exact prefixLift 1992885
  have htrace : WordTrace (prefixWord ++ tailWord_1992885) baseStart_1992885 baseEnd_1992885 := by
    simpa [prefixWord, tailWord_1992885, baseEnd_1992885] using wordTrace_append hprefix tailTrace_1992885
  have hstable : (prefixWord ++ tailWord_1992885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992885).length < 2 ^ (prefixWord ++ tailWord_1992885).sum := by decide
  have hdescent : baseEnd_1992885 < baseStart_1992885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
