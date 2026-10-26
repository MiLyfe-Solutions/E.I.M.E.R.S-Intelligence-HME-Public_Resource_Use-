import V185TrunkScan23Chunk0025

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_153796 : List Nat := [2, 3, 3, 1, 2, 3, 9]
def baseStart_153796 : Nat := 118140960795 + 153796 * 2 ^ 59
def prefixEnd_153796 : Nat := 4983230072969 + 3 ^ 40 * 153796 * 2
def baseEnd_153796 : Nat := 974953959740561804231

theorem tailTrace_153796 : CollatzResearch.WordTrace tailWord_153796 prefixEnd_153796 974953959740561804231 := by
  unfold tailWord_153796
  simp only [CollatzResearch.WordTrace]
  refine ⟨2804700475415416555372621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3739600633887222073830161 2804700475415416555372621)
  ·
    refine ⟨1051762678280781208264733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2804700475415416555372621 1051762678280781208264733)
    ·
      refine ⟨394411004355292953099275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1051762678280781208264733 394411004355292953099275)
      ·
        refine ⟨591616506532939429648913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394411004355292953099275 591616506532939429648913)
        ·
          refine ⟨443712379899704572236685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591616506532939429648913 443712379899704572236685)
          ·
            refine ⟨166392142462389214588757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 443712379899704572236685 166392142462389214588757)
            ·
              refine ⟨974953959740561804231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 166392142462389214588757 974953959740561804231)
              ·
                rfl

theorem cell23_153796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 9].length) (baseStart_153796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153796 prefixEnd_153796 := by exact prefixLift 153796
  have htrace : WordTrace (prefixWord ++ tailWord_153796) baseStart_153796 baseEnd_153796 := by
    simpa [prefixWord, tailWord_153796, baseEnd_153796] using wordTrace_append hprefix tailTrace_153796
  have hstable : (prefixWord ++ tailWord_153796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153796).length < 2 ^ (prefixWord ++ tailWord_153796).sum := by decide
  have hdescent : baseEnd_153796 < baseStart_153796 := by decide
  rcases family_descends (prefixWord ++ tailWord_153796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153807 : List Nat := [1, 1, 2, 1, 1, 3, 7, 2, 1, 2, 2]
def baseStart_153807 : Nat := 118140960795 + 153807 * 2 ^ 59
def prefixEnd_153807 : Nat := 4983230072969 + 3 ^ 40 * 153807 * 2
def baseEnd_153807 : Nat := 78976919026184963105161

theorem tailTrace_153807 : CollatzResearch.WordTrace tailWord_153807 prefixEnd_153807 78976919026184963105161 := by
  unfold tailWord_153807
  simp only [CollatzResearch.WordTrace]
  refine ⟨5609802153790981989395675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3739868102527321326263783 5609802153790981989395675)
  ·
    refine ⟨8414703230686472984093513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5609802153790981989395675 8414703230686472984093513)
    ·
      refine ⟨6311027423014854738070135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8414703230686472984093513 6311027423014854738070135)
      ·
        refine ⟨9466541134522282107105203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6311027423014854738070135 9466541134522282107105203)
        ·
          refine ⟨14199811701783423160657805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9466541134522282107105203 14199811701783423160657805)
          ·
            refine ⟨5324929388168783685246677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14199811701783423160657805 5324929388168783685246677)
            ·
              refine ⟨124803032535205867622969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5324929388168783685246677 124803032535205867622969)
              ·
                refine ⟨93602274401404400717227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124803032535205867622969 93602274401404400717227)
                ·
                  refine ⟨140403411602106601075841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93602274401404400717227 140403411602106601075841)
                  ·
                    refine ⟨105302558701579950806881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 140403411602106601075841 105302558701579950806881)
                    ·
                      refine ⟨78976919026184963105161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 105302558701579950806881 78976919026184963105161)
                      ·
                        rfl

theorem cell23_153807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 1, 2, 2].length) (baseStart_153807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153807 prefixEnd_153807 := by exact prefixLift 153807
  have htrace : WordTrace (prefixWord ++ tailWord_153807) baseStart_153807 baseEnd_153807 := by
    simpa [prefixWord, tailWord_153807, baseEnd_153807] using wordTrace_append hprefix tailTrace_153807
  have hstable : (prefixWord ++ tailWord_153807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153807).length < 2 ^ (prefixWord ++ tailWord_153807).sum := by decide
  have hdescent : baseEnd_153807 < baseStart_153807 := by decide
  rcases family_descends (prefixWord ++ tailWord_153807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153827 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 1, 2, 3]
def baseStart_153827 : Nat := 118140960795 + 153827 * 2 ^ 59
def prefixEnd_153827 : Nat := 4983230072969 + 3 ^ 40 * 153827 * 2
def baseEnd_153827 : Nat := 78987188639274884855069

theorem tailTrace_153827 : CollatzResearch.WordTrace tailWord_153827 prefixEnd_153827 78987188639274884855069 := by
  unfold tailWord_153827
  simp only [CollatzResearch.WordTrace]
  refine ⟨5610531613718525405123735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3740354409145683603415823 5610531613718525405123735)
  ·
    refine ⟨8415797420577788107685603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5610531613718525405123735 8415797420577788107685603)
    ·
      refine ⟨12623696130866682161528405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8415797420577788107685603 12623696130866682161528405)
      ·
        refine ⟨147933939033593931580411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 12623696130866682161528405 147933939033593931580411)
        ·
          refine ⟨221900908550390897370617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147933939033593931580411 221900908550390897370617)
          ·
            refine ⟨166425681412793173027963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221900908550390897370617 166425681412793173027963)
            ·
              refine ⟨249638522119189759541945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166425681412793173027963 249638522119189759541945)
              ·
                refine ⟨187228891589392319656459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249638522119189759541945 187228891589392319656459)
                ·
                  refine ⟨280843337384088479484689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187228891589392319656459 280843337384088479484689)
                  ·
                    refine ⟨210632503038066359613517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 280843337384088479484689 210632503038066359613517)
                    ·
                      refine ⟨78987188639274884855069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 210632503038066359613517 78987188639274884855069)
                      ·
                        rfl

theorem cell23_153827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_153827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153827 prefixEnd_153827 := by exact prefixLift 153827
  have htrace : WordTrace (prefixWord ++ tailWord_153827) baseStart_153827 baseEnd_153827 := by
    simpa [prefixWord, tailWord_153827, baseEnd_153827] using wordTrace_append hprefix tailTrace_153827
  have hstable : (prefixWord ++ tailWord_153827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153827).length < 2 ^ (prefixWord ++ tailWord_153827).sum := by decide
  have hdescent : baseEnd_153827 < baseStart_153827 := by decide
  rcases family_descends (prefixWord ++ tailWord_153827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153849 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_153849 : Nat := 118140960795 + 153849 * 2 ^ 59
def prefixEnd_153849 : Nat := 4983230072969 + 3 ^ 40 * 153849 * 2
def baseEnd_153849 : Nat := 78998485213673798779967

theorem tailTrace_153849 : CollatzResearch.WordTrace tailWord_153849 prefixEnd_153849 78998485213673798779967 := by
  unfold tailWord_153849
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611334019638823162424601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3740889346425882108283067 5611334019638823162424601)
  ·
    refine ⟨4208500514729117371818451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5611334019638823162424601 4208500514729117371818451)
    ·
      refine ⟨6312750772093676057727677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208500514729117371818451 6312750772093676057727677)
      ·
        refine ⟨2367281539535128521647879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6312750772093676057727677 2367281539535128521647879)
        ·
          refine ⟨3550922309302692782471819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367281539535128521647879 3550922309302692782471819)
          ·
            refine ⟨5326383463954039173707729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3550922309302692782471819 5326383463954039173707729)
            ·
              refine ⟨3994787597965529380280797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5326383463954039173707729 3994787597965529380280797)
              ·
                refine ⟨1498045349237073517605299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3994787597965529380280797 1498045349237073517605299)
                ·
                  refine ⟨2247068023855610276407949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498045349237073517605299 2247068023855610276407949)
                  ·
                    refine ⟨842650508945853853652981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2247068023855610276407949 842650508945853853652981)
                    ·
                      refine ⟨78998485213673798779967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 842650508945853853652981 78998485213673798779967)
                      ·
                        rfl

theorem cell23_153849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_153849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153849 prefixEnd_153849 := by exact prefixLift 153849
  have htrace : WordTrace (prefixWord ++ tailWord_153849) baseStart_153849 baseEnd_153849 := by
    simpa [prefixWord, tailWord_153849, baseEnd_153849] using wordTrace_append hprefix tailTrace_153849
  have hstable : (prefixWord ++ tailWord_153849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153849).length < 2 ^ (prefixWord ++ tailWord_153849).sum := by decide
  have hdescent : baseEnd_153849 < baseStart_153849 := by decide
  rcases family_descends (prefixWord ++ tailWord_153849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153866 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_153866 : Nat := 118140960795 + 153866 * 2 ^ 59
def prefixEnd_153866 : Nat := 4983230072969 + 3 ^ 40 * 153866 * 2
def baseEnd_153866 : Nat := 79007214384800232267389

theorem tailTrace_153866 : CollatzResearch.WordTrace tailWord_153866 prefixEnd_153866 79007214384800232267389 := by
  unfold tailWord_153866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402988515144308766448363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3741302707051490043862301 1402988515144308766448363)
  ·
    refine ⟨2104482772716463149672545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1402988515144308766448363 2104482772716463149672545)
    ·
      refine ⟨1578362079537347362254409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2104482772716463149672545 1578362079537347362254409)
      ·
        refine ⟨1183771559653010521690807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1578362079537347362254409 1183771559653010521690807)
        ·
          refine ⟨1775657339479515782536211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183771559653010521690807 1775657339479515782536211)
          ·
            refine ⟨2663486009219273673804317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775657339479515782536211 2663486009219273673804317)
            ·
              refine ⟨998807253457227627676619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2663486009219273673804317 998807253457227627676619)
              ·
                refine ⟨1498210880185841441514929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998807253457227627676619 1498210880185841441514929)
                ·
                  refine ⟨1123658160139381081136197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1498210880185841441514929 1123658160139381081136197)
                  ·
                    refine ⟨210685905026133952713037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1123658160139381081136197 210685905026133952713037)
                    ·
                      refine ⟨79007214384800232267389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 210685905026133952713037 79007214384800232267389)
                      ·
                        rfl

theorem cell23_153866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_153866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153866 prefixEnd_153866 := by exact prefixLift 153866
  have htrace : WordTrace (prefixWord ++ tailWord_153866) baseStart_153866 baseEnd_153866 := by
    simpa [prefixWord, tailWord_153866, baseEnd_153866] using wordTrace_append hprefix tailTrace_153866
  have hstable : (prefixWord ++ tailWord_153866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153866).length < 2 ^ (prefixWord ++ tailWord_153866).sum := by decide
  have hdescent : baseEnd_153866 < baseStart_153866 := by decide
  rcases family_descends (prefixWord ++ tailWord_153866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153880 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 2, 2, 2]
def baseStart_153880 : Nat := 118140960795 + 153880 * 2 ^ 59
def prefixEnd_153880 : Nat := 4983230072969 + 3 ^ 40 * 153880 * 2
def baseEnd_153880 : Nat := 79014403113963177492325

theorem tailTrace_153880 : CollatzResearch.WordTrace tailWord_153880 prefixEnd_153880 79014403113963177492325 := by
  unfold tailWord_153880
  simp only [CollatzResearch.WordTrace]
  refine ⟨2806232341263257728401547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3741643121684343637868729 2806232341263257728401547)
  ·
    refine ⟨4209348511894886592602321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2806232341263257728401547 4209348511894886592602321)
    ·
      refine ⟨3157011383921164944451741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4209348511894886592602321 3157011383921164944451741)
      ·
        refine ⟨1183879268970436854169403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3157011383921164944451741 1183879268970436854169403)
        ·
          refine ⟨1775818903455655281254105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183879268970436854169403 1775818903455655281254105)
          ·
            refine ⟨1331864177591741460940579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1775818903455655281254105 1331864177591741460940579)
            ·
              refine ⟨1997796266387612191410869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331864177591741460940579 1997796266387612191410869)
              ·
                refine ⟨187293399973838642944769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1997796266387612191410869 187293399973838642944769)
                ·
                  refine ⟨140470049980378982208577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187293399973838642944769 140470049980378982208577)
                  ·
                    refine ⟨105352537485284236656433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 140470049980378982208577 105352537485284236656433)
                    ·
                      refine ⟨79014403113963177492325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 105352537485284236656433 79014403113963177492325)
                      ·
                        rfl

theorem cell23_153880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_153880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153880 prefixEnd_153880 := by exact prefixLift 153880
  have htrace : WordTrace (prefixWord ++ tailWord_153880) baseStart_153880 baseEnd_153880 := by
    simpa [prefixWord, tailWord_153880, baseEnd_153880] using wordTrace_append hprefix tailTrace_153880
  have hstable : (prefixWord ++ tailWord_153880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153880).length < 2 ^ (prefixWord ++ tailWord_153880).sum := by decide
  have hdescent : baseEnd_153880 < baseStart_153880 := by decide
  rcases family_descends (prefixWord ++ tailWord_153880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153901 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_153901 : Nat := 118140960795 + 153901 * 2 ^ 59
def prefixEnd_153901 : Nat := 4983230072969 + 3 ^ 40 * 153901 * 2
def baseEnd_153901 : Nat := 79025186207707595329729

theorem tailTrace_153901 : CollatzResearch.WordTrace tailWord_153901 prefixEnd_153901 79025186207707595329729 := by
  unfold tailWord_153901
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613230615450436043317557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3742153743633624028878371 5613230615450436043317557)
  ·
    refine ⟨526240370198478379061021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5613230615450436043317557 526240370198478379061021)
    ·
      refine ⟨197340138824429392147883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 526240370198478379061021 197340138824429392147883)
      ·
        refine ⟨296010208236644088221825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197340138824429392147883 296010208236644088221825)
        ·
          refine ⟨222007656177483066166369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296010208236644088221825 222007656177483066166369)
          ·
            refine ⟨166505742133112299624777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222007656177483066166369 166505742133112299624777)
            ·
              refine ⟨124879306599834224718583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166505742133112299624777 124879306599834224718583)
              ·
                refine ⟨187318959899751337077875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124879306599834224718583 187318959899751337077875)
                ·
                  refine ⟨280978439849627005616813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187318959899751337077875 280978439849627005616813)
                  ·
                    refine ⟨105366914943610127106305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280978439849627005616813 105366914943610127106305)
                    ·
                      refine ⟨79025186207707595329729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 105366914943610127106305 79025186207707595329729)
                      ·
                        rfl

theorem cell23_153901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_153901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153901 prefixEnd_153901 := by exact prefixLift 153901
  have htrace : WordTrace (prefixWord ++ tailWord_153901) baseStart_153901 baseEnd_153901 := by
    simpa [prefixWord, tailWord_153901, baseEnd_153901] using wordTrace_append hprefix tailTrace_153901
  have hstable : (prefixWord ++ tailWord_153901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153901).length < 2 ^ (prefixWord ++ tailWord_153901).sum := by decide
  have hdescent : baseEnd_153901 < baseStart_153901 := by decide
  rcases family_descends (prefixWord ++ tailWord_153901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153913 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 2, 3, 3]
def baseStart_153913 : Nat := 118140960795 + 153913 * 2 ^ 59
def prefixEnd_153913 : Nat := 4983230072969 + 3 ^ 40 * 153913 * 2
def baseEnd_153913 : Nat := 79031347975561548379673

theorem tailTrace_153913 : CollatzResearch.WordTrace tailWord_153913 prefixEnd_153913 79031347975561548379673 := by
  unfold tailWord_153913
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613668291406962092754393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3742445527604641395169595 5613668291406962092754393)
  ·
    refine ⟨4210251218555221569565795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5613668291406962092754393 4210251218555221569565795)
    ·
      refine ⟨6315376827832832354348693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4210251218555221569565795 6315376827832832354348693)
      ·
        refine ⟨296033288804664016610095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6315376827832832354348693 296033288804664016610095)
        ·
          refine ⟨444049933206996024915143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296033288804664016610095 444049933206996024915143)
          ·
            refine ⟨666074899810494037372715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444049933206996024915143 666074899810494037372715)
            ·
              refine ⟨999112349715741056059073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666074899810494037372715 999112349715741056059073)
              ·
                refine ⟨749334262286805792044305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 999112349715741056059073 749334262286805792044305)
                ·
                  refine ⟨562000696715104344033229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 749334262286805792044305 562000696715104344033229)
                  ·
                    refine ⟨210750261268164129012461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 562000696715104344033229 210750261268164129012461)
                    ·
                      refine ⟨79031347975561548379673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 210750261268164129012461 79031347975561548379673)
                      ·
                        rfl

theorem cell23_153913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_153913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153913 prefixEnd_153913 := by exact prefixLift 153913
  have htrace : WordTrace (prefixWord ++ tailWord_153913) baseStart_153913 baseEnd_153913 := by
    simpa [prefixWord, tailWord_153913, baseEnd_153913] using wordTrace_append hprefix tailTrace_153913
  have hstable : (prefixWord ++ tailWord_153913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153913).length < 2 ^ (prefixWord ++ tailWord_153913).sum := by decide
  have hdescent : baseEnd_153913 < baseStart_153913 := by decide
  rcases family_descends (prefixWord ++ tailWord_153913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153916 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_153916 : Nat := 118140960795 + 153916 * 2 ^ 59
def prefixEnd_153916 : Nat := 4983230072969 + 3 ^ 40 * 153916 * 2
def baseEnd_153916 : Nat := 26344296139175012214053

theorem tailTrace_153916 : CollatzResearch.WordTrace tailWord_153916 prefixEnd_153916 26344296139175012214053 := by
  unfold tailWord_153916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2806888855198046802556801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3742518473597395736742401 2806888855198046802556801)
  ·
    refine ⟨2105166641398535101917601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2806888855198046802556801 2105166641398535101917601)
    ·
      refine ⟨1578874981048901326438201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2105166641398535101917601 1578874981048901326438201)
      ·
        refine ⟨1184156235786675994828651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1578874981048901326438201 1184156235786675994828651)
        ·
          refine ⟨1776234353680013992242977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184156235786675994828651 1776234353680013992242977)
          ·
            refine ⟨1332175765260010494182233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1776234353680013992242977 1332175765260010494182233)
            ·
              refine ⟨999131823945007870636675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332175765260010494182233 999131823945007870636675)
              ·
                refine ⟨1498697735917511805955013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999131823945007870636675 1498697735917511805955013)
                ·
                  refine ⟨281005825484533463616565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498697735917511805955013 281005825484533463616565)
                  ·
                    refine ⟨26344296139175012214053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 281005825484533463616565 26344296139175012214053)
                    ·
                      rfl

theorem cell23_153916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_153916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153916 prefixEnd_153916 := by exact prefixLift 153916
  have htrace : WordTrace (prefixWord ++ tailWord_153916) baseStart_153916 baseEnd_153916 := by
    simpa [prefixWord, tailWord_153916, baseEnd_153916] using wordTrace_append hprefix tailTrace_153916
  have hstable : (prefixWord ++ tailWord_153916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153916).length < 2 ^ (prefixWord ++ tailWord_153916).sum := by decide
  have hdescent : baseEnd_153916 < baseStart_153916 := by decide
  rcases family_descends (prefixWord ++ tailWord_153916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153936 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 4]
def baseStart_153936 : Nat := 118140960795 + 153936 * 2 ^ 59
def prefixEnd_153936 : Nat := 4983230072969 + 3 ^ 40 * 153936 * 2
def baseEnd_153936 : Nat := 79043158030614958392067

theorem tailTrace_153936 : CollatzResearch.WordTrace tailWord_153936 prefixEnd_153936 79043158030614958392067 := by
  unfold tailWord_153936
  simp only [CollatzResearch.WordTrace]
  refine ⟨2807253585161818510420831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3743004780215758013894441 2807253585161818510420831)
  ·
    refine ⟨4210880377742727765631247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2807253585161818510420831 4210880377742727765631247)
    ·
      refine ⟨6316320566614091648446871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4210880377742727765631247 6316320566614091648446871)
      ·
        refine ⟨9474480849921137472670307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6316320566614091648446871 9474480849921137472670307)
        ·
          refine ⟨14211721274881706209005461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9474480849921137472670307 14211721274881706209005461)
          ·
            refine ⟨666174434760079978547131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14211721274881706209005461 666174434760079978547131)
            ·
              refine ⟨999261652140119967820697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666174434760079978547131 999261652140119967820697)
              ·
                refine ⟨749446239105089975865523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 999261652140119967820697 749446239105089975865523)
                ·
                  refine ⟨1124169358657634963798285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749446239105089975865523 1124169358657634963798285)
                  ·
                    refine ⟨421563509496613111424357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1124169358657634963798285 421563509496613111424357)
                    ·
                      refine ⟨79043158030614958392067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 421563509496613111424357 79043158030614958392067)
                      ·
                        rfl

theorem cell23_153936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_153936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153936 prefixEnd_153936 := by exact prefixLift 153936
  have htrace : WordTrace (prefixWord ++ tailWord_153936) baseStart_153936 baseEnd_153936 := by
    simpa [prefixWord, tailWord_153936, baseEnd_153936] using wordTrace_append hprefix tailTrace_153936
  have hstable : (prefixWord ++ tailWord_153936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153936).length < 2 ^ (prefixWord ++ tailWord_153936).sum := by decide
  have hdescent : baseEnd_153936 < baseStart_153936 := by decide
  rcases family_descends (prefixWord ++ tailWord_153936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153993 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 6]
def baseStart_153993 : Nat := 118140960795 + 153993 * 2 ^ 59
def prefixEnd_153993 : Nat := 4983230072969 + 3 ^ 40 * 153993 * 2
def baseEnd_153993 : Nat := 8785825158657915042145

theorem tailTrace_153993 : CollatzResearch.WordTrace tailWord_153993 prefixEnd_153993 8785825158657915042145 := by
  unfold tailWord_153993
  simp only [CollatzResearch.WordTrace]
  refine ⟨5616586131117135755666633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3744390754078090503777755 5616586131117135755666633)
  ·
    refine ⟨4212439598337851816749975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5616586131117135755666633 4212439598337851816749975)
    ·
      refine ⟨6318659397506777725124963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4212439598337851816749975 6318659397506777725124963)
      ·
        refine ⟨9477989096260166587687445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6318659397506777725124963 9477989096260166587687445)
        ·
          refine ⟨444280738887195308797849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9477989096260166587687445 444280738887195308797849)
          ·
            refine ⟨333210554165396481598387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444280738887195308797849 333210554165396481598387)
            ·
              refine ⟨499815831248094722397581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333210554165396481598387 499815831248094722397581)
              ·
                refine ⟨187430936718035520899093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 499815831248094722397581 187430936718035520899093)
                ·
                  refine ⟨8785825158657915042145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 187430936718035520899093 8785825158657915042145)
                  ·
                    rfl

theorem cell23_153993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 6].length) (baseStart_153993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153993 prefixEnd_153993 := by exact prefixLift 153993
  have htrace : WordTrace (prefixWord ++ tailWord_153993) baseStart_153993 baseEnd_153993 := by
    simpa [prefixWord, tailWord_153993, baseEnd_153993] using wordTrace_append hprefix tailTrace_153993
  have hstable : (prefixWord ++ tailWord_153993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153993).length < 2 ^ (prefixWord ++ tailWord_153993).sum := by decide
  have hdescent : baseEnd_153993 < baseStart_153993 := by decide
  rcases family_descends (prefixWord ++ tailWord_153993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154070 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_154070 : Nat := 118140960795 + 154070 * 2 ^ 59
def prefixEnd_154070 : Nat := 4983230072969 + 3 ^ 40 * 154070 * 2
def baseEnd_154070 : Nat := 26370654812772478038817

theorem tailTrace_154070 : CollatzResearch.WordTrace tailWord_154070 prefixEnd_154070 26370654812772478038817 := by
  unfold tailWord_154070
  simp only [CollatzResearch.WordTrace]
  refine ⟨351212159489886119138729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3746263034558785270813109 351212159489886119138729)
  ·
    refine ⟨263409119617414589354047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 351212159489886119138729 263409119617414589354047)
    ·
      refine ⟨395113679426121884031071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263409119617414589354047 395113679426121884031071)
      ·
        refine ⟨592670519139182826046607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395113679426121884031071 592670519139182826046607)
        ·
          refine ⟨889005778708774239069911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592670519139182826046607 889005778708774239069911)
          ·
            refine ⟨1333508668063161358604867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889005778708774239069911 1333508668063161358604867)
            ·
              refine ⟨2000263002094742037907301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333508668063161358604867 2000263002094742037907301)
              ·
                refine ⟨375049312892764132107619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2000263002094742037907301 375049312892764132107619)
                ·
                  refine ⟨562573969339146198161429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375049312892764132107619 562573969339146198161429)
                  ·
                    refine ⟨26370654812772478038817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 562573969339146198161429 26370654812772478038817)
                    ·
                      rfl

theorem cell23_154070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_154070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154070 prefixEnd_154070 := by exact prefixLift 154070
  have htrace : WordTrace (prefixWord ++ tailWord_154070) baseStart_154070 baseEnd_154070 := by
    simpa [prefixWord, tailWord_154070, baseEnd_154070] using wordTrace_append hprefix tailTrace_154070
  have hstable : (prefixWord ++ tailWord_154070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154070).length < 2 ^ (prefixWord ++ tailWord_154070).sum := by decide
  have hdescent : baseEnd_154070 < baseStart_154070 := by decide
  rcases family_descends (prefixWord ++ tailWord_154070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154073 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 4]
def baseStart_154073 : Nat := 118140960795 + 154073 * 2 ^ 59
def prefixEnd_154073 : Nat := 4983230072969 + 3 ^ 40 * 154073 * 2
def baseEnd_154073 : Nat := 79113504880280922378937

theorem tailTrace_154073 : CollatzResearch.WordTrace tailWord_154073 prefixEnd_154073 79113504880280922378937 := by
  unfold tailWord_154073
  simp only [CollatzResearch.WordTrace]
  refine ⟨5619503970827309418578873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3746335980551539612385915 5619503970827309418578873)
  ·
    refine ⟨4214627978120482063934155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5619503970827309418578873 4214627978120482063934155)
    ·
      refine ⟨6321941967180723095901233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4214627978120482063934155 6321941967180723095901233)
      ·
        refine ⟨4741456475385542321925925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6321941967180723095901233 4741456475385542321925925)
        ·
          refine ⟨889023089134789185361111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4741456475385542321925925 889023089134789185361111)
          ·
            refine ⟨1333534633702183778041667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889023089134789185361111 1333534633702183778041667)
            ·
              refine ⟨2000301950553275667062501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333534633702183778041667 2000301950553275667062501)
              ·
                refine ⟨375056615728739187574219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2000301950553275667062501 375056615728739187574219)
                ·
                  refine ⟨562584923593108781361329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375056615728739187574219 562584923593108781361329)
                  ·
                    refine ⟨421938692694831586020997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 562584923593108781361329 421938692694831586020997)
                    ·
                      refine ⟨79113504880280922378937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 421938692694831586020997 79113504880280922378937)
                      ·
                        rfl

theorem cell23_154073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_154073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154073 prefixEnd_154073 := by exact prefixLift 154073
  have htrace : WordTrace (prefixWord ++ tailWord_154073) baseStart_154073 baseEnd_154073 := by
    simpa [prefixWord, tailWord_154073, baseEnd_154073] using wordTrace_append hprefix tailTrace_154073
  have hstable : (prefixWord ++ tailWord_154073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154073).length < 2 ^ (prefixWord ++ tailWord_154073).sum := by decide
  have hdescent : baseEnd_154073 < baseStart_154073 := by decide
  rcases family_descends (prefixWord ++ tailWord_154073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154077 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_154077 : Nat := 118140960795 + 154077 * 2 ^ 59
def prefixEnd_154077 : Nat := 4983230072969 + 3 ^ 40 * 154077 * 2
def baseEnd_154077 : Nat := 79115558802898906728919

theorem tailTrace_154077 : CollatzResearch.WordTrace tailWord_154077 prefixEnd_154077 79115558802898906728919 := by
  unfold tailWord_154077
  simp only [CollatzResearch.WordTrace]
  refine ⟨5619649862812818101724485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3746433241875212067816323 5619649862812818101724485)
  ·
    refine ⟨1053684349277403394073341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5619649862812818101724485 1053684349277403394073341)
    ·
      refine ⟨395131630979026272777503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1053684349277403394073341 395131630979026272777503)
      ·
        refine ⟨592697446468539409166255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395131630979026272777503 592697446468539409166255)
        ·
          refine ⟨889046169702809113749383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592697446468539409166255 889046169702809113749383)
          ·
            refine ⟨1333569254554213670624075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889046169702809113749383 1333569254554213670624075)
            ·
              refine ⟨2000353881831320505936113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333569254554213670624075 2000353881831320505936113)
              ·
                refine ⟨1500265411373490379452085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2000353881831320505936113 1500265411373490379452085)
                ·
                  refine ⟨140649882316264723073633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1500265411373490379452085 140649882316264723073633)
                  ·
                    refine ⟨105487411737198542305225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 140649882316264723073633 105487411737198542305225)
                    ·
                      refine ⟨79115558802898906728919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 105487411737198542305225 79115558802898906728919)
                      ·
                        rfl

theorem cell23_154077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_154077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154077 prefixEnd_154077 := by exact prefixLift 154077
  have htrace : WordTrace (prefixWord ++ tailWord_154077) baseStart_154077 baseEnd_154077 := by
    simpa [prefixWord, tailWord_154077, baseEnd_154077] using wordTrace_append hprefix tailTrace_154077
  have hstable : (prefixWord ++ tailWord_154077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154077).length < 2 ^ (prefixWord ++ tailWord_154077).sum := by decide
  have hdescent : baseEnd_154077 < baseStart_154077 := by decide
  rcases family_descends (prefixWord ++ tailWord_154077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154080 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 3]
def baseStart_154080 : Nat := 118140960795 + 154080 * 2 ^ 59
def prefixEnd_154080 : Nat := 4983230072969 + 3 ^ 40 * 154080 * 2
def baseEnd_154080 : Nat := 79117099244862394991405

theorem tailTrace_154080 : CollatzResearch.WordTrace tailWord_154080 prefixEnd_154080 79117099244862394991405 := by
  unfold tailWord_154080
  simp only [CollatzResearch.WordTrace]
  refine ⟨2809879640900974807041847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3746506187867966409389129 2809879640900974807041847)
  ·
    refine ⟨4214819461351462210562771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2809879640900974807041847 4214819461351462210562771)
    ·
      refine ⟨6322229192027193315844157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4214819461351462210562771 6322229192027193315844157)
      ·
        refine ⟨2370835947010197493441559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6322229192027193315844157 2370835947010197493441559)
        ·
          refine ⟨3556253920515296240162339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2370835947010197493441559 3556253920515296240162339)
          ·
            refine ⟨5334380880772944360243509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3556253920515296240162339 5334380880772944360243509)
            ·
              refine ⟨500098207572463533772829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5334380880772944360243509 500098207572463533772829)
              ·
                refine ⟨187536827839673825164811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 500098207572463533772829 187536827839673825164811)
                ·
                  refine ⟨281305241759510737747217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187536827839673825164811 281305241759510737747217)
                  ·
                    refine ⟨210978931319633053310413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 281305241759510737747217 210978931319633053310413)
                    ·
                      refine ⟨79117099244862394991405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 210978931319633053310413 79117099244862394991405)
                      ·
                        rfl

theorem cell23_154080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_154080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154080 prefixEnd_154080 := by exact prefixLift 154080
  have htrace : WordTrace (prefixWord ++ tailWord_154080) baseStart_154080 baseEnd_154080 := by
    simpa [prefixWord, tailWord_154080, baseEnd_154080] using wordTrace_append hprefix tailTrace_154080
  have hstable : (prefixWord ++ tailWord_154080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154080).length < 2 ^ (prefixWord ++ tailWord_154080).sum := by decide
  have hdescent : baseEnd_154080 < baseStart_154080 := by decide
  rcases family_descends (prefixWord ++ tailWord_154080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154083 : List Nat := [1, 1, 1, 6, 3, 1, 10]
def baseStart_154083 : Nat := 118140960795 + 154083 * 2 ^ 59
def prefixEnd_154083 : Nat := 4983230072969 + 3 ^ 40 * 154083 * 2
def baseEnd_154083 : Nat := 976773329466986213011

theorem tailTrace_154083 : CollatzResearch.WordTrace tailWord_154083 prefixEnd_154083 976773329466986213011 := by
  unfold tailWord_154083
  simp only [CollatzResearch.WordTrace]
  refine ⟨5619868700791081126442903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3746579133860720750961935 5619868700791081126442903)
  ·
    refine ⟨8429803051186621689664355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5619868700791081126442903 8429803051186621689664355)
    ·
      refine ⟨12644704576779932534496533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8429803051186621689664355 12644704576779932534496533)
      ·
        refine ⟨592720527036559337554525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12644704576779932534496533 592720527036559337554525)
        ·
          refine ⟨222270197638709751582947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 592720527036559337554525 222270197638709751582947)
          ·
            refine ⟨333405296458064627374421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222270197638709751582947 333405296458064627374421)
            ·
              refine ⟨976773329466986213011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 333405296458064627374421 976773329466986213011)
              ·
                rfl

theorem cell23_154083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 10].length) (baseStart_154083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154083 prefixEnd_154083 := by exact prefixLift 154083
  have htrace : WordTrace (prefixWord ++ tailWord_154083) baseStart_154083 baseEnd_154083 := by
    simpa [prefixWord, tailWord_154083, baseEnd_154083] using wordTrace_append hprefix tailTrace_154083
  have hstable : (prefixWord ++ tailWord_154083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154083).length < 2 ^ (prefixWord ++ tailWord_154083).sum := by decide
  have hdescent : baseEnd_154083 < baseStart_154083 := by decide
  rcases family_descends (prefixWord ++ tailWord_154083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154094 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_154094 : Nat := 118140960795 + 154094 * 2 ^ 59
def prefixEnd_154094 : Nat := 4983230072969 + 3 ^ 40 * 154094 * 2
def baseEnd_154094 : Nat := 79124287974025340216341

theorem tailTrace_154094 : CollatzResearch.WordTrace tailWord_154094 prefixEnd_154094 79124287974025340216341 := by
  unfold tailWord_154094
  simp only [CollatzResearch.WordTrace]
  refine ⟨702533737968903750636667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3746846602500820003395557 702533737968903750636667)
  ·
    refine ⟨1053800606953355625955001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 702533737968903750636667 1053800606953355625955001)
    ·
      refine ⟨790350455215016719466251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1053800606953355625955001 790350455215016719466251)
      ·
        refine ⟨1185525682822525079199377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790350455215016719466251 1185525682822525079199377)
        ·
          refine ⟨889144262116893809399533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185525682822525079199377 889144262116893809399533)
          ·
            refine ⟨333429098293835178524825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 889144262116893809399533 333429098293835178524825)
            ·
              refine ⟨250071823720376383893619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333429098293835178524825 250071823720376383893619)
              ·
                refine ⟨375107735580564575840429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250071823720376383893619 375107735580564575840429)
                ·
                  refine ⟨140665400842711715940161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375107735580564575840429 140665400842711715940161)
                  ·
                    refine ⟨105499050632033786955121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 140665400842711715940161 105499050632033786955121)
                    ·
                      refine ⟨79124287974025340216341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 105499050632033786955121 79124287974025340216341)
                      ·
                        rfl

theorem cell23_154094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_154094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154094 prefixEnd_154094 := by exact prefixLift 154094
  have htrace : WordTrace (prefixWord ++ tailWord_154094) baseStart_154094 baseEnd_154094 := by
    simpa [prefixWord, tailWord_154094, baseEnd_154094] using wordTrace_append hprefix tailTrace_154094
  have hstable : (prefixWord ++ tailWord_154094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154094).length < 2 ^ (prefixWord ++ tailWord_154094).sum := by decide
  have hdescent : baseEnd_154094 < baseStart_154094 := by decide
  rcases family_descends (prefixWord ++ tailWord_154094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154123 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 5]
def baseStart_154123 : Nat := 118140960795 + 154123 * 2 ^ 59
def prefixEnd_154123 : Nat := 4983230072969 + 3 ^ 40 * 154123 * 2
def baseEnd_154123 : Nat := 79139178913005726753707

theorem tailTrace_154123 : CollatzResearch.WordTrace tailWord_154123 prefixEnd_154123 79139178913005726753707 := by
  unfold tailWord_154123
  simp only [CollatzResearch.WordTrace]
  refine ⟨5621327620646167957899023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3747551747097445305266015 5621327620646167957899023)
  ·
    refine ⟨8431991430969251936848535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5621327620646167957899023 8431991430969251936848535)
    ·
      refine ⟨12647987146453877905272803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8431991430969251936848535 12647987146453877905272803)
      ·
        refine ⟨18971980719680816857909205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12647987146453877905272803 18971980719680816857909205)
        ·
          refine ⟨444655798117519145107247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 18971980719680816857909205 444655798117519145107247)
          ·
            refine ⟨666983697176278717660871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444655798117519145107247 666983697176278717660871)
            ·
              refine ⟨1000475545764418076491307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666983697176278717660871 1000475545764418076491307)
              ·
                refine ⟨1500713318646627114736961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000475545764418076491307 1500713318646627114736961)
                ·
                  refine ⟨1125534988984970336052721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1500713318646627114736961 1125534988984970336052721)
                  ·
                    refine ⟨844151241738727752039541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1125534988984970336052721 844151241738727752039541)
                    ·
                      refine ⟨79139178913005726753707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 844151241738727752039541 79139178913005726753707)
                      ·
                        rfl

theorem cell23_154123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 5].length) (baseStart_154123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154123 prefixEnd_154123 := by exact prefixLift 154123
  have htrace : WordTrace (prefixWord ++ tailWord_154123) baseStart_154123 baseEnd_154123 := by
    simpa [prefixWord, tailWord_154123, baseEnd_154123] using wordTrace_append hprefix tailTrace_154123
  have hstable : (prefixWord ++ tailWord_154123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154123).length < 2 ^ (prefixWord ++ tailWord_154123).sum := by decide
  have hdescent : baseEnd_154123 < baseStart_154123 := by decide
  rcases family_descends (prefixWord ++ tailWord_154123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154163 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 4]
def baseStart_154163 : Nat := 118140960795 + 154163 * 2 ^ 59
def prefixEnd_154163 : Nat := 4983230072969 + 3 ^ 40 * 154163 * 2
def baseEnd_154163 : Nat := 79159718139185570253523

theorem tailTrace_154163 : CollatzResearch.WordTrace tailWord_154163 prefixEnd_154163 79159718139185570253523 := by
  unfold tailWord_154163
  simp only [CollatzResearch.WordTrace]
  refine ⟨5622786540501254789355143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3748524360334169859570095 5622786540501254789355143)
  ·
    refine ⟨8434179810751882184032715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5622786540501254789355143 8434179810751882184032715)
    ·
      refine ⟨12651269716127823276049073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8434179810751882184032715 12651269716127823276049073)
      ·
        refine ⟨9488452287095867457036805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12651269716127823276049073 9488452287095867457036805)
        ·
          refine ⟨1779084803830475148194401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9488452287095867457036805 1779084803830475148194401)
          ·
            refine ⟨1334313602872856361145801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1779084803830475148194401 1334313602872856361145801)
            ·
              refine ⟨1000735202154642270859351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334313602872856361145801 1000735202154642270859351)
              ·
                refine ⟨1501102803231963406289027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000735202154642270859351 1501102803231963406289027)
                ·
                  refine ⟨2251654204847945109433541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501102803231963406289027 2251654204847945109433541)
                  ·
                    refine ⟨422185163408989708018789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2251654204847945109433541 422185163408989708018789)
                    ·
                      refine ⟨79159718139185570253523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 422185163408989708018789 79159718139185570253523)
                      ·
                        rfl

theorem cell23_154163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_154163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154163 prefixEnd_154163 := by exact prefixLift 154163
  have htrace : WordTrace (prefixWord ++ tailWord_154163) baseStart_154163 baseEnd_154163 := by
    simpa [prefixWord, tailWord_154163, baseEnd_154163] using wordTrace_append hprefix tailTrace_154163
  have hstable : (prefixWord ++ tailWord_154163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154163).length < 2 ^ (prefixWord ++ tailWord_154163).sum := by decide
  have hdescent : baseEnd_154163 < baseStart_154163 := by decide
  rcases family_descends (prefixWord ++ tailWord_154163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154240 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 4]
def baseStart_154240 : Nat := 118140960795 + 154240 * 2 ^ 59
def prefixEnd_154240 : Nat := 4983230072969 + 3 ^ 40 * 154240 * 2
def baseEnd_154240 : Nat := 79199256149581768990669

theorem tailTrace_154240 : CollatzResearch.WordTrace tailWord_154240 prefixEnd_154240 79199256149581768990669 := by
  unfold tailWord_154240
  simp only [CollatzResearch.WordTrace]
  refine ⟨2812797480611148469954087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3750396640814864626605449 2812797480611148469954087)
  ·
    refine ⟨4219196220916722704931131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2812797480611148469954087 4219196220916722704931131)
    ·
      refine ⟨6328794331375084057396697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4219196220916722704931131 6328794331375084057396697)
      ·
        refine ⟨4746595748531313043047523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6328794331375084057396697 4746595748531313043047523)
        ·
          refine ⟨7119893622796969564571285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4746595748531313043047523 7119893622796969564571285)
          ·
            refine ⟨333745013568607948339279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7119893622796969564571285 333745013568607948339279)
            ·
              refine ⟨500617520352911922508919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333745013568607948339279 500617520352911922508919)
              ·
                refine ⟨750926280529367883763379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500617520352911922508919 750926280529367883763379)
                ·
                  refine ⟨1126389420794051825645069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750926280529367883763379 1126389420794051825645069)
                  ·
                    refine ⟨422396032797769434616901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1126389420794051825645069 422396032797769434616901)
                    ·
                      refine ⟨79199256149581768990669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 422396032797769434616901 79199256149581768990669)
                      ·
                        rfl

theorem cell23_154240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_154240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154240 prefixEnd_154240 := by exact prefixLift 154240
  have htrace : WordTrace (prefixWord ++ tailWord_154240) baseStart_154240 baseEnd_154240 := by
    simpa [prefixWord, tailWord_154240, baseEnd_154240] using wordTrace_append hprefix tailTrace_154240
  have hstable : (prefixWord ++ tailWord_154240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154240).length < 2 ^ (prefixWord ++ tailWord_154240).sum := by decide
  have hdescent : baseEnd_154240 < baseStart_154240 := by decide
  rcases family_descends (prefixWord ++ tailWord_154240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154290 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_154290 : Nat := 118140960795 + 154290 * 2 ^ 59
def prefixEnd_154290 : Nat := 4983230072969 + 3 ^ 40 * 154290 * 2
def baseEnd_154290 : Nat := 79224930182306573365439

theorem tailTrace_154290 : CollatzResearch.WordTrace tailWord_154290 prefixEnd_154290 79224930182306573365439 := by
  unfold tailWord_154290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1406854652760288869807081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3751612407360770319485549 1406854652760288869807081)
  ·
    refine ⟨1055140989570216652355311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1406854652760288869807081 1055140989570216652355311)
    ·
      refine ⟨1582711484355324978532967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1055140989570216652355311 1582711484355324978532967)
      ·
        refine ⟨2374067226532987467799451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582711484355324978532967 2374067226532987467799451)
        ·
          refine ⟨3561100839799481201699177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374067226532987467799451 3561100839799481201699177)
          ·
            refine ⟨2670825629849610901274383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3561100839799481201699177 2670825629849610901274383)
            ·
              refine ⟨4006238444774416351911575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670825629849610901274383 4006238444774416351911575)
              ·
                refine ⟨6009357667161624527867363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006238444774416351911575 6009357667161624527867363)
                ·
                  refine ⟨9014036500742436791801045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6009357667161624527867363 9014036500742436791801045)
                  ·
                    refine ⟨211266480486150862307837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9014036500742436791801045 211266480486150862307837)
                    ·
                      refine ⟨79224930182306573365439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 211266480486150862307837 79224930182306573365439)
                      ·
                        rfl

theorem cell23_154290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_154290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154290 prefixEnd_154290 := by exact prefixLift 154290
  have htrace : WordTrace (prefixWord ++ tailWord_154290) baseStart_154290 baseEnd_154290 := by
    simpa [prefixWord, tailWord_154290, baseEnd_154290] using wordTrace_append hprefix tailTrace_154290
  have hstable : (prefixWord ++ tailWord_154290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154290).length < 2 ^ (prefixWord ++ tailWord_154290).sum := by decide
  have hdescent : baseEnd_154290 < baseStart_154290 := by decide
  rcases family_descends (prefixWord ++ tailWord_154290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154301 : List Nat := [1, 4, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_154301 : Nat := 118140960795 + 154301 * 2 ^ 59
def prefixEnd_154301 : Nat := 4983230072969 + 3 ^ 40 * 154301 * 2
def baseEnd_154301 : Nat := 26410192823168676775963

theorem tailTrace_154301 : CollatzResearch.WordTrace tailWord_154301 prefixEnd_154301 26410192823168676775963 := by
  unfold tailWord_154301
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627819814001304357878757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3751879876000869571919171 5627819814001304357878757)
  ·
    refine ⟨1055216215125244567102267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5627819814001304357878757 1055216215125244567102267)
    ·
      refine ⟨1582824322687866850653401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1055216215125244567102267 1582824322687866850653401)
      ·
        refine ⟨1187118242015900137990051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1582824322687866850653401 1187118242015900137990051)
        ·
          refine ⟨1780677363023850206985077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187118242015900137990051 1780677363023850206985077)
          ·
            refine ⟨166938502783485956904851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1780677363023850206985077 166938502783485956904851)
            ·
              refine ⟨250407754175228935357277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166938502783485956904851 250407754175228935357277)
              ·
                refine ⟨93902907815710850758979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250407754175228935357277 93902907815710850758979)
                ·
                  refine ⟨140854361723566276138469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93902907815710850758979 140854361723566276138469)
                  ·
                    refine ⟨26410192823168676775963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140854361723566276138469 26410192823168676775963)
                    ·
                      rfl

theorem cell23_154301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_154301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154301 prefixEnd_154301 := by exact prefixLift 154301
  have htrace : WordTrace (prefixWord ++ tailWord_154301) baseStart_154301 baseEnd_154301 := by
    simpa [prefixWord, tailWord_154301, baseEnd_154301] using wordTrace_append hprefix tailTrace_154301
  have hstable : (prefixWord ++ tailWord_154301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154301).length < 2 ^ (prefixWord ++ tailWord_154301).sum := by decide
  have hdescent : baseEnd_154301 < baseStart_154301 := by decide
  rcases family_descends (prefixWord ++ tailWord_154301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154375 : List Nat := [1, 1, 4, 4, 1, 3, 2, 2, 1, 1, 3]
def baseStart_154375 : Nat := 118140960795 + 154375 * 2 ^ 59
def prefixEnd_154375 : Nat := 4983230072969 + 3 ^ 40 * 154375 * 2
def baseEnd_154375 : Nat := 79268576037938740802549

theorem tailTrace_154375 : CollatzResearch.WordTrace tailWord_154375 prefixEnd_154375 79268576037938740802549 := by
  unfold tailWord_154375
  simp only [CollatzResearch.WordTrace]
  refine ⟨5630518815733214996072579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3753679210488809997381719 5630518815733214996072579)
  ·
    refine ⟨8445778223599822494108869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5630518815733214996072579 8445778223599822494108869)
    ·
      refine ⟨1583583416924966717645413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8445778223599822494108869 1583583416924966717645413)
      ·
        refine ⟨296921890673431259558515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1583583416924966717645413 296921890673431259558515)
        ·
          refine ⟨445382836010146889337773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296921890673431259558515 445382836010146889337773)
          ·
            refine ⟨167018563503805083501665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 445382836010146889337773 167018563503805083501665)
            ·
              refine ⟨125263922627853812626249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167018563503805083501665 125263922627853812626249)
              ·
                refine ⟨93947941970890359469687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125263922627853812626249 93947941970890359469687)
                ·
                  refine ⟨140921912956335539204531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93947941970890359469687 140921912956335539204531)
                  ·
                    refine ⟨211382869434503308806797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140921912956335539204531 211382869434503308806797)
                    ·
                      refine ⟨79268576037938740802549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 211382869434503308806797 79268576037938740802549)
                      ·
                        rfl

theorem cell23_154375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_154375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154375 prefixEnd_154375 := by exact prefixLift 154375
  have htrace : WordTrace (prefixWord ++ tailWord_154375) baseStart_154375 baseEnd_154375 := by
    simpa [prefixWord, tailWord_154375, baseEnd_154375] using wordTrace_append hprefix tailTrace_154375
  have hstable : (prefixWord ++ tailWord_154375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154375).length < 2 ^ (prefixWord ++ tailWord_154375).sum := by decide
  have hdescent : baseEnd_154375 < baseStart_154375 := by decide
  rcases family_descends (prefixWord ++ tailWord_154375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154404 : List Nat := [2, 3, 1, 3, 3, 1, 3, 7]
def baseStart_154404 : Nat := 118140960795 + 154404 * 2 ^ 59
def prefixEnd_154404 : Nat := 4983230072969 + 3 ^ 40 * 154404 * 2
def baseEnd_154404 : Nat := 2936424702848856568145

theorem tailTrace_154404 : CollatzResearch.WordTrace tailWord_154404 prefixEnd_154404 2936424702848856568145 := by
  unfold tailWord_154404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2815788266314076474439133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3754384355085435299252177 2815788266314076474439133)
  ·
    refine ⟨1055920599867778677914675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2815788266314076474439133 1055920599867778677914675)
    ·
      refine ⟨1583880899801668016872013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1055920599867778677914675 1583880899801668016872013)
      ·
        refine ⟨593955337425625506327005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1583880899801668016872013 593955337425625506327005)
        ·
          refine ⟨222733251534609564872627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 593955337425625506327005 222733251534609564872627)
          ·
            refine ⟨334099877301914347308941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222733251534609564872627 334099877301914347308941)
            ·
              refine ⟨125287453988217880240853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334099877301914347308941 125287453988217880240853)
              ·
                refine ⟨2936424702848856568145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 125287453988217880240853 2936424702848856568145)
                ·
                  rfl

theorem cell23_154404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 7].length) (baseStart_154404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154404 prefixEnd_154404 := by exact prefixLift 154404
  have htrace : WordTrace (prefixWord ++ tailWord_154404) baseStart_154404 baseEnd_154404 := by
    simpa [prefixWord, tailWord_154404, baseEnd_154404] using wordTrace_append hprefix tailTrace_154404
  have hstable : (prefixWord ++ tailWord_154404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154404).length < 2 ^ (prefixWord ++ tailWord_154404).sum := by decide
  have hdescent : baseEnd_154404 < baseStart_154404 := by decide
  rcases family_descends (prefixWord ++ tailWord_154404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154431 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 2, 1, 3]
def baseStart_154431 : Nat := 118140960795 + 154431 * 2 ^ 59
def prefixEnd_154431 : Nat := 4983230072969 + 3 ^ 40 * 154431 * 2
def baseEnd_154431 : Nat := 79297330954590521702291

theorem tailTrace_154431 : CollatzResearch.WordTrace tailWord_154431 prefixEnd_154431 79297330954590521702291 := by
  unfold tailWord_154431
  simp only [CollatzResearch.WordTrace]
  refine ⟨5632561303530336560111147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3755040869020224373407431 5632561303530336560111147)
  ·
    refine ⟨8448841955295504840166721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5632561303530336560111147 8448841955295504840166721)
    ·
      refine ⟨6336631466471628630125041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8448841955295504840166721 6336631466471628630125041)
      ·
        refine ⟨4752473599853721472593781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6336631466471628630125041 4752473599853721472593781)
        ·
          refine ⟨445544399986286388055667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4752473599853721472593781 445544399986286388055667)
          ·
            refine ⟨668316599979429582083501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445544399986286388055667 668316599979429582083501)
            ·
              refine ⟨250618724992286093281313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 668316599979429582083501 250618724992286093281313)
              ·
                refine ⟨187964043744214569960985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250618724992286093281313 187964043744214569960985)
                ·
                  refine ⟨140973032808160927470739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187964043744214569960985 140973032808160927470739)
                  ·
                    refine ⟨211459549212241391206109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140973032808160927470739 211459549212241391206109)
                    ·
                      refine ⟨79297330954590521702291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 211459549212241391206109 79297330954590521702291)
                      ·
                        rfl

theorem cell23_154431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_154431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154431 prefixEnd_154431 := by exact prefixLift 154431
  have htrace : WordTrace (prefixWord ++ tailWord_154431) baseStart_154431 baseEnd_154431 := by
    simpa [prefixWord, tailWord_154431, baseEnd_154431] using wordTrace_append hprefix tailTrace_154431
  have hstable : (prefixWord ++ tailWord_154431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154431).length < 2 ^ (prefixWord ++ tailWord_154431).sum := by decide
  have hdescent : baseEnd_154431 < baseStart_154431 := by decide
  rcases family_descends (prefixWord ++ tailWord_154431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154471 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_154471 : Nat := 118140960795 + 154471 * 2 ^ 59
def prefixEnd_154471 : Nat := 4983230072969 + 3 ^ 40 * 154471 * 2
def baseEnd_154471 : Nat := 79317870180770365202107

theorem tailTrace_154471 : CollatzResearch.WordTrace tailWord_154471 prefixEnd_154471 79317870180770365202107 := by
  unfold tailWord_154471
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634020223385423391567267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3756013482256948927711511 5634020223385423391567267)
  ·
    refine ⟨8451030335078135087350901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5634020223385423391567267 8451030335078135087350901)
    ·
      refine ⟨792284093913575164439147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8451030335078135087350901 792284093913575164439147)
      ·
        refine ⟨1188426140870362746658721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792284093913575164439147 1188426140870362746658721)
        ·
          refine ⟨891319605652772059994041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1188426140870362746658721 891319605652772059994041)
          ·
            refine ⟨668489704239579044995531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 891319605652772059994041 668489704239579044995531)
            ·
              refine ⟨1002734556359368567493297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668489704239579044995531 1002734556359368567493297)
              ·
                refine ⟨752050917269526425619973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002734556359368567493297 752050917269526425619973)
                ·
                  refine ⟨141009546988036204803745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752050917269526425619973 141009546988036204803745)
                  ·
                    refine ⟨105757160241027153602809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141009546988036204803745 105757160241027153602809)
                    ·
                      refine ⟨79317870180770365202107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 105757160241027153602809 79317870180770365202107)
                      ·
                        rfl

theorem cell23_154471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_154471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154471 prefixEnd_154471 := by exact prefixLift 154471
  have htrace : WordTrace (prefixWord ++ tailWord_154471) baseStart_154471 baseEnd_154471 := by
    simpa [prefixWord, tailWord_154471, baseEnd_154471] using wordTrace_append hprefix tailTrace_154471
  have hstable : (prefixWord ++ tailWord_154471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154471).length < 2 ^ (prefixWord ++ tailWord_154471).sum := by decide
  have hdescent : baseEnd_154471 < baseStart_154471 := by decide
  rcases family_descends (prefixWord ++ tailWord_154471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154487 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 3]
def baseStart_154487 : Nat := 118140960795 + 154487 * 2 ^ 59
def prefixEnd_154487 : Nat := 4983230072969 + 3 ^ 40 * 154487 * 2
def baseEnd_154487 : Nat := 79326085871242302602033

theorem tailTrace_154487 : CollatzResearch.WordTrace tailWord_154487 prefixEnd_154487 79326085871242302602033 := by
  unfold tailWord_154487
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634603791327458124149715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3756402527551638749433143 5634603791327458124149715)
  ·
    refine ⟨8451905686991187186224573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5634603791327458124149715 8451905686991187186224573)
    ·
      refine ⟨3169464632621695194834215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8451905686991187186224573 3169464632621695194834215)
      ·
        refine ⟨4754196948932542792251323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169464632621695194834215 4754196948932542792251323)
        ·
          refine ⟨7131295423398814188376985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4754196948932542792251323 7131295423398814188376985)
          ·
            refine ⟨5348471567549110641282739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7131295423398814188376985 5348471567549110641282739)
            ·
              refine ⟨8022707351323665961924109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5348471567549110641282739 8022707351323665961924109)
              ·
                refine ⟨3008515256746374735721541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8022707351323665961924109 3008515256746374735721541)
                ·
                  refine ⟨564096610639945262947789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3008515256746374735721541 564096610639945262947789)
                  ·
                    refine ⟨211536228989979473605421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 564096610639945262947789 211536228989979473605421)
                    ·
                      refine ⟨79326085871242302602033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 211536228989979473605421 79326085871242302602033)
                      ·
                        rfl

theorem cell23_154487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_154487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154487 prefixEnd_154487 := by exact prefixLift 154487
  have htrace : WordTrace (prefixWord ++ tailWord_154487) baseStart_154487 baseEnd_154487 := by
    simpa [prefixWord, tailWord_154487, baseEnd_154487] using wordTrace_append hprefix tailTrace_154487
  have hstable : (prefixWord ++ tailWord_154487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154487).length < 2 ^ (prefixWord ++ tailWord_154487).sum := by decide
  have hdescent : baseEnd_154487 < baseStart_154487 := by decide
  rcases family_descends (prefixWord ++ tailWord_154487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154505 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 2, 2, 2]
def baseStart_154505 : Nat := 118140960795 + 154505 * 2 ^ 59
def prefixEnd_154505 : Nat := 4983230072969 + 3 ^ 40 * 154505 * 2
def baseEnd_154505 : Nat := 79335328523023232176951

theorem tailTrace_154505 : CollatzResearch.WordTrace tailWord_154505 prefixEnd_154505 79335328523023232176951 := by
  unfold tailWord_154505
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635260305262247198304969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3756840203508164798869979 5635260305262247198304969)
  ·
    refine ⟨4226445228946685398728727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5635260305262247198304969 4226445228946685398728727)
    ·
      refine ⟨6339667843420028098093091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4226445228946685398728727 6339667843420028098093091)
      ·
        refine ⟨9509501765130042147139637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6339667843420028098093091 9509501765130042147139637)
        ·
          refine ⟨891515790480941451294341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9509501765130042147139637 891515790480941451294341)
          ·
            refine ⟨167159210715176522117689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 891515790480941451294341 167159210715176522117689)
            ·
              refine ⟨125369408036382391588267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167159210715176522117689 125369408036382391588267)
              ·
                refine ⟨188054112054573587382401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125369408036382391588267 188054112054573587382401)
                ·
                  refine ⟨141040584040930190536801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188054112054573587382401 141040584040930190536801)
                  ·
                    refine ⟨105780438030697642902601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141040584040930190536801 105780438030697642902601)
                    ·
                      refine ⟨79335328523023232176951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 105780438030697642902601 79335328523023232176951)
                      ·
                        rfl

theorem cell23_154505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 2, 2, 2].length) (baseStart_154505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154505 prefixEnd_154505 := by exact prefixLift 154505
  have htrace : WordTrace (prefixWord ++ tailWord_154505) baseStart_154505 baseEnd_154505 := by
    simpa [prefixWord, tailWord_154505, baseEnd_154505] using wordTrace_append hprefix tailTrace_154505
  have hstable : (prefixWord ++ tailWord_154505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154505).length < 2 ^ (prefixWord ++ tailWord_154505).sum := by decide
  have hdescent : baseEnd_154505 < baseStart_154505 := by decide
  rcases family_descends (prefixWord ++ tailWord_154505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154545 : List Nat := [1, 2, 2, 4, 4, 1, 2, 2, 5]
def baseStart_154545 : Nat := 118140960795 + 154545 * 2 ^ 59
def prefixEnd_154545 : Nat := 4983230072969 + 3 ^ 40 * 154545 * 2
def baseEnd_154545 : Nat := 8817318638800341741863

theorem tailTrace_154545 : CollatzResearch.WordTrace tailWord_154545 prefixEnd_154545 8817318638800341741863 := by
  unfold tailWord_154545
  simp only [CollatzResearch.WordTrace]
  refine ⟨5636719225117334029761089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3757812816744889353174059 5636719225117334029761089)
  ·
    refine ⟨4227539418838000522320817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5636719225117334029761089 4227539418838000522320817)
    ·
      refine ⟨3170654564128500391740613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4227539418838000522320817 3170654564128500391740613)
      ·
        refine ⟨594497730774093823451365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3170654564128500391740613 594497730774093823451365)
        ·
          refine ⟨111468324520142591897131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 594497730774093823451365 111468324520142591897131)
          ·
            refine ⟨167202486780213887845697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111468324520142591897131 167202486780213887845697)
            ·
              refine ⟨125401865085160415884273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167202486780213887845697 125401865085160415884273)
              ·
                refine ⟨94051398813870311913205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125401865085160415884273 94051398813870311913205)
                ·
                  refine ⟨8817318638800341741863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94051398813870311913205 8817318638800341741863)
                  ·
                    rfl

theorem cell23_154545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 5].length) (baseStart_154545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154545 prefixEnd_154545 := by exact prefixLift 154545
  have htrace : WordTrace (prefixWord ++ tailWord_154545) baseStart_154545 baseEnd_154545 := by
    simpa [prefixWord, tailWord_154545, baseEnd_154545] using wordTrace_append hprefix tailTrace_154545
  have hstable : (prefixWord ++ tailWord_154545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154545).length < 2 ^ (prefixWord ++ tailWord_154545).sum := by decide
  have hdescent : baseEnd_154545 < baseStart_154545 := by decide
  rcases family_descends (prefixWord ++ tailWord_154545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154548 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_154548 : Nat := 118140960795 + 154548 * 2 ^ 59
def prefixEnd_154548 : Nat := 4983230072969 + 3 ^ 40 * 154548 * 2
def baseEnd_154548 : Nat := 79357408191166563939253

theorem tailTrace_154548 : CollatzResearch.WordTrace tailWord_154548 prefixEnd_154548 79357408191166563939253 := by
  unfold tailWord_154548
  simp only [CollatzResearch.WordTrace]
  refine ⟨2818414322053232771060149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3757885762737643694746865 2818414322053232771060149)
  ·
    refine ⟨264226342692490572286889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2818414322053232771060149 264226342692490572286889)
    ·
      refine ⟨198169757019367929215167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264226342692490572286889 198169757019367929215167)
      ·
        refine ⟨297254635529051893822751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198169757019367929215167 297254635529051893822751)
        ·
          refine ⟨445881953293577840734127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297254635529051893822751 445881953293577840734127)
          ·
            refine ⟨668822929940366761101191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445881953293577840734127 668822929940366761101191)
            ·
              refine ⟨1003234394910550141651787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668822929940366761101191 1003234394910550141651787)
              ·
                refine ⟨1504851592365825212477681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003234394910550141651787 1504851592365825212477681)
                ·
                  refine ⟨1128638694274368909358261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1504851592365825212477681 1128638694274368909358261)
                  ·
                    refine ⟨105809877588222085252337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1128638694274368909358261 105809877588222085252337)
                    ·
                      refine ⟨79357408191166563939253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 105809877588222085252337 79357408191166563939253)
                      ·
                        rfl

theorem cell23_154548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_154548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154548 prefixEnd_154548 := by exact prefixLift 154548
  have htrace : WordTrace (prefixWord ++ tailWord_154548) baseStart_154548 baseEnd_154548 := by
    simpa [prefixWord, tailWord_154548, baseEnd_154548] using wordTrace_append hprefix tailTrace_154548
  have hstable : (prefixWord ++ tailWord_154548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154548).length < 2 ^ (prefixWord ++ tailWord_154548).sum := by decide
  have hdescent : baseEnd_154548 < baseStart_154548 := by decide
  rcases family_descends (prefixWord ++ tailWord_154548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154554 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 3, 4]
def baseStart_154554 : Nat := 118140960795 + 154554 * 2 ^ 59
def prefixEnd_154554 : Nat := 4983230072969 + 3 ^ 40 * 154554 * 2
def baseEnd_154554 : Nat := 26453496358364513488075

theorem tailTrace_154554 : CollatzResearch.WordTrace tailWord_154554 prefixEnd_154554 26453496358364513488075 := by
  unfold tailWord_154554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1409261870521182141709679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3758031654723152377892477 1409261870521182141709679)
  ·
    refine ⟨2113892805781773212564519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1409261870521182141709679 2113892805781773212564519)
    ·
      refine ⟨3170839208672659818846779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2113892805781773212564519 3170839208672659818846779)
      ·
        refine ⟨4756258813008989728270169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3170839208672659818846779 4756258813008989728270169)
        ·
          refine ⟨3567194109756742296202627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4756258813008989728270169 3567194109756742296202627)
          ·
            refine ⟨5350791164635113444303941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567194109756742296202627 5350791164635113444303941)
            ·
              refine ⟨1003273343369083770806989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5350791164635113444303941 1003273343369083770806989)
              ·
                refine ⟨376227503763406414052621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1003273343369083770806989 376227503763406414052621)
                ·
                  refine ⟨141085313911277405269733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 376227503763406414052621 141085313911277405269733)
                  ·
                    refine ⟨26453496358364513488075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141085313911277405269733 26453496358364513488075)
                    ·
                      rfl

theorem cell23_154554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_154554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154554 prefixEnd_154554 := by exact prefixLift 154554
  have htrace : WordTrace (prefixWord ++ tailWord_154554) baseStart_154554 baseEnd_154554 := by
    simpa [prefixWord, tailWord_154554, baseEnd_154554] using wordTrace_append hprefix tailTrace_154554
  have hstable : (prefixWord ++ tailWord_154554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154554).length < 2 ^ (prefixWord ++ tailWord_154554).sum := by decide
  have hdescent : baseEnd_154554 < baseStart_154554 := by decide
  rcases family_descends (prefixWord ++ tailWord_154554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154578 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_154578 : Nat := 118140960795 + 154578 * 2 ^ 59
def prefixEnd_154578 : Nat := 4983230072969 + 3 ^ 40 * 154578 * 2
def baseEnd_154578 : Nat := 79372812610801446564115

theorem tailTrace_154578 : CollatzResearch.WordTrace tailWord_154578 prefixEnd_154578 79372812610801446564115 := by
  unfold tailWord_154578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1409480708499445166428097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3758615222665187110474925 1409480708499445166428097)
  ·
    refine ⟨1057110531374583874821073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1409480708499445166428097 1057110531374583874821073)
    ·
      refine ⟨792832898530937906115805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1057110531374583874821073 792832898530937906115805)
      ·
        refine ⟨297312336949101714793427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 792832898530937906115805 297312336949101714793427)
        ·
          refine ⟨445968505423652572190141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297312336949101714793427 445968505423652572190141)
          ·
            refine ⟨167238189533869714571303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 445968505423652572190141 167238189533869714571303)
            ·
              refine ⟨250857284300804571856955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167238189533869714571303 250857284300804571856955)
              ·
                refine ⟨376285926451206857785433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250857284300804571856955 376285926451206857785433)
                ·
                  refine ⟨282214444838405143339075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376285926451206857785433 282214444838405143339075)
                  ·
                    refine ⟨423321667257607715008613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 282214444838405143339075 423321667257607715008613)
                    ·
                      refine ⟨79372812610801446564115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 423321667257607715008613 79372812610801446564115)
                      ·
                        rfl

theorem cell23_154578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_154578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154578 prefixEnd_154578 := by exact prefixLift 154578
  have htrace : WordTrace (prefixWord ++ tailWord_154578) baseStart_154578 baseEnd_154578 := by
    simpa [prefixWord, tailWord_154578, baseEnd_154578] using wordTrace_append hprefix tailTrace_154578
  have hstable : (prefixWord ++ tailWord_154578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154578).length < 2 ^ (prefixWord ++ tailWord_154578).sum := by decide
  have hdescent : baseEnd_154578 < baseStart_154578 := by decide
  rcases family_descends (prefixWord ++ tailWord_154578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154581 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_154581 : Nat := 118140960795 + 154581 * 2 ^ 59
def prefixEnd_154581 : Nat := 4983230072969 + 3 ^ 40 * 154581 * 2
def baseEnd_154581 : Nat := 79374353052764934826601

theorem tailTrace_154581 : CollatzResearch.WordTrace tailWord_154581 prefixEnd_154581 79374353052764934826601 := by
  unfold tailWord_154581
  simp only [CollatzResearch.WordTrace]
  refine ⟨5638032252986912178071597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3758688168657941452047731 5638032252986912178071597)
  ·
    refine ⟨2114262094870092066776849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5638032252986912178071597 2114262094870092066776849)
    ·
      refine ⟨1585696571152569050082637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2114262094870092066776849 1585696571152569050082637)
      ·
        refine ⟨594636214182213393780989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1585696571152569050082637 594636214182213393780989)
        ·
          refine ⟨222988580318330022667871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 594636214182213393780989 222988580318330022667871)
          ·
            refine ⟨334482870477495034001807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222988580318330022667871 334482870477495034001807)
            ·
              refine ⟨501724305716242551002711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334482870477495034001807 501724305716242551002711)
              ·
                refine ⟨752586458574363826504067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501724305716242551002711 752586458574363826504067)
                ·
                  refine ⟨1128879687861545739756101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752586458574363826504067 1128879687861545739756101)
                  ·
                    refine ⟨211664941474039826204269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1128879687861545739756101 211664941474039826204269)
                    ·
                      refine ⟨79374353052764934826601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 211664941474039826204269 79374353052764934826601)
                      ·
                        rfl

theorem cell23_154581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_154581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154581 prefixEnd_154581 := by exact prefixLift 154581
  have htrace : WordTrace (prefixWord ++ tailWord_154581) baseStart_154581 baseEnd_154581 := by
    simpa [prefixWord, tailWord_154581, baseEnd_154581] using wordTrace_append hprefix tailTrace_154581
  have hstable : (prefixWord ++ tailWord_154581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154581).length < 2 ^ (prefixWord ++ tailWord_154581).sum := by decide
  have hdescent : baseEnd_154581 < baseStart_154581 := by decide
  rcases family_descends (prefixWord ++ tailWord_154581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154631 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 1, 5]
def baseStart_154631 : Nat := 118140960795 + 154631 * 2 ^ 59
def prefixEnd_154631 : Nat := 4983230072969 + 3 ^ 40 * 154631 * 2
def baseEnd_154631 : Nat := 26466675695163246400457

theorem tailTrace_154631 : CollatzResearch.WordTrace tailWord_154631 prefixEnd_154631 26466675695163246400457 := by
  unfold tailWord_154631
  simp only [CollatzResearch.WordTrace]
  refine ⟨5639855902805770717391747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3759903935203847144927831 5639855902805770717391747)
  ·
    refine ⟨8459783854208656076087621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5639855902805770717391747 8459783854208656076087621)
    ·
      refine ⟨1586209472664123014266429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8459783854208656076087621 1586209472664123014266429)
      ·
        refine ⟨594828552249046130349911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1586209472664123014266429 594828552249046130349911)
        ·
          refine ⟨892242828373569195524867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594828552249046130349911 892242828373569195524867)
          ·
            refine ⟨1338364242560353793287301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892242828373569195524867 1338364242560353793287301)
            ·
              refine ⟨250943295480066336241369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1338364242560353793287301 250943295480066336241369)
              ·
                refine ⟨188207471610049752181027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250943295480066336241369 188207471610049752181027)
                ·
                  refine ⟨282311207415074628271541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188207471610049752181027 282311207415074628271541)
                  ·
                    refine ⟨26466675695163246400457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 282311207415074628271541 26466675695163246400457)
                    ·
                      rfl

theorem cell23_154631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_154631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154631 prefixEnd_154631 := by exact prefixLift 154631
  have htrace : WordTrace (prefixWord ++ tailWord_154631) baseStart_154631 baseEnd_154631 := by
    simpa [prefixWord, tailWord_154631, baseEnd_154631] using wordTrace_append hprefix tailTrace_154631
  have hstable : (prefixWord ++ tailWord_154631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154631).length < 2 ^ (prefixWord ++ tailWord_154631).sum := by decide
  have hdescent : baseEnd_154631 < baseStart_154631 := by decide
  rcases family_descends (prefixWord ++ tailWord_154631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154645 : List Nat := [1, 3, 2, 1, 4, 1, 3, 3, 1, 1, 3]
def baseStart_154645 : Nat := 118140960795 + 154645 * 2 ^ 59
def prefixEnd_154645 : Nat := 4983230072969 + 3 ^ 40 * 154645 * 2
def baseEnd_154645 : Nat := 79407215814652684426307

theorem tailTrace_154645 : CollatzResearch.WordTrace tailWord_154645 prefixEnd_154645 79407215814652684426307 := by
  unfold tailWord_154645
  simp only [CollatzResearch.WordTrace]
  refine ⟨5640366524755051108401389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3760244349836700738934259 5640366524755051108401389)
  ·
    refine ⟨2115137446783144165650521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5640366524755051108401389 2115137446783144165650521)
    ·
      refine ⟨1586353085087358124237891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2115137446783144165650521 1586353085087358124237891)
      ·
        refine ⟨2379529627631037186356837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1586353085087358124237891 2379529627631037186356837)
        ·
          refine ⟨446161805180819472441907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2379529627631037186356837 446161805180819472441907)
          ·
            refine ⟨669242707771229208662861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446161805180819472441907 669242707771229208662861)
            ·
              refine ⟨250966015414210953248573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 669242707771229208662861 250966015414210953248573)
              ·
                refine ⟨94112255780329107468215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250966015414210953248573 94112255780329107468215)
                ·
                  refine ⟨141168383670493661202323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94112255780329107468215 141168383670493661202323)
                  ·
                    refine ⟨211752575505740491803485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 141168383670493661202323 211752575505740491803485)
                    ·
                      refine ⟨79407215814652684426307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 211752575505740491803485 79407215814652684426307)
                      ·
                        rfl

theorem cell23_154645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_154645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154645 prefixEnd_154645 := by exact prefixLift 154645
  have htrace : WordTrace (prefixWord ++ tailWord_154645) baseStart_154645 baseEnd_154645 := by
    simpa [prefixWord, tailWord_154645, baseEnd_154645] using wordTrace_append hprefix tailTrace_154645
  have hstable : (prefixWord ++ tailWord_154645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154645).length < 2 ^ (prefixWord ++ tailWord_154645).sum := by decide
  have hdescent : baseEnd_154645 < baseStart_154645 := by decide
  rcases family_descends (prefixWord ++ tailWord_154645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154661 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 2, 4]
def baseStart_154661 : Nat := 118140960795 + 154661 * 2 ^ 59
def prefixEnd_154661 : Nat := 4983230072969 + 3 ^ 40 * 154661 * 2
def baseEnd_154661 : Nat := 26471810501708207275411

theorem tailTrace_154661 : CollatzResearch.WordTrace tailWord_154661 prefixEnd_154661 26471810501708207275411 := by
  unfold tailWord_154661
  simp only [CollatzResearch.WordTrace]
  refine ⟨5640950092697085840983837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3760633395131390560655891 5640950092697085840983837)
  ·
    refine ⟨2115356284761407190368939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5640950092697085840983837 2115356284761407190368939)
    ·
      refine ⟨3173034427142110785553409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2115356284761407190368939 3173034427142110785553409)
      ·
        refine ⟨2379775820356583089165057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3173034427142110785553409 2379775820356583089165057)
        ·
          refine ⟨1784831865267437316873793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2379775820356583089165057 1784831865267437316873793)
          ·
            refine ⟨1338623898950577987655345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1784831865267437316873793 1338623898950577987655345)
            ·
              refine ⟨1003967924212933490741509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338623898950577987655345 1003967924212933490741509)
              ·
                refine ⟨188243985789925029514033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1003967924212933490741509 188243985789925029514033)
                ·
                  refine ⟨141182989342443772135525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188243985789925029514033 141182989342443772135525)
                  ·
                    refine ⟨26471810501708207275411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141182989342443772135525 26471810501708207275411)
                    ·
                      rfl

theorem cell23_154661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_154661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154661 prefixEnd_154661 := by exact prefixLift 154661
  have htrace : WordTrace (prefixWord ++ tailWord_154661) baseStart_154661 baseEnd_154661 := by
    simpa [prefixWord, tailWord_154661, baseEnd_154661] using wordTrace_append hprefix tailTrace_154661
  have hstable : (prefixWord ++ tailWord_154661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154661).length < 2 ^ (prefixWord ++ tailWord_154661).sum := by decide
  have hdescent : baseEnd_154661 < baseStart_154661 := by decide
  rcases family_descends (prefixWord ++ tailWord_154661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154674 : List Nat := [3, 2, 1, 1, 2, 2, 4, 8]
def baseStart_154674 : Nat := 118140960795 + 154674 * 2 ^ 59
def prefixEnd_154674 : Nat := 4983230072969 + 3 ^ 40 * 154674 * 2
def baseEnd_154674 : Nat := 2941559509393817443099

theorem tailTrace_154674 : CollatzResearch.WordTrace tailWord_154674 prefixEnd_154674 2941559509393817443099 := by
  unfold tailWord_154674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1410356060412497265301769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3760949494433326040804717 1410356060412497265301769)
  ·
    refine ⟨1057767045309372948976327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1410356060412497265301769 1057767045309372948976327)
    ·
      refine ⟨1586650567964059423464491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1057767045309372948976327 1586650567964059423464491)
      ·
        refine ⟨2379975851946089135196737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1586650567964059423464491 2379975851946089135196737)
        ·
          refine ⟨1784981888959566851397553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2379975851946089135196737 1784981888959566851397553)
          ·
            refine ⟨1338736416719675138548165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1784981888959566851397553 1338736416719675138548165)
            ·
              refine ⟨251013078134939088477781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1338736416719675138548165 251013078134939088477781)
              ·
                refine ⟨2941559509393817443099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 251013078134939088477781 2941559509393817443099)
                ·
                  rfl

theorem cell23_154674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 8].length) (baseStart_154674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154674 prefixEnd_154674 := by exact prefixLift 154674
  have htrace : WordTrace (prefixWord ++ tailWord_154674) baseStart_154674 baseEnd_154674 := by
    simpa [prefixWord, tailWord_154674, baseEnd_154674] using wordTrace_append hprefix tailTrace_154674
  have hstable : (prefixWord ++ tailWord_154674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154674).length < 2 ^ (prefixWord ++ tailWord_154674).sum := by decide
  have hdescent : baseEnd_154674 < baseStart_154674 := by decide
  rcases family_descends (prefixWord ++ tailWord_154674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154744 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_154744 : Nat := 118140960795 + 154744 * 2 ^ 59
def prefixEnd_154744 : Nat := 4983230072969 + 3 ^ 40 * 154744 * 2
def baseEnd_154744 : Nat := 79458050399447797088351

theorem tailTrace_154744 : CollatzResearch.WordTrace tailWord_154744 prefixEnd_154744 79458050399447797088351 := by
  unfold tailWord_154744
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821988675698195508127643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3762651567597594010836857 2821988675698195508127643)
  ·
    refine ⟨4232983013547293262191465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2821988675698195508127643 4232983013547293262191465)
    ·
      refine ⟨3174737260160469946643599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4232983013547293262191465 3174737260160469946643599)
      ·
        refine ⟨4762105890240704919965399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3174737260160469946643599 4762105890240704919965399)
        ·
          refine ⟨7143158835361057379948099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4762105890240704919965399 7143158835361057379948099)
          ·
            refine ⟨10714738253041586069922149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7143158835361057379948099 10714738253041586069922149)
            ·
              refine ⟨2009013422445297388110403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10714738253041586069922149 2009013422445297388110403)
              ·
                refine ⟨3013520133667946082165605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009013422445297388110403 3013520133667946082165605)
                ·
                  refine ⟨565035025062739890406051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3013520133667946082165605 565035025062739890406051)
                  ·
                    refine ⟨847552537594109835609077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 565035025062739890406051 847552537594109835609077)
                    ·
                      refine ⟨79458050399447797088351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 847552537594109835609077 79458050399447797088351)
                      ·
                        rfl

theorem cell23_154744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_154744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154744 prefixEnd_154744 := by exact prefixLift 154744
  have htrace : WordTrace (prefixWord ++ tailWord_154744) baseStart_154744 baseEnd_154744 := by
    simpa [prefixWord, tailWord_154744, baseEnd_154744] using wordTrace_append hprefix tailTrace_154744
  have hstable : (prefixWord ++ tailWord_154744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154744).length < 2 ^ (prefixWord ++ tailWord_154744).sum := by decide
  have hdescent : baseEnd_154744 < baseStart_154744 := by decide
  rcases family_descends (prefixWord ++ tailWord_154744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154775 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 4, 2, 2]
def baseStart_154775 : Nat := 118140960795 + 154775 * 2 ^ 59
def prefixEnd_154775 : Nat := 4983230072969 + 3 ^ 40 * 154775 * 2
def baseEnd_154775 : Nat := 79473968299737175800709

theorem tailTrace_154775 : CollatzResearch.WordTrace tailWord_154775 prefixEnd_154775 79473968299737175800709 := by
  unfold tailWord_154775
  simp only [CollatzResearch.WordTrace]
  refine ⟨5645108014284083310633779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3763405342856055540422519 5645108014284083310633779)
  ·
    refine ⟨8467662021426124965950669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5645108014284083310633779 8467662021426124965950669)
    ·
      refine ⟨3175373258034796862231501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8467662021426124965950669 3175373258034796862231501)
      ·
        refine ⟨1190764971763048823336813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3175373258034796862231501 1190764971763048823336813)
        ·
          refine ⟨446536864411143308751305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1190764971763048823336813 446536864411143308751305)
          ·
            refine ⟨334902648308357481563479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446536864411143308751305 334902648308357481563479)
            ·
              refine ⟨502353972462536222345219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334902648308357481563479 502353972462536222345219)
              ·
                refine ⟨753530958693804333517829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502353972462536222345219 753530958693804333517829)
                ·
                  refine ⟨141287054755088312534593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 753530958693804333517829 141287054755088312534593)
                  ·
                    refine ⟨105965291066316234400945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141287054755088312534593 105965291066316234400945)
                    ·
                      refine ⟨79473968299737175800709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 105965291066316234400945 79473968299737175800709)
                      ·
                        rfl

theorem cell23_154775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_154775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154775 prefixEnd_154775 := by exact prefixLift 154775
  have htrace : WordTrace (prefixWord ++ tailWord_154775) baseStart_154775 baseEnd_154775 := by
    simpa [prefixWord, tailWord_154775, baseEnd_154775] using wordTrace_append hprefix tailTrace_154775
  have hstable : (prefixWord ++ tailWord_154775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154775).length < 2 ^ (prefixWord ++ tailWord_154775).sum := by decide
  have hdescent : baseEnd_154775 < baseStart_154775 := by decide
  rcases family_descends (prefixWord ++ tailWord_154775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154781 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 7]
def baseStart_154781 : Nat := 118140960795 + 154781 * 2 ^ 59
def prefixEnd_154781 : Nat := 4983230072969 + 3 ^ 40 * 154781 * 2
def baseEnd_154781 : Nat := 8830783242629350258409

theorem tailTrace_154781 : CollatzResearch.WordTrace tailWord_154781 prefixEnd_154781 8830783242629350258409 := by
  unfold tailWord_154781
  simp only [CollatzResearch.WordTrace]
  refine ⟨5645326852262346335352197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3763551234841564223568131 5645326852262346335352197)
  ·
    refine ⟨1058498784799189937878537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5645326852262346335352197 1058498784799189937878537)
    ·
      refine ⟨793874088599392453408903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1058498784799189937878537 793874088599392453408903)
      ·
        refine ⟨1190811132899088680113355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793874088599392453408903 1190811132899088680113355)
        ·
          refine ⟨1786216699348633020170033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190811132899088680113355 1786216699348633020170033)
          ·
            refine ⟨1339662524511474765127525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1786216699348633020170033 1339662524511474765127525)
            ·
              refine ⟨251186723345901518461411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1339662524511474765127525 251186723345901518461411)
              ·
                refine ⟨376780085018852277692117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251186723345901518461411 376780085018852277692117)
                ·
                  refine ⟨8830783242629350258409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 376780085018852277692117 8830783242629350258409)
                  ·
                    rfl

theorem cell23_154781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_154781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154781 prefixEnd_154781 := by exact prefixLift 154781
  have htrace : WordTrace (prefixWord ++ tailWord_154781) baseStart_154781 baseEnd_154781 := by
    simpa [prefixWord, tailWord_154781, baseEnd_154781] using wordTrace_append hprefix tailTrace_154781
  have hstable : (prefixWord ++ tailWord_154781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154781).length < 2 ^ (prefixWord ++ tailWord_154781).sum := by decide
  have hdescent : baseEnd_154781 < baseStart_154781 := by decide
  rcases family_descends (prefixWord ++ tailWord_154781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154892 : List Nat := [2, 2, 1, 2, 2, 3, 4, 2, 1, 4]
def baseStart_154892 : Nat := 118140960795 + 154892 * 2 ^ 59
def prefixEnd_154892 : Nat := 4983230072969 + 3 ^ 40 * 154892 * 2
def baseEnd_154892 : Nat := 26511348512104406012557

theorem tailTrace_154892 : CollatzResearch.WordTrace tailWord_154892 prefixEnd_154892 26511348512104406012557 := by
  unfold tailWord_154892
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824687677430106146321465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3766250236573474861761953 2824687677430106146321465)
  ·
    refine ⟨2118515758072579609741099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2824687677430106146321465 2118515758072579609741099)
    ·
      refine ⟨3177773637108869414611649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2118515758072579609741099 3177773637108869414611649)
      ·
        refine ⟨2383330227831652060958737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3177773637108869414611649 2383330227831652060958737)
        ·
          refine ⟨1787497670873739045719053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2383330227831652060958737 1787497670873739045719053)
          ·
            refine ⟨670311626577652142144645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1787497670873739045719053 670311626577652142144645)
            ·
              refine ⟨125683429983309776652121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 670311626577652142144645 125683429983309776652121)
              ·
                refine ⟨94262572487482332489091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125683429983309776652121 94262572487482332489091)
                ·
                  refine ⟨141393858731223498733637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94262572487482332489091 141393858731223498733637)
                  ·
                    refine ⟨26511348512104406012557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141393858731223498733637 26511348512104406012557)
                    ·
                      rfl

theorem cell23_154892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_154892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154892 prefixEnd_154892 := by exact prefixLift 154892
  have htrace : WordTrace (prefixWord ++ tailWord_154892) baseStart_154892 baseEnd_154892 := by
    simpa [prefixWord, tailWord_154892, baseEnd_154892] using wordTrace_append hprefix tailTrace_154892
  have hstable : (prefixWord ++ tailWord_154892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154892).length < 2 ^ (prefixWord ++ tailWord_154892).sum := by decide
  have hdescent : baseEnd_154892 < baseStart_154892 := by decide
  rcases family_descends (prefixWord ++ tailWord_154892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154915 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 3, 1, 3]
def baseStart_154915 : Nat := 118140960795 + 154915 * 2 ^ 59
def prefixEnd_154915 : Nat := 4983230072969 + 3 ^ 40 * 154915 * 2
def baseEnd_154915 : Nat := 79545855591366628050065

theorem tailTrace_154915 : CollatzResearch.WordTrace tailWord_154915 prefixEnd_154915 79545855591366628050065 := by
  unfold tailWord_154915
  simp only [CollatzResearch.WordTrace]
  refine ⟨5650214233776887220730199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3766809489184591480486799 5650214233776887220730199)
  ·
    refine ⟨8475321350665330831095299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5650214233776887220730199 8475321350665330831095299)
    ·
      refine ⟨12712982025997996246642949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8475321350665330831095299 12712982025997996246642949)
      ·
        refine ⟨2383684129874624296245553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12712982025997996246642949 2383684129874624296245553)
        ·
          refine ⟨1787763097405968222184165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2383684129874624296245553 1787763097405968222184165)
          ·
            refine ⟨335205580763619041659531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1787763097405968222184165 335205580763619041659531)
            ·
              refine ⟨502808371145428562489297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335205580763619041659531 502808371145428562489297)
              ·
                refine ⟨377106278359071421866973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502808371145428562489297 377106278359071421866973)
                ·
                  refine ⟨141414854384651783200115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377106278359071421866973 141414854384651783200115)
                  ·
                    refine ⟨212122281576977674800173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 141414854384651783200115 212122281576977674800173)
                    ·
                      refine ⟨79545855591366628050065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 212122281576977674800173 79545855591366628050065)
                      ·
                        rfl

theorem cell23_154915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_154915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154915 prefixEnd_154915 := by exact prefixLift 154915
  have htrace : WordTrace (prefixWord ++ tailWord_154915) baseStart_154915 baseEnd_154915 := by
    simpa [prefixWord, tailWord_154915, baseEnd_154915] using wordTrace_append hprefix tailTrace_154915
  have hstable : (prefixWord ++ tailWord_154915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154915).length < 2 ^ (prefixWord ++ tailWord_154915).sum := by decide
  have hdescent : baseEnd_154915 < baseStart_154915 := by decide
  rcases family_descends (prefixWord ++ tailWord_154915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154958 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_154958 : Nat := 118140960795 + 154958 * 2 ^ 59
def prefixEnd_154958 : Nat := 4983230072969 + 3 ^ 40 * 154958 * 2
def baseEnd_154958 : Nat := 79567935259509959812367

theorem tailTrace_154958 : CollatzResearch.WordTrace tailWord_154958 prefixEnd_154958 79567935259509959812367 := by
  unfold tailWord_154958
  simp only [CollatzResearch.WordTrace]
  refine ⟨706472821577638195568191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3767855048414070376363685 706472821577638195568191)
  ·
    refine ⟨1059709232366457293352287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 706472821577638195568191 1059709232366457293352287)
    ·
      refine ⟨1589563848549685940028431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1059709232366457293352287 1589563848549685940028431)
      ·
        refine ⟨2384345772824528910042647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1589563848549685940028431 2384345772824528910042647)
        ·
          refine ⟨3576518659236793365063971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384345772824528910042647 3576518659236793365063971)
          ·
            refine ⟨5364777988855190047595957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576518659236793365063971 5364777988855190047595957)
            ·
              refine ⟨502947936455174066962121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5364777988855190047595957 502947936455174066962121)
              ·
                refine ⟨377210952341380550221591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502947936455174066962121 377210952341380550221591)
                ·
                  refine ⟨565816428512070825332387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377210952341380550221591 565816428512070825332387)
                  ·
                    refine ⟨848724642768106237998581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 565816428512070825332387 848724642768106237998581)
                    ·
                      refine ⟨79567935259509959812367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 848724642768106237998581 79567935259509959812367)
                      ·
                        rfl

theorem cell23_154958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_154958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154958 prefixEnd_154958 := by exact prefixLift 154958
  have htrace : WordTrace (prefixWord ++ tailWord_154958) baseStart_154958 baseEnd_154958 := by
    simpa [prefixWord, tailWord_154958, baseEnd_154958] using wordTrace_append hprefix tailTrace_154958
  have hstable : (prefixWord ++ tailWord_154958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154958).length < 2 ^ (prefixWord ++ tailWord_154958).sum := by decide
  have hdescent : baseEnd_154958 < baseStart_154958 := by decide
  rcases family_descends (prefixWord ++ tailWord_154958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154961 : List Nat := [1, 2, 2, 1, 4, 1, 2, 10]
def baseStart_154961 : Nat := 118140960795 + 154961 * 2 ^ 59
def prefixEnd_154961 : Nat := 4983230072969 + 3 ^ 40 * 154961 * 2
def baseEnd_154961 : Nat := 2947017618573090669439

theorem tailTrace_154961 : CollatzResearch.WordTrace tailWord_154961 prefixEnd_154961 2947017618573090669439 := by
  unfold tailWord_154961
  simp only [CollatzResearch.WordTrace]
  refine ⟨5651891991610237076904737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3767927994406824717936491 5651891991610237076904737)
  ·
    refine ⟨4238918993707677807678553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5651891991610237076904737 4238918993707677807678553)
    ·
      refine ⟨3179189245280758355758915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4238918993707677807678553 3179189245280758355758915)
      ·
        refine ⟨4768783867921137533638373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3179189245280758355758915 4768783867921137533638373)
        ·
          refine ⟨894146975235213287557195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4768783867921137533638373 894146975235213287557195)
          ·
            refine ⟨1341220462852819931335793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894146975235213287557195 1341220462852819931335793)
            ·
              refine ⟨1005915347139614948501845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1341220462852819931335793 1005915347139614948501845)
              ·
                refine ⟨2947017618573090669439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1005915347139614948501845 2947017618573090669439)
                ·
                  rfl

theorem cell23_154961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 10].length) (baseStart_154961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154961 prefixEnd_154961 := by exact prefixLift 154961
  have htrace : WordTrace (prefixWord ++ tailWord_154961) baseStart_154961 baseEnd_154961 := by
    simpa [prefixWord, tailWord_154961, baseEnd_154961] using wordTrace_append hprefix tailTrace_154961
  have hstable : (prefixWord ++ tailWord_154961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154961).length < 2 ^ (prefixWord ++ tailWord_154961).sum := by decide
  have hdescent : baseEnd_154961 < baseStart_154961 := by decide
  rcases family_descends (prefixWord ++ tailWord_154961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154965 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 1, 6]
def baseStart_154965 : Nat := 118140960795 + 154965 * 2 ^ 59
def prefixEnd_154965 : Nat := 4983230072969 + 3 ^ 40 * 154965 * 2
def baseEnd_154965 : Nat := 26523843208030477474945

theorem tailTrace_154965 : CollatzResearch.WordTrace tailWord_154965 prefixEnd_154965 26523843208030477474945 := by
  unfold tailWord_154965
  simp only [CollatzResearch.WordTrace]
  refine ⟨5652037883595745760050349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3768025255730497173366899 5652037883595745760050349)
  ·
    refine ⟨2119514206348404660018881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5652037883595745760050349 2119514206348404660018881)
    ·
      refine ⟨1589635654761303495014161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2119514206348404660018881 1589635654761303495014161)
      ·
        refine ⟨1192226741070977621260621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1589635654761303495014161 1192226741070977621260621)
        ·
          refine ⟨447085027901616607972733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1192226741070977621260621 447085027901616607972733)
          ·
            refine ⟨167656885463106227989775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 447085027901616607972733 167656885463106227989775)
            ·
              refine ⟨251485328194659341984663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167656885463106227989775 251485328194659341984663)
              ·
                refine ⟨377227992291989012976995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251485328194659341984663 377227992291989012976995)
                ·
                  refine ⟨565841988437983519465493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377227992291989012976995 565841988437983519465493)
                  ·
                    refine ⟨26523843208030477474945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 565841988437983519465493 26523843208030477474945)
                    ·
                      rfl

theorem cell23_154965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_154965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154965 prefixEnd_154965 := by exact prefixLift 154965
  have htrace : WordTrace (prefixWord ++ tailWord_154965) baseStart_154965 baseEnd_154965 := by
    simpa [prefixWord, tailWord_154965, baseEnd_154965] using wordTrace_append hprefix tailTrace_154965
  have hstable : (prefixWord ++ tailWord_154965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154965).length < 2 ^ (prefixWord ++ tailWord_154965).sum := by decide
  have hdescent : baseEnd_154965 < baseStart_154965 := by decide
  rcases family_descends (prefixWord ++ tailWord_154965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154978 : List Nat := [3, 3, 2, 1, 1, 1, 3, 9]
def baseStart_154978 : Nat := 118140960795 + 154978 * 2 ^ 59
def prefixEnd_154978 : Nat := 4983230072969 + 3 ^ 40 * 154978 * 2
def baseEnd_154978 : Nat := 2947340921207403020825

theorem tailTrace_154978 : CollatzResearch.WordTrace tailWord_154978 prefixEnd_154978 2947340921207403020825 := by
  unfold tailWord_154978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413128008137162245068397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3768341355032432653515725 1413128008137162245068397)
  ·
    refine ⟨529923003051435841900649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1413128008137162245068397 529923003051435841900649)
    ·
      refine ⟨397442252288576881425487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 529923003051435841900649 397442252288576881425487)
      ·
        refine ⟨596163378432865322138231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397442252288576881425487 596163378432865322138231)
        ·
          refine ⟨894245067649297983207347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596163378432865322138231 894245067649297983207347)
          ·
            refine ⟨1341367601473946974811021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894245067649297983207347 1341367601473946974811021)
            ·
              refine ⟨503012850552730115554133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1341367601473946974811021 503012850552730115554133)
              ·
                refine ⟨2947340921207403020825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 503012850552730115554133 2947340921207403020825)
                ·
                  rfl

theorem cell23_154978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 9].length) (baseStart_154978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_154978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_154978 prefixEnd_154978 := by exact prefixLift 154978
  have htrace : WordTrace (prefixWord ++ tailWord_154978) baseStart_154978 baseEnd_154978 := by
    simpa [prefixWord, tailWord_154978, baseEnd_154978] using wordTrace_append hprefix tailTrace_154978
  have hstable : (prefixWord ++ tailWord_154978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154978).length < 2 ^ (prefixWord ++ tailWord_154978).sum := by decide
  have hdescent : baseEnd_154978 < baseStart_154978 := by decide
  rcases family_descends (prefixWord ++ tailWord_154978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155005 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_155005 : Nat := 118140960795 + 155005 * 2 ^ 59
def prefixEnd_155005 : Nat := 4983230072969 + 3 ^ 40 * 155005 * 2
def baseEnd_155005 : Nat := 79592068850271275924651

theorem tailTrace_155005 : CollatzResearch.WordTrace tailWord_155005 prefixEnd_155005 79592068850271275924651 := by
  unfold tailWord_155005
  simp only [CollatzResearch.WordTrace]
  refine ⟨5653496803450832591506469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3768997868967221727670979 5653496803450832591506469)
  ·
    refine ⟨1060030650647031110907463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5653496803450832591506469 1060030650647031110907463)
    ·
      refine ⟨1590045975970546666361195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060030650647031110907463 1590045975970546666361195)
      ·
        refine ⟨2385068963955819999541793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590045975970546666361195 2385068963955819999541793)
        ·
          refine ⟨1788801722966864999656345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2385068963955819999541793 1788801722966864999656345)
          ·
            refine ⟨1341601292225148749742259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1788801722966864999656345 1341601292225148749742259)
            ·
              refine ⟨2012401938337723124613389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341601292225148749742259 2012401938337723124613389)
              ·
                refine ⟨754650726876646171730021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2012401938337723124613389 754650726876646171730021)
                ·
                  refine ⟨141497011289371157199379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754650726876646171730021 141497011289371157199379)
                  ·
                    refine ⟨212245516934056735799069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 141497011289371157199379 212245516934056735799069)
                    ·
                      refine ⟨79592068850271275924651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 212245516934056735799069 79592068850271275924651)
                      ·
                        rfl

theorem cell23_155005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_155005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155005 prefixEnd_155005 := by exact prefixLift 155005
  have htrace : WordTrace (prefixWord ++ tailWord_155005) baseStart_155005 baseEnd_155005 := by
    simpa [prefixWord, tailWord_155005, baseEnd_155005] using wordTrace_append hprefix tailTrace_155005
  have hstable : (prefixWord ++ tailWord_155005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155005).length < 2 ^ (prefixWord ++ tailWord_155005).sum := by decide
  have hdescent : baseEnd_155005 < baseStart_155005 := by decide
  rcases family_descends (prefixWord ++ tailWord_155005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155026 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_155026 : Nat := 118140960795 + 155026 * 2 ^ 59
def prefixEnd_155026 : Nat := 4983230072969 + 3 ^ 40 * 155026 * 2
def baseEnd_155026 : Nat := 79602851944015693762055

theorem tailTrace_155026 : CollatzResearch.WordTrace tailWord_155026 prefixEnd_155026 79602851944015693762055 := by
  unfold tailWord_155026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413565684093688294505233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3769508490916502118680621 1413565684093688294505233)
  ·
    refine ⟨1060174263070266220878925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1413565684093688294505233 1060174263070266220878925)
    ·
      refine ⟨397565348651349832829597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1060174263070266220878925 397565348651349832829597)
      ·
        refine ⟨149087005744256187311099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397565348651349832829597 149087005744256187311099)
        ·
          refine ⟨223630508616384280966649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149087005744256187311099 223630508616384280966649)
          ·
            refine ⟨167722881462288210724987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223630508616384280966649 167722881462288210724987)
            ·
              refine ⟨251584322193432316087481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167722881462288210724987 251584322193432316087481)
              ·
                refine ⟨188688241645074237065611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251584322193432316087481 188688241645074237065611)
                ·
                  refine ⟨283032362467611355598417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188688241645074237065611 283032362467611355598417)
                  ·
                    refine ⟨212274271850708516698813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 283032362467611355598417 212274271850708516698813)
                    ·
                      refine ⟨79602851944015693762055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 212274271850708516698813 79602851944015693762055)
                      ·
                        rfl

theorem cell23_155026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_155026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155026 prefixEnd_155026 := by exact prefixLift 155026
  have htrace : WordTrace (prefixWord ++ tailWord_155026) baseStart_155026 baseEnd_155026 := by
    simpa [prefixWord, tailWord_155026, baseEnd_155026] using wordTrace_append hprefix tailTrace_155026
  have hstable : (prefixWord ++ tailWord_155026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155026).length < 2 ^ (prefixWord ++ tailWord_155026).sum := by decide
  have hdescent : baseEnd_155026 < baseStart_155026 := by decide
  rcases family_descends (prefixWord ++ tailWord_155026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155108 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_155108 : Nat := 118140960795 + 155108 * 2 ^ 59
def prefixEnd_155108 : Nat := 4983230072969 + 3 ^ 40 * 155108 * 2
def baseEnd_155108 : Nat := 79644957357684372936677

theorem tailTrace_155108 : CollatzResearch.WordTrace tailWord_155108 prefixEnd_155108 79644957357684372936677 := by
  unfold tailWord_155108
  simp only [CollatzResearch.WordTrace]
  refine ⟨2828626761038840591252989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3771502348051787455003985 2828626761038840591252989)
  ·
    refine ⟨1060735035389565221719871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2828626761038840591252989 1060735035389565221719871)
    ·
      refine ⟨1591102553084347832579807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060735035389565221719871 1591102553084347832579807)
      ·
        refine ⟨2386653829626521748869711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1591102553084347832579807 2386653829626521748869711)
        ·
          refine ⟨3579980744439782623304567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2386653829626521748869711 3579980744439782623304567)
          ·
            refine ⟨5369971116659673934956851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3579980744439782623304567 5369971116659673934956851)
            ·
              refine ⟨8054956674989510902435277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5369971116659673934956851 8054956674989510902435277)
              ·
                refine ⟨3020608753121066588413229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8054956674989510902435277 3020608753121066588413229)
                ·
                  refine ⟨1132728282420399970654961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3020608753121066588413229 1132728282420399970654961)
                  ·
                    refine ⟨849546211815299977991221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1132728282420399970654961 849546211815299977991221)
                    ·
                      refine ⟨79644957357684372936677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 849546211815299977991221 79644957357684372936677)
                      ·
                        rfl

theorem cell23_155108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_155108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155108 prefixEnd_155108 := by exact prefixLift 155108
  have htrace : WordTrace (prefixWord ++ tailWord_155108) baseStart_155108 baseEnd_155108 := by
    simpa [prefixWord, tailWord_155108, baseEnd_155108] using wordTrace_append hprefix tailTrace_155108
  have hstable : (prefixWord ++ tailWord_155108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155108).length < 2 ^ (prefixWord ++ tailWord_155108).sum := by decide
  have hdescent : baseEnd_155108 < baseStart_155108 := by decide
  rcases family_descends (prefixWord ++ tailWord_155108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155135 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 1, 6, 2]
def baseStart_155135 : Nat := 118140960795 + 155135 * 2 ^ 59
def prefixEnd_155135 : Nat := 4983230072969 + 3 ^ 40 * 155135 * 2
def baseEnd_155135 : Nat := 79658821335355767299053

theorem tailTrace_155135 : CollatzResearch.WordTrace tailWord_155135 prefixEnd_155135 79658821335355767299053 := by
  unfold tailWord_155135
  simp only [CollatzResearch.WordTrace]
  refine ⟨5658238292979864793738859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3772158861986576529159239 5658238292979864793738859)
  ·
    refine ⟨8487357439469797190608289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5658238292979864793738859 8487357439469797190608289)
    ·
      refine ⟨6365518079602347892956217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8487357439469797190608289 6365518079602347892956217)
      ·
        refine ⟨4774138559701760919717163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6365518079602347892956217 4774138559701760919717163)
        ·
          refine ⟨7161207839552641379575745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4774138559701760919717163 7161207839552641379575745)
          ·
            refine ⟨5370905879664481034681809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7161207839552641379575745 5370905879664481034681809)
            ·
              refine ⟨4028179409748360776011357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5370905879664481034681809 4028179409748360776011357)
              ·
                refine ⟨1510567278655635291004259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4028179409748360776011357 1510567278655635291004259)
                ·
                  refine ⟨2265850917983452936506389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510567278655635291004259 2265850917983452936506389)
                  ·
                    refine ⟨106211761780474356398737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2265850917983452936506389 106211761780474356398737)
                    ·
                      refine ⟨79658821335355767299053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 106211761780474356398737 79658821335355767299053)
                      ·
                        rfl

theorem cell23_155135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 6, 2].length) (baseStart_155135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155135 prefixEnd_155135 := by exact prefixLift 155135
  have htrace : WordTrace (prefixWord ++ tailWord_155135) baseStart_155135 baseEnd_155135 := by
    simpa [prefixWord, tailWord_155135, baseEnd_155135] using wordTrace_append hprefix tailTrace_155135
  have hstable : (prefixWord ++ tailWord_155135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155135).length < 2 ^ (prefixWord ++ tailWord_155135).sum := by decide
  have hdescent : baseEnd_155135 < baseStart_155135 := by decide
  rcases family_descends (prefixWord ++ tailWord_155135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155145 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 3, 4]
def baseStart_155145 : Nat := 118140960795 + 155145 * 2 ^ 59
def prefixEnd_155145 : Nat := 4983230072969 + 3 ^ 40 * 155145 * 2
def baseEnd_155145 : Nat := 26554652047300242724669

theorem tailTrace_155145 : CollatzResearch.WordTrace tailWord_155145 prefixEnd_155145 26554652047300242724669 := by
  unfold tailWord_155145
  simp only [CollatzResearch.WordTrace]
  refine ⟨5658603022943636501602889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3772402015295757667735259 5658603022943636501602889)
  ·
    refine ⟨4243952267207727376202167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5658603022943636501602889 4243952267207727376202167)
    ·
      refine ⟨6365928400811591064303251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4243952267207727376202167 6365928400811591064303251)
      ·
        refine ⟨9548892601217386596454877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6365928400811591064303251 9548892601217386596454877)
        ·
          refine ⟨3580834725456519973670579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9548892601217386596454877 3580834725456519973670579)
          ·
            refine ⟨5371252088184779960505869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3580834725456519973670579 5371252088184779960505869)
            ·
              refine ⟨2014219533069292485189701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5371252088184779960505869 2014219533069292485189701)
              ·
                refine ⟨377666162450492340973069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2014219533069292485189701 377666162450492340973069)
                ·
                  refine ⟨141624810918934627864901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377666162450492340973069 141624810918934627864901)
                  ·
                    refine ⟨26554652047300242724669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141624810918934627864901 26554652047300242724669)
                    ·
                      rfl

theorem cell23_155145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 4].length) (baseStart_155145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155145 prefixEnd_155145 := by exact prefixLift 155145
  have htrace : WordTrace (prefixWord ++ tailWord_155145) baseStart_155145 baseEnd_155145 := by
    simpa [prefixWord, tailWord_155145, baseEnd_155145] using wordTrace_append hprefix tailTrace_155145
  have hstable : (prefixWord ++ tailWord_155145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155145).length < 2 ^ (prefixWord ++ tailWord_155145).sum := by decide
  have hdescent : baseEnd_155145 < baseStart_155145 := by decide
  rcases family_descends (prefixWord ++ tailWord_155145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155155 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 3]
def baseStart_155155 : Nat := 118140960795 + 155155 * 2 ^ 59
def prefixEnd_155155 : Nat := 4983230072969 + 3 ^ 40 * 155155 * 2
def baseEnd_155155 : Nat := 79669090948445689048961

theorem tailTrace_155155 : CollatzResearch.WordTrace tailWord_155155 prefixEnd_155155 79669090948445689048961 := by
  unfold tailWord_155155
  simp only [CollatzResearch.WordTrace]
  refine ⟨5658967752907408209466919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3772645168604938806311279 5658967752907408209466919)
  ·
    refine ⟨8488451629361112314200379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5658967752907408209466919 8488451629361112314200379)
    ·
      refine ⟨12732677444041668471300569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8488451629361112314200379 12732677444041668471300569)
      ·
        refine ⟨9549508083031251353475427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12732677444041668471300569 9549508083031251353475427)
        ·
          refine ⟨14324262124546877030213141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9549508083031251353475427 14324262124546877030213141)
          ·
            refine ⟨671449787088134860791241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14324262124546877030213141 671449787088134860791241)
            ·
              refine ⟨503587340316101145593431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 671449787088134860791241 503587340316101145593431)
              ·
                refine ⟨755381010474151718390147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503587340316101145593431 755381010474151718390147)
                ·
                  refine ⟨1133071515711227577585221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755381010474151718390147 1133071515711227577585221)
                  ·
                    refine ⟨212450909195855170797229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1133071515711227577585221 212450909195855170797229)
                    ·
                      refine ⟨79669090948445689048961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 212450909195855170797229 79669090948445689048961)
                      ·
                        rfl

theorem cell23_155155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 3].length) (baseStart_155155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155155 prefixEnd_155155 := by exact prefixLift 155155
  have htrace : WordTrace (prefixWord ++ tailWord_155155) baseStart_155155 baseEnd_155155 := by
    simpa [prefixWord, tailWord_155155, baseEnd_155155] using wordTrace_append hprefix tailTrace_155155
  have hstable : (prefixWord ++ tailWord_155155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155155).length < 2 ^ (prefixWord ++ tailWord_155155).sum := by decide
  have hdescent : baseEnd_155155 < baseStart_155155 := by decide
  rcases family_descends (prefixWord ++ tailWord_155155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155192 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 6]
def baseStart_155192 : Nat := 118140960795 + 155192 * 2 ^ 59
def prefixEnd_155192 : Nat := 4983230072969 + 3 ^ 40 * 155192 * 2
def baseEnd_155192 : Nat := 8854232192518004920699

theorem tailTrace_155192 : CollatzResearch.WordTrace tailWord_155192 prefixEnd_155192 8854232192518004920699 := by
  unfold tailWord_155192
  simp only [CollatzResearch.WordTrace]
  refine ⟨2830158626886681764281915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3773544835848909019042553 2830158626886681764281915)
  ·
    refine ⟨4245237940330022646422873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2830158626886681764281915 4245237940330022646422873)
    ·
      refine ⟨3183928455247516984817155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4245237940330022646422873 3183928455247516984817155)
      ·
        refine ⟨4775892682871275477225733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3183928455247516984817155 4775892682871275477225733)
        ·
          refine ⟨895479878038364151979825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4775892682871275477225733 895479878038364151979825)
          ·
            refine ⟨671609908528773113984869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 895479878038364151979825 671609908528773113984869)
            ·
              refine ⟨125926857849144958872163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 671609908528773113984869 125926857849144958872163)
              ·
                refine ⟨188890286773717438308245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125926857849144958872163 188890286773717438308245)
                ·
                  refine ⟨8854232192518004920699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 188890286773717438308245 8854232192518004920699)
                  ·
                    rfl

theorem cell23_155192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 6].length) (baseStart_155192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155192 prefixEnd_155192 := by exact prefixLift 155192
  have htrace : WordTrace (prefixWord ++ tailWord_155192) baseStart_155192 baseEnd_155192 := by
    simpa [prefixWord, tailWord_155192, baseEnd_155192] using wordTrace_append hprefix tailTrace_155192
  have hstable : (prefixWord ++ tailWord_155192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155192).length < 2 ^ (prefixWord ++ tailWord_155192).sum := by decide
  have hdescent : baseEnd_155192 < baseStart_155192 := by decide
  rcases family_descends (prefixWord ++ tailWord_155192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155205 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_155205 : Nat := 118140960795 + 155205 * 2 ^ 59
def prefixEnd_155205 : Nat := 4983230072969 + 3 ^ 40 * 155205 * 2
def baseEnd_155205 : Nat := 26564921660390164474577

theorem tailTrace_155205 : CollatzResearch.WordTrace tailWord_155205 prefixEnd_155205 26564921660390164474577 := by
  unfold tailWord_155205
  simp only [CollatzResearch.WordTrace]
  refine ⟨5660791402726266748787069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3773860935150844499191379 5660791402726266748787069)
  ·
    refine ⟨2122796776022350030795151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5660791402726266748787069 2122796776022350030795151)
    ·
      refine ⟨3184195164033525046192727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2122796776022350030795151 3184195164033525046192727)
      ·
        refine ⟨4776292746050287569289091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184195164033525046192727 4776292746050287569289091)
        ·
          refine ⟨7164439119075431353933637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776292746050287569289091 7164439119075431353933637)
          ·
            refine ⟨1343332334826643378862557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7164439119075431353933637 1343332334826643378862557)
            ·
              refine ⟨503749625559991267073459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1343332334826643378862557 503749625559991267073459)
              ·
                refine ⟨755624438339986900610189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503749625559991267073459 755624438339986900610189)
                ·
                  refine ⟨283359164377495087728821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755624438339986900610189 283359164377495087728821)
                  ·
                    refine ⟨26564921660390164474577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 283359164377495087728821 26564921660390164474577)
                    ·
                      rfl

theorem cell23_155205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_155205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155205 prefixEnd_155205 := by exact prefixLift 155205
  have htrace : WordTrace (prefixWord ++ tailWord_155205) baseStart_155205 baseEnd_155205 := by
    simpa [prefixWord, tailWord_155205, baseEnd_155205] using wordTrace_append hprefix tailTrace_155205
  have hstable : (prefixWord ++ tailWord_155205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155205).length < 2 ^ (prefixWord ++ tailWord_155205).sum := by decide
  have hdescent : baseEnd_155205 < baseStart_155205 := by decide
  rcases family_descends (prefixWord ++ tailWord_155205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155236 : List Nat := [2, 3, 1, 1, 2, 4, 1, 4, 1, 1, 3]
def baseStart_155236 : Nat := 118140960795 + 155236 * 2 ^ 59
def prefixEnd_155236 : Nat := 4983230072969 + 3 ^ 40 * 155236 * 2
def baseEnd_155236 : Nat := 79710682881459872136089

theorem tailTrace_155236 : CollatzResearch.WordTrace tailWord_155236 prefixEnd_155236 79710682881459872136089 := by
  unfold tailWord_155236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2830961032806979521582781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3774614710409306028777041 2830961032806979521582781)
  ·
    refine ⟨1061610387302617320593543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2830961032806979521582781 1061610387302617320593543)
    ·
      refine ⟨1592415580953925980890315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1061610387302617320593543 1592415580953925980890315)
      ·
        refine ⟨2388623371430888971335473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592415580953925980890315 2388623371430888971335473)
        ·
          refine ⟨1791467528573166728501605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2388623371430888971335473 1791467528573166728501605)
          ·
            refine ⟨335900161607468761594051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1791467528573166728501605 335900161607468761594051)
            ·
              refine ⟨503850242411203142391077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335900161607468761594051 503850242411203142391077)
              ·
                refine ⟨94471920452100589198327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 503850242411203142391077 94471920452100589198327)
                ·
                  refine ⟨141707880678150883797491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94471920452100589198327 141707880678150883797491)
                  ·
                    refine ⟨212561821017226325696237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 141707880678150883797491 212561821017226325696237)
                    ·
                      refine ⟨79710682881459872136089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 212561821017226325696237 79710682881459872136089)
                      ·
                        rfl

theorem cell23_155236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_155236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155236 prefixEnd_155236 := by exact prefixLift 155236
  have htrace : WordTrace (prefixWord ++ tailWord_155236) baseStart_155236 baseEnd_155236 := by
    simpa [prefixWord, tailWord_155236, baseEnd_155236] using wordTrace_append hprefix tailTrace_155236
  have hstable : (prefixWord ++ tailWord_155236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155236).length < 2 ^ (prefixWord ++ tailWord_155236).sum := by decide
  have hdescent : baseEnd_155236 < baseStart_155236 := by decide
  rcases family_descends (prefixWord ++ tailWord_155236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155242 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_155242 : Nat := 118140960795 + 155242 * 2 ^ 59
def prefixEnd_155242 : Nat := 4983230072969 + 3 ^ 40 * 155242 * 2
def baseEnd_155242 : Nat := 79713763765386848661061

theorem tailTrace_155242 : CollatzResearch.WordTrace tailWord_155242 prefixEnd_155242 79713763765386848661061 := by
  unfold tailWord_155242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415535225898055516970995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3774760602394814711922653 1415535225898055516970995)
  ·
    refine ⟨2123302838847083275456493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1415535225898055516970995 2123302838847083275456493)
    ·
      refine ⟨796238564567656228296185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2123302838847083275456493 796238564567656228296185)
      ·
        refine ⟨597178923425742171222139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 796238564567656228296185 597178923425742171222139)
        ·
          refine ⟨895768385138613256833209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597178923425742171222139 895768385138613256833209)
          ·
            refine ⟨671826288853959942624907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 895768385138613256833209 671826288853959942624907)
            ·
              refine ⟨1007739433280939913937361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671826288853959942624907 1007739433280939913937361)
              ·
                refine ⟨755804574960704935453021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007739433280939913937361 755804574960704935453021)
                ·
                  refine ⟨283426715610264350794883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755804574960704935453021 283426715610264350794883)
                  ·
                    refine ⟨425140073415396526192325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 283426715610264350794883 425140073415396526192325)
                    ·
                      refine ⟨79713763765386848661061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 425140073415396526192325 79713763765386848661061)
                      ·
                        rfl

theorem cell23_155242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_155242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155242 prefixEnd_155242 := by exact prefixLift 155242
  have htrace : WordTrace (prefixWord ++ tailWord_155242) baseStart_155242 baseEnd_155242 := by
    simpa [prefixWord, tailWord_155242, baseEnd_155242] using wordTrace_append hprefix tailTrace_155242
  have hstable : (prefixWord ++ tailWord_155242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155242).length < 2 ^ (prefixWord ++ tailWord_155242).sum := by decide
  have hdescent : baseEnd_155242 < baseStart_155242 := by decide
  rcases family_descends (prefixWord ++ tailWord_155242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155259 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 3, 2, 2]
def baseStart_155259 : Nat := 118140960795 + 155259 * 2 ^ 59
def prefixEnd_155259 : Nat := 4983230072969 + 3 ^ 40 * 155259 * 2
def baseEnd_155259 : Nat := 79722492936513282148483

theorem tailTrace_155259 : CollatzResearch.WordTrace tailWord_155259 prefixEnd_155259 79722492936513282148483 := by
  unfold tailWord_155259
  simp only [CollatzResearch.WordTrace]
  refine ⟨5662760944530633971252831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3775173963020422647501887 5662760944530633971252831)
  ·
    refine ⟨8494141416795950956879247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5662760944530633971252831 8494141416795950956879247)
    ·
      refine ⟨12741212125193926435318871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8494141416795950956879247 12741212125193926435318871)
      ·
        refine ⟨19111818187790889652978307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12741212125193926435318871 19111818187790889652978307)
        ·
          refine ⟨28667727281686334479467461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19111818187790889652978307 28667727281686334479467461)
          ·
            refine ⟨5375198865316187714900149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28667727281686334479467461 5375198865316187714900149)
            ·
              refine ⟨503924893623392598271889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5375198865316187714900149 503924893623392598271889)
              ·
                refine ⟨377943670217544448703917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503924893623392598271889 377943670217544448703917)
                ·
                  refine ⟨141728876331579168263969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377943670217544448703917 141728876331579168263969)
                  ·
                    refine ⟨106296657248684376197977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141728876331579168263969 106296657248684376197977)
                    ·
                      refine ⟨79722492936513282148483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 106296657248684376197977 79722492936513282148483)
                      ·
                        rfl

theorem cell23_155259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 2, 2].length) (baseStart_155259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155259 prefixEnd_155259 := by exact prefixLift 155259
  have htrace : WordTrace (prefixWord ++ tailWord_155259) baseStart_155259 baseEnd_155259 := by
    simpa [prefixWord, tailWord_155259, baseEnd_155259] using wordTrace_append hprefix tailTrace_155259
  have hstable : (prefixWord ++ tailWord_155259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155259).length < 2 ^ (prefixWord ++ tailWord_155259).sum := by decide
  have hdescent : baseEnd_155259 < baseStart_155259 := by decide
  rcases family_descends (prefixWord ++ tailWord_155259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155282 : List Nat := [3, 2, 3, 1, 3, 1, 10]
def baseStart_155282 : Nat := 118140960795 + 155282 * 2 ^ 59
def prefixEnd_155282 : Nat := 4983230072969 + 3 ^ 40 * 155282 * 2
def baseEnd_155282 : Nat := 984374111006996199517

theorem tailTrace_155282 : CollatzResearch.WordTrace tailWord_155282 prefixEnd_155282 984374111006996199517 := by
  unfold tailWord_155282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415899955861827224835025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3775733215631539266226733 1415899955861827224835025)
  ·
    refine ⟨1061924966896370418626269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1415899955861827224835025 1061924966896370418626269)
    ·
      refine ⟨398221862586138906984851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1061924966896370418626269 398221862586138906984851)
      ·
        refine ⟨597332793879208360477277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398221862586138906984851 597332793879208360477277)
        ·
          refine ⟨223999797704703135178979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 597332793879208360477277 223999797704703135178979)
          ·
            refine ⟨335999696557054702768469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223999797704703135178979 335999696557054702768469)
            ·
              refine ⟨984374111006996199517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 335999696557054702768469 984374111006996199517)
              ·
                rfl

theorem cell23_155282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 10].length) (baseStart_155282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155282 prefixEnd_155282 := by exact prefixLift 155282
  have htrace : WordTrace (prefixWord ++ tailWord_155282) baseStart_155282 baseEnd_155282 := by
    simpa [prefixWord, tailWord_155282, baseEnd_155282] using wordTrace_append hprefix tailTrace_155282
  have hstable : (prefixWord ++ tailWord_155282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155282).length < 2 ^ (prefixWord ++ tailWord_155282).sum := by decide
  have hdescent : baseEnd_155282 < baseStart_155282 := by decide
  rcases family_descends (prefixWord ++ tailWord_155282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155352 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 2, 4, 3]
def baseStart_155352 : Nat := 118140960795 + 155352 * 2 ^ 59
def prefixEnd_155352 : Nat := 4983230072969 + 3 ^ 40 * 155352 * 2
def baseEnd_155352 : Nat := 79770246637381418285555

theorem tailTrace_155352 : CollatzResearch.WordTrace tailWord_155352 prefixEnd_155352 79770246637381418285555 := by
  unfold tailWord_155352
  simp only [CollatzResearch.WordTrace]
  refine ⟨2833076466596855427194155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3777435288795807236258873 2833076466596855427194155)
  ·
    refine ⟨4249614699895283140791233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2833076466596855427194155 4249614699895283140791233)
    ·
      refine ⟨3187211024921462355593425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4249614699895283140791233 3187211024921462355593425)
      ·
        refine ⟨2390408268691096766695069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3187211024921462355593425 2390408268691096766695069)
        ·
          refine ⟨896403100759161287510651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2390408268691096766695069 896403100759161287510651)
          ·
            refine ⟨1344604651138741931265977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896403100759161287510651 1344604651138741931265977)
            ·
              refine ⟨1008453488354056448449483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344604651138741931265977 1008453488354056448449483)
              ·
                refine ⟨1512680232531084672674225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008453488354056448449483 1512680232531084672674225)
                ·
                  refine ⟨1134510174398313504505669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1512680232531084672674225 1134510174398313504505669)
                  ·
                    refine ⟨212720657699683782094813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1134510174398313504505669 212720657699683782094813)
                    ·
                      refine ⟨79770246637381418285555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 212720657699683782094813 79770246637381418285555)
                      ·
                        rfl

theorem cell23_155352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_155352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155352 prefixEnd_155352 := by exact prefixLift 155352
  have htrace : WordTrace (prefixWord ++ tailWord_155352) baseStart_155352 baseEnd_155352 := by
    simpa [prefixWord, tailWord_155352, baseEnd_155352] using wordTrace_append hprefix tailTrace_155352
  have hstable : (prefixWord ++ tailWord_155352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155352).length < 2 ^ (prefixWord ++ tailWord_155352).sum := by decide
  have hdescent : baseEnd_155352 < baseStart_155352 := by decide
  rcases family_descends (prefixWord ++ tailWord_155352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155406 : List Nat := [4, 1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_155406 : Nat := 118140960795 + 155406 * 2 ^ 59
def prefixEnd_155406 : Nat := 4983230072969 + 3 ^ 40 * 155406 * 2
def baseEnd_155406 : Nat := 8866441621413800778923

theorem tailTrace_155406 : CollatzResearch.WordTrace tailWord_155406 prefixEnd_155406 8866441621413800778923 := by
  unfold tailWord_155406
  simp only [CollatzResearch.WordTrace]
  refine ⟨708515309374759759606759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3778748316665385384569381 708515309374759759606759)
  ·
    refine ⟨1062772964062139639410139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 708515309374759759606759 1062772964062139639410139)
    ·
      refine ⟨1594159446093209459115209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1062772964062139639410139 1594159446093209459115209)
      ·
        refine ⟨1195619584569907094336407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1594159446093209459115209 1195619584569907094336407)
        ·
          refine ⟨1793429376854860641504611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195619584569907094336407 1793429376854860641504611)
          ·
            refine ⟨2690144065282290962256917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793429376854860641504611 2690144065282290962256917)
            ·
              refine ⟨126100503060107388855793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2690144065282290962256917 126100503060107388855793)
              ·
                refine ⟨94575377295080541641845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126100503060107388855793 94575377295080541641845)
                ·
                  refine ⟨8866441621413800778923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94575377295080541641845 8866441621413800778923)
                  ·
                    rfl

theorem cell23_155406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_155406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155406 prefixEnd_155406 := by exact prefixLift 155406
  have htrace : WordTrace (prefixWord ++ tailWord_155406) baseStart_155406 baseEnd_155406 := by
    simpa [prefixWord, tailWord_155406, baseEnd_155406] using wordTrace_append hprefix tailTrace_155406
  have hstable : (prefixWord ++ tailWord_155406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155406).length < 2 ^ (prefixWord ++ tailWord_155406).sum := by decide
  have hdescent : baseEnd_155406 < baseStart_155406 := by decide
  rcases family_descends (prefixWord ++ tailWord_155406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155452 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_155452 : Nat := 118140960795 + 155452 * 2 ^ 59
def prefixEnd_155452 : Nat := 4983230072969 + 3 ^ 40 * 155452 * 2
def baseEnd_155452 : Nat := 79821594702831027035095

theorem tailTrace_155452 : CollatzResearch.WordTrace tailWord_155452 prefixEnd_155452 79821594702831027035095 := by
  unfold tailWord_155452
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834900116415713966514305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3779866821887618622019073 2834900116415713966514305)
  ·
    refine ⟨2126175087311785474885729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2834900116415713966514305 2126175087311785474885729)
    ·
      refine ⟨1594631315483839106164297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2126175087311785474885729 1594631315483839106164297)
      ·
        refine ⟨1195973486612879329623223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1594631315483839106164297 1195973486612879329623223)
        ·
          refine ⟨1793960229919318994434835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195973486612879329623223 1793960229919318994434835)
          ·
            refine ⟨2690940344878978491652253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793960229919318994434835 2690940344878978491652253)
            ·
              refine ⟨1009102629329616934369595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2690940344878978491652253 1009102629329616934369595)
              ·
                refine ⟨1513653943994425401554393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009102629329616934369595 1513653943994425401554393)
                ·
                  refine ⟨1135240457995819051165795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1513653943994425401554393 1135240457995819051165795)
                  ·
                    refine ⟨1702860686993728576748693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1135240457995819051165795 1702860686993728576748693)
                    ·
                      refine ⟨79821594702831027035095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1702860686993728576748693 79821594702831027035095)
                      ·
                        rfl

theorem cell23_155452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_155452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155452 prefixEnd_155452 := by exact prefixLift 155452
  have htrace : WordTrace (prefixWord ++ tailWord_155452) baseStart_155452 baseEnd_155452 := by
    simpa [prefixWord, tailWord_155452, baseEnd_155452] using wordTrace_append hprefix tailTrace_155452
  have hstable : (prefixWord ++ tailWord_155452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155452).length < 2 ^ (prefixWord ++ tailWord_155452).sum := by decide
  have hdescent : baseEnd_155452 < baseStart_155452 := by decide
  rcases family_descends (prefixWord ++ tailWord_155452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155466 : List Nat := [3, 1, 2, 1, 1, 1, 3, 6, 1, 4]
def baseStart_155466 : Nat := 118140960795 + 155466 * 2 ^ 59
def prefixEnd_155466 : Nat := 4983230072969 + 3 ^ 40 * 155466 * 2
def baseEnd_155466 : Nat := 26609594477331324086677

theorem tailTrace_155466 : CollatzResearch.WordTrace tailWord_155466 prefixEnd_155466 26609594477331324086677 := by
  unfold tailWord_155466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417577713695177081009563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3780207236520472216025501 1417577713695177081009563)
  ·
    refine ⟨2126366570542765621514345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1417577713695177081009563 2126366570542765621514345)
    ·
      refine ⟨1594774927907074216135759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2126366570542765621514345 1594774927907074216135759)
      ·
        refine ⟨2392162391860611324203639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1594774927907074216135759 2392162391860611324203639)
        ·
          refine ⟨3588243587790916986305459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392162391860611324203639 3588243587790916986305459)
          ·
            refine ⟨5382365381686375479458189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588243587790916986305459 5382365381686375479458189)
            ·
              refine ⟨2018387018132390804796821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5382365381686375479458189 2018387018132390804796821)
              ·
                refine ⟨94611891474955818974851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2018387018132390804796821 94611891474955818974851)
                ·
                  refine ⟨141917837212433728462277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94611891474955818974851 141917837212433728462277)
                  ·
                    refine ⟨26609594477331324086677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141917837212433728462277 26609594477331324086677)
                    ·
                      rfl

theorem cell23_155466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_155466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155466 prefixEnd_155466 := by exact prefixLift 155466
  have htrace : WordTrace (prefixWord ++ tailWord_155466) baseStart_155466 baseEnd_155466 := by
    simpa [prefixWord, tailWord_155466, baseEnd_155466] using wordTrace_append hprefix tailTrace_155466
  have hstable : (prefixWord ++ tailWord_155466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155466).length < 2 ^ (prefixWord ++ tailWord_155466).sum := by decide
  have hdescent : baseEnd_155466 < baseStart_155466 := by decide
  rcases family_descends (prefixWord ++ tailWord_155466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155482 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_155482 : Nat := 118140960795 + 155482 * 2 ^ 59
def prefixEnd_155482 : Nat := 4983230072969 + 3 ^ 40 * 155482 * 2
def baseEnd_155482 : Nat := 79836999122465909659957

theorem tailTrace_155482 : CollatzResearch.WordTrace tailWord_155482 prefixEnd_155482 79836999122465909659957 := by
  unfold tailWord_155482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417723605680685764155175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3780596281815162037747133 1417723605680685764155175)
  ·
    refine ⟨2126585408521028646232763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1417723605680685764155175 2126585408521028646232763)
    ·
      refine ⟨3189878112781542969349145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126585408521028646232763 3189878112781542969349145)
      ·
        refine ⟨2392408584586157227011859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3189878112781542969349145 2392408584586157227011859)
        ·
          refine ⟨3588612876879235840517789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392408584586157227011859 3588612876879235840517789)
          ·
            refine ⟨1345729828829713440194171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3588612876879235840517789 1345729828829713440194171)
            ·
              refine ⟨2018594743244570160291257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345729828829713440194171 2018594743244570160291257)
              ·
                refine ⟨1513946057433427620218443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2018594743244570160291257 1513946057433427620218443)
                ·
                  refine ⟨2270919086150141430327665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513946057433427620218443 2270919086150141430327665)
                  ·
                    refine ⟨1703189314612606072745749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2270919086150141430327665 1703189314612606072745749)
                    ·
                      refine ⟨79836999122465909659957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1703189314612606072745749 79836999122465909659957)
                      ·
                        rfl

theorem cell23_155482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_155482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155482 prefixEnd_155482 := by exact prefixLift 155482
  have htrace : WordTrace (prefixWord ++ tailWord_155482) baseStart_155482 baseEnd_155482 := by
    simpa [prefixWord, tailWord_155482, baseEnd_155482] using wordTrace_append hprefix tailTrace_155482
  have hstable : (prefixWord ++ tailWord_155482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155482).length < 2 ^ (prefixWord ++ tailWord_155482).sum := by decide
  have hdescent : baseEnd_155482 < baseStart_155482 := by decide
  rcases family_descends (prefixWord ++ tailWord_155482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155512 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_155512 : Nat := 118140960795 + 155512 * 2 ^ 59
def prefixEnd_155512 : Nat := 4983230072969 + 3 ^ 40 * 155512 * 2
def baseEnd_155512 : Nat := 79852403542100792284819

theorem tailTrace_155512 : CollatzResearch.WordTrace tailWord_155512 prefixEnd_155512 79852403542100792284819 := by
  unfold tailWord_155512
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835994306307029090106395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3781325741742705453475193 2835994306307029090106395)
  ·
    refine ⟨4253991459460543635159593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2835994306307029090106395 4253991459460543635159593)
    ·
      refine ⟨3190493594595407726369695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4253991459460543635159593 3190493594595407726369695)
      ·
        refine ⟨4785740391893111589554543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3190493594595407726369695 4785740391893111589554543)
        ·
          refine ⟨7178610587839667384331815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4785740391893111589554543 7178610587839667384331815)
          ·
            refine ⟨10767915881759501076497723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7178610587839667384331815 10767915881759501076497723)
            ·
              refine ⟨16151873822639251614746585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10767915881759501076497723 16151873822639251614746585)
              ·
                refine ⟨12113905366979438711059939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16151873822639251614746585 12113905366979438711059939)
                ·
                  refine ⟨18170858050469158066589909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12113905366979438711059939 18170858050469158066589909)
                  ·
                    refine ⟨425879485557870892185701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18170858050469158066589909 425879485557870892185701)
                    ·
                      refine ⟨79852403542100792284819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 425879485557870892185701 79852403542100792284819)
                      ·
                        rfl

theorem cell23_155512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_155512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155512 prefixEnd_155512 := by exact prefixLift 155512
  have htrace : WordTrace (prefixWord ++ tailWord_155512) baseStart_155512 baseEnd_155512 := by
    simpa [prefixWord, tailWord_155512, baseEnd_155512] using wordTrace_append hprefix tailTrace_155512
  have hstable : (prefixWord ++ tailWord_155512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155512).length < 2 ^ (prefixWord ++ tailWord_155512).sum := by decide
  have hdescent : baseEnd_155512 < baseStart_155512 := by decide
  rcases family_descends (prefixWord ++ tailWord_155512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155523 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 3, 1, 3]
def baseStart_155523 : Nat := 118140960795 + 155523 * 2 ^ 59
def prefixEnd_155523 : Nat := 4983230072969 + 3 ^ 40 * 155523 * 2
def baseEnd_155523 : Nat := 79858051829300249247269

theorem tailTrace_155523 : CollatzResearch.WordTrace tailWord_155523 prefixEnd_155523 79858051829300249247269 := by
  unfold tailWord_155523
  simp only [CollatzResearch.WordTrace]
  refine ⟨5672389815574207058863223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3781593210382804705908815 5672389815574207058863223)
  ·
    refine ⟨8508584723361310588294835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5672389815574207058863223 8508584723361310588294835)
    ·
      refine ⟨12762877085041965882442253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8508584723361310588294835 12762877085041965882442253)
      ·
        refine ⟨4786078906890737205915845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12762877085041965882442253 4786078906890737205915845)
        ·
          refine ⟨897389795042013226109221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4786078906890737205915845 897389795042013226109221)
          ·
            refine ⟨168260586570377479895479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 897389795042013226109221 168260586570377479895479)
            ·
              refine ⟨252390879855566219843219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168260586570377479895479 252390879855566219843219)
              ·
                refine ⟨378586319783349329764829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252390879855566219843219 378586319783349329764829)
                ·
                  refine ⟨141969869918755998661811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378586319783349329764829 141969869918755998661811)
                  ·
                    refine ⟨212954804878133997992717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 141969869918755998661811 212954804878133997992717)
                    ·
                      refine ⟨79858051829300249247269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 212954804878133997992717 79858051829300249247269)
                      ·
                        rfl

theorem cell23_155523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_155523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155523 prefixEnd_155523 := by exact prefixLift 155523
  have htrace : WordTrace (prefixWord ++ tailWord_155523) baseStart_155523 baseEnd_155523 := by
    simpa [prefixWord, tailWord_155523, baseEnd_155523] using wordTrace_append hprefix tailTrace_155523
  have hstable : (prefixWord ++ tailWord_155523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155523).length < 2 ^ (prefixWord ++ tailWord_155523).sum := by decide
  have hdescent : baseEnd_155523 < baseStart_155523 := by decide
  rcases family_descends (prefixWord ++ tailWord_155523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155529 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 4]
def baseStart_155529 : Nat := 118140960795 + 155529 * 2 ^ 59
def prefixEnd_155529 : Nat := 4983230072969 + 3 ^ 40 * 155529 * 2
def baseEnd_155529 : Nat := 79861132713227225772241

theorem tailTrace_155529 : CollatzResearch.WordTrace tailWord_155529 prefixEnd_155529 79861132713227225772241 := by
  unfold tailWord_155529
  simp only [CollatzResearch.WordTrace]
  refine ⟨5672608653552470083581641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3781739102368313389054427 5672608653552470083581641)
  ·
    refine ⟨4254456490164352562686231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5672608653552470083581641 4254456490164352562686231)
    ·
      refine ⟨6381684735246528844029347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4254456490164352562686231 6381684735246528844029347)
      ·
        refine ⟨9572527102869793266044021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6381684735246528844029347 9572527102869793266044021)
        ·
          refine ⟨897424415894043118691627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9572527102869793266044021 897424415894043118691627)
          ·
            refine ⟨1346136623841064678037441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897424415894043118691627 1346136623841064678037441)
            ·
              refine ⟨1009602467880798508528081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1346136623841064678037441 1009602467880798508528081)
              ·
                refine ⟨757201850910598881396061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1009602467880798508528081 757201850910598881396061)
                ·
                  refine ⟨283950694091474580523523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757201850910598881396061 283950694091474580523523)
                  ·
                    refine ⟨425926041137211870785285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 283950694091474580523523 425926041137211870785285)
                    ·
                      refine ⟨79861132713227225772241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 425926041137211870785285 79861132713227225772241)
                      ·
                        rfl

theorem cell23_155529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_155529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155529 prefixEnd_155529 := by exact prefixLift 155529
  have htrace : WordTrace (prefixWord ++ tailWord_155529) baseStart_155529 baseEnd_155529 := by
    simpa [prefixWord, tailWord_155529, baseEnd_155529] using wordTrace_append hprefix tailTrace_155529
  have hstable : (prefixWord ++ tailWord_155529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155529).length < 2 ^ (prefixWord ++ tailWord_155529).sum := by decide
  have hdescent : baseEnd_155529 < baseStart_155529 := by decide
  rcases family_descends (prefixWord ++ tailWord_155529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155530 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 6]
def baseStart_155530 : Nat := 118140960795 + 155530 * 2 ^ 59
def prefixEnd_155530 : Nat := 4983230072969 + 3 ^ 40 * 155530 * 2
def baseEnd_155530 : Nat := 8873516243764635762193

theorem tailTrace_155530 : CollatzResearch.WordTrace tailWord_155530 prefixEnd_155530 8873516243764635762193 := by
  unfold tailWord_155530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1418161281637211813592011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3781763417699231502912029 1418161281637211813592011)
  ·
    refine ⟨2127241922455817720388017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1418161281637211813592011 2127241922455817720388017)
    ·
      refine ⟨1595431441841863290291013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2127241922455817720388017 1595431441841863290291013)
      ·
        refine ⟨299143395345349366929565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1595431441841863290291013 299143395345349366929565)
        ·
          refine ⟨112178773254506012598587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299143395345349366929565 112178773254506012598587)
          ·
            refine ⟨168268159881759018897881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112178773254506012598587 168268159881759018897881)
            ·
              refine ⟨126201119911319264173411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168268159881759018897881 126201119911319264173411)
              ·
                refine ⟨189301679866978896260117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126201119911319264173411 189301679866978896260117)
                ·
                  refine ⟨8873516243764635762193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 189301679866978896260117 8873516243764635762193)
                  ·
                    rfl

theorem cell23_155530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_155530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155530 prefixEnd_155530 := by exact prefixLift 155530
  have htrace : WordTrace (prefixWord ++ tailWord_155530) baseStart_155530 baseEnd_155530 := by
    simpa [prefixWord, tailWord_155530, baseEnd_155530] using wordTrace_append hprefix tailTrace_155530
  have hstable : (prefixWord ++ tailWord_155530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155530).length < 2 ^ (prefixWord ++ tailWord_155530).sum := by decide
  have hdescent : baseEnd_155530 < baseStart_155530 := by decide
  rcases family_descends (prefixWord ++ tailWord_155530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155546 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_155546 : Nat := 118140960795 + 155546 * 2 ^ 59
def prefixEnd_155546 : Nat := 4983230072969 + 3 ^ 40 * 155546 * 2
def baseEnd_155546 : Nat := 79869861884353659259663

theorem tailTrace_155546 : CollatzResearch.WordTrace tailWord_155546 prefixEnd_155546 79869861884353659259663 := by
  unfold tailWord_155546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1418307173622720496737623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3782152462993921324633661 1418307173622720496737623)
  ·
    refine ⟨2127460760434080745106435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1418307173622720496737623 2127460760434080745106435)
    ·
      refine ⟨3191191140651121117659653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2127460760434080745106435 3191191140651121117659653)
      ·
        refine ⟨598348338872085209561185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3191191140651121117659653 598348338872085209561185)
        ·
          refine ⟨448761254154063907170889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598348338872085209561185 448761254154063907170889)
          ·
            refine ⟨336570940615547930378167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448761254154063907170889 336570940615547930378167)
            ·
              refine ⟨504856410923321895567251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336570940615547930378167 504856410923321895567251)
              ·
                refine ⟨757284616384982843350877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504856410923321895567251 757284616384982843350877)
                ·
                  refine ⟨283981731144368566256579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757284616384982843350877 283981731144368566256579)
                  ·
                    refine ⟨425972596716552849384869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 283981731144368566256579 425972596716552849384869)
                    ·
                      refine ⟨79869861884353659259663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 425972596716552849384869 79869861884353659259663)
                      ·
                        rfl

theorem cell23_155546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_155546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155546 prefixEnd_155546 := by exact prefixLift 155546
  have htrace : WordTrace (prefixWord ++ tailWord_155546) baseStart_155546 baseEnd_155546 := by
    simpa [prefixWord, tailWord_155546, baseEnd_155546] using wordTrace_append hprefix tailTrace_155546
  have hstable : (prefixWord ++ tailWord_155546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155546).length < 2 ^ (prefixWord ++ tailWord_155546).sum := by decide
  have hdescent : baseEnd_155546 < baseStart_155546 := by decide
  rcases family_descends (prefixWord ++ tailWord_155546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155573 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 2, 4]
def baseStart_155573 : Nat := 118140960795 + 155573 * 2 ^ 59
def prefixEnd_155573 : Nat := 4983230072969 + 3 ^ 40 * 155573 * 2
def baseEnd_155573 : Nat := 26627908620675017874013

theorem tailTrace_155573 : CollatzResearch.WordTrace tailWord_155573 prefixEnd_155573 26627908620675017874013 := by
  unfold tailWord_155573
  simp only [CollatzResearch.WordTrace]
  refine ⟨5674213465393065598183373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3782808976928710398788915 5674213465393065598183373)
  ·
    refine ⟨2127830049522399599318765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5674213465393065598183373 2127830049522399599318765)
    ·
      refine ⟨797936268570899849744537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2127830049522399599318765 797936268570899849744537)
      ·
        refine ⟨598452201428174887308403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 797936268570899849744537 598452201428174887308403)
        ·
          refine ⟨897678302142262330962605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598452201428174887308403 897678302142262330962605)
          ·
            refine ⟨336629363303348374110977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 897678302142262330962605 336629363303348374110977)
            ·
              refine ⟨252472022477511280583233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336629363303348374110977 252472022477511280583233)
              ·
                refine ⟨189354016858133460437425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252472022477511280583233 189354016858133460437425)
                ·
                  refine ⟨142015512643600095328069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189354016858133460437425 142015512643600095328069)
                  ·
                    refine ⟨26627908620675017874013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142015512643600095328069 26627908620675017874013)
                    ·
                      rfl

theorem cell23_155573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_155573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155573 prefixEnd_155573 := by exact prefixLift 155573
  have htrace : WordTrace (prefixWord ++ tailWord_155573) baseStart_155573 baseEnd_155573 := by
    simpa [prefixWord, tailWord_155573, baseEnd_155573] using wordTrace_append hprefix tailTrace_155573
  have hstable : (prefixWord ++ tailWord_155573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155573).length < 2 ^ (prefixWord ++ tailWord_155573).sum := by decide
  have hdescent : baseEnd_155573 < baseStart_155573 := by decide
  rcases family_descends (prefixWord ++ tailWord_155573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155596 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 1, 3, 3]
def baseStart_155596 : Nat := 118140960795 + 155596 * 2 ^ 59
def prefixEnd_155596 : Nat := 4983230072969 + 3 ^ 40 * 155596 * 2
def baseEnd_155596 : Nat := 79895535917078463634433

theorem tailTrace_155596 : CollatzResearch.WordTrace tailWord_155596 prefixEnd_155596 79895535917078463634433 := by
  unfold tailWord_155596
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837526172154870263135321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3783368229539827017513761 2837526172154870263135321)
  ·
    refine ⟨2128144629116152697351491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2837526172154870263135321 2128144629116152697351491)
    ·
      refine ⟨3192216943674229046027237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2128144629116152697351491 3192216943674229046027237)
      ·
        refine ⟨598540676938917946130107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3192216943674229046027237 598540676938917946130107)
        ·
          refine ⟨897811015408376919195161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598540676938917946130107 897811015408376919195161)
          ·
            refine ⟨673358261556282689396371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 897811015408376919195161 673358261556282689396371)
            ·
              refine ⟨1010037392334424034094557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673358261556282689396371 1010037392334424034094557)
              ·
                refine ⟨378764022125409012785459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1010037392334424034094557 378764022125409012785459)
                ·
                  refine ⟨568146033188113519178189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378764022125409012785459 568146033188113519178189)
                  ·
                    refine ⟨213054762445542569691821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568146033188113519178189 213054762445542569691821)
                    ·
                      refine ⟨79895535917078463634433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 213054762445542569691821 79895535917078463634433)
                      ·
                        rfl

theorem cell23_155596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_155596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155596 prefixEnd_155596 := by exact prefixLift 155596
  have htrace : WordTrace (prefixWord ++ tailWord_155596) baseStart_155596 baseEnd_155596 := by
    simpa [prefixWord, tailWord_155596, baseEnd_155596] using wordTrace_append hprefix tailTrace_155596
  have hstable : (prefixWord ++ tailWord_155596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155596).length < 2 ^ (prefixWord ++ tailWord_155596).sum := by decide
  have hdescent : baseEnd_155596 < baseStart_155596 := by decide
  rcases family_descends (prefixWord ++ tailWord_155596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155630 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_155630 : Nat := 118140960795 + 155630 * 2 ^ 59
def prefixEnd_155630 : Nat := 4983230072969 + 3 ^ 40 * 155630 * 2
def baseEnd_155630 : Nat := 79912994259331330609277

theorem tailTrace_155630 : CollatzResearch.WordTrace tailWord_155630 prefixEnd_155630 79912994259331330609277 := by
  unfold tailWord_155630
  simp only [CollatzResearch.WordTrace]
  refine ⟨709536553273320541626043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3784194950791042888672229 709536553273320541626043)
  ·
    refine ⟨1064304829909980812439065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 709536553273320541626043 1064304829909980812439065)
    ·
      refine ⟨798228622432485609329299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1064304829909980812439065 798228622432485609329299)
      ·
        refine ⟨1197342933648728413993949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798228622432485609329299 1197342933648728413993949)
        ·
          refine ⟨449003600118273155247731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1197342933648728413993949 449003600118273155247731)
          ·
            refine ⟨673505400177409732871597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449003600118273155247731 673505400177409732871597)
            ·
              refine ⟨252564525066528649826849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 673505400177409732871597 252564525066528649826849)
              ·
                refine ⟨189423393799896487370137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252564525066528649826849 189423393799896487370137)
                ·
                  refine ⟨142067545349922365527603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189423393799896487370137 142067545349922365527603)
                  ·
                    refine ⟨213101318024883548291405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142067545349922365527603 213101318024883548291405)
                    ·
                      refine ⟨79912994259331330609277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 213101318024883548291405 79912994259331330609277)
                      ·
                        rfl

theorem cell23_155630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_155630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155630 prefixEnd_155630 := by exact prefixLift 155630
  have htrace : WordTrace (prefixWord ++ tailWord_155630) baseStart_155630 baseEnd_155630 := by
    simpa [prefixWord, tailWord_155630, baseEnd_155630] using wordTrace_append hprefix tailTrace_155630
  have hstable : (prefixWord ++ tailWord_155630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155630).length < 2 ^ (prefixWord ++ tailWord_155630).sum := by decide
  have hdescent : baseEnd_155630 < baseStart_155630 := by decide
  rcases family_descends (prefixWord ++ tailWord_155630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155653 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 1, 4, 2]
def baseStart_155653 : Nat := 118140960795 + 155653 * 2 ^ 59
def prefixEnd_155653 : Nat := 4983230072969 + 3 ^ 40 * 155653 * 2
def baseEnd_155653 : Nat := 79924804314384740621671

theorem tailTrace_155653 : CollatzResearch.WordTrace tailWord_155653 prefixEnd_155653 79924804314384740621671 := by
  unfold tailWord_155653
  simp only [CollatzResearch.WordTrace]
  refine ⟨5677131305103239261095613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3784754203402159507397075 5677131305103239261095613)
  ·
    refine ⟨2128924239413714722910855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5677131305103239261095613 2128924239413714722910855)
    ·
      refine ⟨3193386359120572084366283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2128924239413714722910855 3193386359120572084366283)
      ·
        refine ⟨4790079538680858126549425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193386359120572084366283 4790079538680858126549425)
        ·
          refine ⟨3592559654010643594912069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4790079538680858126549425 3592559654010643594912069)
          ·
            refine ⟨673604935126995674046013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3592559654010643594912069 673604935126995674046013)
            ·
              refine ⟨252601850672623377767255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 673604935126995674046013 252601850672623377767255)
              ·
                refine ⟨378902776008935066650883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252601850672623377767255 378902776008935066650883)
                ·
                  refine ⟨568354164013402599976325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378902776008935066650883 568354164013402599976325)
                  ·
                    refine ⟨106566405752512987495561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 568354164013402599976325 106566405752512987495561)
                    ·
                      refine ⟨79924804314384740621671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 106566405752512987495561 79924804314384740621671)
                      ·
                        rfl

theorem cell23_155653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 4, 2].length) (baseStart_155653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155653 prefixEnd_155653 := by exact prefixLift 155653
  have htrace : WordTrace (prefixWord ++ tailWord_155653) baseStart_155653 baseEnd_155653 := by
    simpa [prefixWord, tailWord_155653, baseEnd_155653] using wordTrace_append hprefix tailTrace_155653
  have hstable : (prefixWord ++ tailWord_155653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155653).length < 2 ^ (prefixWord ++ tailWord_155653).sum := by decide
  have hdescent : baseEnd_155653 < baseStart_155653 := by decide
  rcases family_descends (prefixWord ++ tailWord_155653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155654 : List Nat := [6, 2, 1, 2, 1, 2, 2, 7]
def baseStart_155654 : Nat := 118140960795 + 155654 * 2 ^ 59
def prefixEnd_155654 : Nat := 4983230072969 + 3 ^ 40 * 155654 * 2
def baseEnd_155654 : Nat := 2960196955371823581821

theorem tailTrace_155654 : CollatzResearch.WordTrace tailWord_155654 prefixEnd_155654 2960196955371823581821 := by
  unfold tailWord_155654
  simp only [CollatzResearch.WordTrace]
  refine ⟨177411493065613013496313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3784778518733077621254677 177411493065613013496313)
  ·
    refine ⟨133058619799209760122235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177411493065613013496313 133058619799209760122235)
    ·
      refine ⟨199587929698814640183353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133058619799209760122235 199587929698814640183353)
      ·
        refine ⟨149690947274110980137515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199587929698814640183353 149690947274110980137515)
        ·
          refine ⟨224536420911166470206273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149690947274110980137515 224536420911166470206273)
          ·
            refine ⟨168402315683374852654705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224536420911166470206273 168402315683374852654705)
            ·
              refine ⟨126301736762531139491029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168402315683374852654705 126301736762531139491029)
              ·
                refine ⟨2960196955371823581821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 126301736762531139491029 2960196955371823581821)
                ·
                  rfl

theorem cell23_155654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_155654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155654 prefixEnd_155654 := by exact prefixLift 155654
  have htrace : WordTrace (prefixWord ++ tailWord_155654) baseStart_155654 baseEnd_155654 := by
    simpa [prefixWord, tailWord_155654, baseEnd_155654] using wordTrace_append hprefix tailTrace_155654
  have hstable : (prefixWord ++ tailWord_155654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155654).length < 2 ^ (prefixWord ++ tailWord_155654).sum := by decide
  have hdescent : baseEnd_155654 < baseStart_155654 := by decide
  rcases family_descends (prefixWord ++ tailWord_155654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155659 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 7]
def baseStart_155659 : Nat := 118140960795 + 155659 * 2 ^ 59
def prefixEnd_155659 : Nat := 4983230072969 + 3 ^ 40 * 155659 * 2
def baseEnd_155659 : Nat := 8880876133145746349627

theorem tailTrace_155659 : CollatzResearch.WordTrace tailWord_155659 prefixEnd_155659 8880876133145746349627 := by
  unfold tailWord_155659
  simp only [CollatzResearch.WordTrace]
  refine ⟨5677350143081502285814031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3784900095387668190542687 5677350143081502285814031)
  ·
    refine ⟨8516025214622253428721047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5677350143081502285814031 8516025214622253428721047)
    ·
      refine ⟨12774037821933380143081571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8516025214622253428721047 12774037821933380143081571)
      ·
        refine ⟨19161056732900070214622357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12774037821933380143081571 19161056732900070214622357)
        ·
          refine ⟨898174534354690791310423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19161056732900070214622357 898174534354690791310423)
          ·
            refine ⟨1347261801532036186965635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898174534354690791310423 1347261801532036186965635)
            ·
              refine ⟨2020892702298054280448453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347261801532036186965635 2020892702298054280448453)
              ·
                refine ⟨378917381680885177584085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2020892702298054280448453 378917381680885177584085)
                ·
                  refine ⟨8880876133145746349627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 378917381680885177584085 8880876133145746349627)
                  ·
                    rfl

theorem cell23_155659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 7].length) (baseStart_155659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155659 prefixEnd_155659 := by exact prefixLift 155659
  have htrace : WordTrace (prefixWord ++ tailWord_155659) baseStart_155659 baseEnd_155659 := by
    simpa [prefixWord, tailWord_155659, baseEnd_155659] using wordTrace_append hprefix tailTrace_155659
  have hstable : (prefixWord ++ tailWord_155659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155659).length < 2 ^ (prefixWord ++ tailWord_155659).sum := by decide
  have hdescent : baseEnd_155659 < baseStart_155659 := by decide
  rcases family_descends (prefixWord ++ tailWord_155659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155699 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 7]
def baseStart_155699 : Nat := 118140960795 + 155699 * 2 ^ 59
def prefixEnd_155699 : Nat := 4983230072969 + 3 ^ 40 * 155699 * 2
def baseEnd_155699 : Nat := 79948424424491560646459

theorem tailTrace_155699 : CollatzResearch.WordTrace tailWord_155699 prefixEnd_155699 79948424424491560646459 := by
  unfold tailWord_155699
  simp only [CollatzResearch.WordTrace]
  refine ⟨5678809062936589117270151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3785872708624392744846767 5678809062936589117270151)
  ·
    refine ⟨8518213594404883675905227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5678809062936589117270151 8518213594404883675905227)
    ·
      refine ⟨12777320391607325513857841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8518213594404883675905227 12777320391607325513857841)
      ·
        refine ⟨9582990293705494135393381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12777320391607325513857841 9582990293705494135393381)
        ·
          refine ⟨1796810680069780150386259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9582990293705494135393381 1796810680069780150386259)
          ·
            refine ⟨2695216020104670225579389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796810680069780150386259 2695216020104670225579389)
            ·
              refine ⟨1010706007539251334592271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2695216020104670225579389 1010706007539251334592271)
              ·
                refine ⟨1516059011308877001888407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010706007539251334592271 1516059011308877001888407)
                ·
                  refine ⟨2274088516963315502832611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516059011308877001888407 2274088516963315502832611)
                  ·
                    refine ⟨3411132775444973254248917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2274088516963315502832611 3411132775444973254248917)
                    ·
                      refine ⟨79948424424491560646459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3411132775444973254248917 79948424424491560646459)
                      ·
                        rfl

theorem cell23_155699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_155699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155699 prefixEnd_155699 := by exact prefixLift 155699
  have htrace : WordTrace (prefixWord ++ tailWord_155699) baseStart_155699 baseEnd_155699 := by
    simpa [prefixWord, tailWord_155699, baseEnd_155699] using wordTrace_append hprefix tailTrace_155699
  have hstable : (prefixWord ++ tailWord_155699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155699).length < 2 ^ (prefixWord ++ tailWord_155699).sum := by decide
  have hdescent : baseEnd_155699 < baseStart_155699 := by decide
  rcases family_descends (prefixWord ++ tailWord_155699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155704 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 2, 2, 2]
def baseStart_155704 : Nat := 118140960795 + 155704 * 2 ^ 59
def prefixEnd_155704 : Nat := 4983230072969 + 3 ^ 40 * 155704 * 2
def baseEnd_155704 : Nat := 79950991827764041083937

theorem tailTrace_155704 : CollatzResearch.WordTrace tailWord_155704 prefixEnd_155704 79950991827764041083937 := by
  unfold tailWord_155704
  simp only [CollatzResearch.WordTrace]
  refine ⟨2839495713959237485601083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3785994285278983314134777 2839495713959237485601083)
  ·
    refine ⟨4259243570938856228401625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2839495713959237485601083 4259243570938856228401625)
    ·
      refine ⟨3194432678204142171301219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4259243570938856228401625 3194432678204142171301219)
      ·
        refine ⟨4791649017306213256951829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194432678204142171301219 4791649017306213256951829)
        ·
          refine ⟨224608547686228746419617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4791649017306213256951829 224608547686228746419617)
          ·
            refine ⟨168456410764671559814713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224608547686228746419617 168456410764671559814713)
            ·
              refine ⟨126342308073503669861035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168456410764671559814713 126342308073503669861035)
              ·
                refine ⟨189513462110255504791553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126342308073503669861035 189513462110255504791553)
                ·
                  refine ⟨142135096582691628593665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189513462110255504791553 142135096582691628593665)
                  ·
                    refine ⟨106601322437018721445249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142135096582691628593665 106601322437018721445249)
                    ·
                      refine ⟨79950991827764041083937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 106601322437018721445249 79950991827764041083937)
                      ·
                        rfl

theorem cell23_155704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 2, 2, 2].length) (baseStart_155704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155704 prefixEnd_155704 := by exact prefixLift 155704
  have htrace : WordTrace (prefixWord ++ tailWord_155704) baseStart_155704 baseEnd_155704 := by
    simpa [prefixWord, tailWord_155704, baseEnd_155704] using wordTrace_append hprefix tailTrace_155704
  have hstable : (prefixWord ++ tailWord_155704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155704).length < 2 ^ (prefixWord ++ tailWord_155704).sum := by decide
  have hdescent : baseEnd_155704 < baseStart_155704 := by decide
  rcases family_descends (prefixWord ++ tailWord_155704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155777 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_155777 : Nat := 118140960795 + 155777 * 2 ^ 59
def prefixEnd_155777 : Nat := 4983230072969 + 3 ^ 40 * 155777 * 2
def baseEnd_155777 : Nat := 79988475915542255471101

theorem tailTrace_155777 : CollatzResearch.WordTrace tailWord_155777 prefixEnd_155777 79988475915542255471101 := by
  unfold tailWord_155777
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681653956654008438609585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3787769304436005625739723 5681653956654008438609585)
  ·
    refine ⟨4261240467490506328957189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5681653956654008438609585 4261240467490506328957189)
    ·
      refine ⟨798982587654469936679473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4261240467490506328957189 798982587654469936679473)
      ·
        refine ⟨599236940740852452509605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 798982587654469936679473 599236940740852452509605)
        ·
          refine ⟨112356926388909834845551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 599236940740852452509605 112356926388909834845551)
          ·
            refine ⟨168535389583364752268327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112356926388909834845551 168535389583364752268327)
            ·
              refine ⟨252803084375047128402491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168535389583364752268327 252803084375047128402491)
              ·
                refine ⟨379204626562570692603737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252803084375047128402491 379204626562570692603737)
                ·
                  refine ⟨284403469921928019452803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379204626562570692603737 284403469921928019452803)
                  ·
                    refine ⟨426605204882892029179205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 284403469921928019452803 426605204882892029179205)
                    ·
                      refine ⟨79988475915542255471101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 426605204882892029179205 79988475915542255471101)
                      ·
                        rfl

theorem cell23_155777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_155777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155777 prefixEnd_155777 := by exact prefixLift 155777
  have htrace : WordTrace (prefixWord ++ tailWord_155777) baseStart_155777 baseEnd_155777 := by
    simpa [prefixWord, tailWord_155777, baseEnd_155777] using wordTrace_append hprefix tailTrace_155777
  have hstable : (prefixWord ++ tailWord_155777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155777).length < 2 ^ (prefixWord ++ tailWord_155777).sum := by decide
  have hdescent : baseEnd_155777 < baseStart_155777 := by decide
  rcases family_descends (prefixWord ++ tailWord_155777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155800 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 6]
def baseStart_155800 : Nat := 118140960795 + 155800 * 2 ^ 59
def prefixEnd_155800 : Nat := 4983230072969 + 3 ^ 40 * 155800 * 2
def baseEnd_155800 : Nat := 8888920663399518387055

theorem tailTrace_155800 : CollatzResearch.WordTrace tailWord_155800 prefixEnd_155800 8888920663399518387055 := by
  unfold tailWord_155800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2841246417785341683348427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3788328557047122244464569 2841246417785341683348427)
  ·
    refine ⟨4261869626678012525022641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2841246417785341683348427 4261869626678012525022641)
    ·
      refine ⟨3196402220008509393766981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4261869626678012525022641 3196402220008509393766981)
      ·
        refine ⟨599325416251595511331309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3196402220008509393766981 599325416251595511331309)
        ·
          refine ⟨224747031094348316749241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 599325416251595511331309 224747031094348316749241)
          ·
            refine ⟨168560273320761237561931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224747031094348316749241 168560273320761237561931)
            ·
              refine ⟨252840409981141856342897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168560273320761237561931 252840409981141856342897)
              ·
                refine ⟨189630307485856392257173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252840409981141856342897 189630307485856392257173)
                ·
                  refine ⟨8888920663399518387055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 189630307485856392257173 8888920663399518387055)
                  ·
                    rfl

theorem cell23_155800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 6].length) (baseStart_155800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155800 prefixEnd_155800 := by exact prefixLift 155800
  have htrace : WordTrace (prefixWord ++ tailWord_155800) baseStart_155800 baseEnd_155800 := by
    simpa [prefixWord, tailWord_155800, baseEnd_155800] using wordTrace_append hprefix tailTrace_155800
  have hstable : (prefixWord ++ tailWord_155800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155800).length < 2 ^ (prefixWord ++ tailWord_155800).sum := by decide
  have hdescent : baseEnd_155800 < baseStart_155800 := by decide
  rcases family_descends (prefixWord ++ tailWord_155800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155833 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 2, 6, 2]
def baseStart_155833 : Nat := 118140960795 + 155833 * 2 ^ 59
def prefixEnd_155833 : Nat := 4983230072969 + 3 ^ 40 * 155833 * 2
def baseEnd_155833 : Nat := 80017230832194036370843

theorem tailTrace_155833 : CollatzResearch.WordTrace tailWord_155833 prefixEnd_155833 80017230832194036370843 := by
  unfold tailWord_155833
  simp only [CollatzResearch.WordTrace]
  refine ⟨5683696444451130002648153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3789130962967420001765435 5683696444451130002648153)
  ·
    refine ⟨4262772333338347501986115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5683696444451130002648153 4262772333338347501986115)
    ·
      refine ⟨6394158500007521252979173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4262772333338347501986115 6394158500007521252979173)
      ·
        refine ⟨1198904718751410234933595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6394158500007521252979173 1198904718751410234933595)
        ·
          refine ⟨1798357078127115352400393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198904718751410234933595 1798357078127115352400393)
          ·
            refine ⟨1348767808595336514300295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1798357078127115352400393 1348767808595336514300295)
            ·
              refine ⟨2023151712893004771450443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348767808595336514300295 2023151712893004771450443)
              ·
                refine ⟨3034727569339507157175665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023151712893004771450443 3034727569339507157175665)
                ·
                  refine ⟨2276045677004630367881749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3034727569339507157175665 2276045677004630367881749)
                  ·
                    refine ⟨106689641109592048494457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2276045677004630367881749 106689641109592048494457)
                    ·
                      refine ⟨80017230832194036370843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 106689641109592048494457 80017230832194036370843)
                      ·
                        rfl

theorem cell23_155833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_155833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155833 prefixEnd_155833 := by exact prefixLift 155833
  have htrace : WordTrace (prefixWord ++ tailWord_155833) baseStart_155833 baseEnd_155833 := by
    simpa [prefixWord, tailWord_155833, baseEnd_155833] using wordTrace_append hprefix tailTrace_155833
  have hstable : (prefixWord ++ tailWord_155833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155833).length < 2 ^ (prefixWord ++ tailWord_155833).sum := by decide
  have hdescent : baseEnd_155833 < baseStart_155833 := by decide
  rcases family_descends (prefixWord ++ tailWord_155833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155844 : List Nat := [2, 3, 3, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_155844 : Nat := 118140960795 + 155844 * 2 ^ 59
def prefixEnd_155844 : Nat := 4983230072969 + 3 ^ 40 * 155844 * 2
def baseEnd_155844 : Nat := 80022879119393493333293

theorem tailTrace_155844 : CollatzResearch.WordTrace tailWord_155844 prefixEnd_155844 80022879119393493333293 := by
  unfold tailWord_155844
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842048823705639440649293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3789398431607519254199057 2842048823705639440649293)
  ·
    refine ⟨1065768308889614790243485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2842048823705639440649293 1065768308889614790243485)
    ·
      refine ⟨399663115833605546341307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1065768308889614790243485 399663115833605546341307)
      ·
        refine ⟨599494673750408319511961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399663115833605546341307 599494673750408319511961)
        ·
          refine ⟨449621005312806239633971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599494673750408319511961 449621005312806239633971)
          ·
            refine ⟨674431507969209359450957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449621005312806239633971 674431507969209359450957)
            ·
              refine ⟨252911815488453509794109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 674431507969209359450957 252911815488453509794109)
              ·
                refine ⟨94841930808170066172791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252911815488453509794109 94841930808170066172791)
                ·
                  refine ⟨142262896212255099259187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94841930808170066172791 142262896212255099259187)
                  ·
                    refine ⟨213394344318382648888781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142262896212255099259187 213394344318382648888781)
                    ·
                      refine ⟨80022879119393493333293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 213394344318382648888781 80022879119393493333293)
                      ·
                        rfl

theorem cell23_155844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_155844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155844 prefixEnd_155844 := by exact prefixLift 155844
  have htrace : WordTrace (prefixWord ++ tailWord_155844) baseStart_155844 baseEnd_155844 := by
    simpa [prefixWord, tailWord_155844, baseEnd_155844] using wordTrace_append hprefix tailTrace_155844
  have hstable : (prefixWord ++ tailWord_155844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155844).length < 2 ^ (prefixWord ++ tailWord_155844).sum := by decide
  have hdescent : baseEnd_155844 < baseStart_155844 := by decide
  rcases family_descends (prefixWord ++ tailWord_155844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155861 : List Nat := [1, 3, 2, 4, 2, 1, 3, 2, 1, 1, 3]
def baseStart_155861 : Nat := 118140960795 + 155861 * 2 ^ 59
def prefixEnd_155861 : Nat := 4983230072969 + 3 ^ 40 * 155861 * 2
def baseEnd_155861 : Nat := 80031608290519926820715

theorem tailTrace_155861 : CollatzResearch.WordTrace tailWord_155861 prefixEnd_155861 80031608290519926820715 := by
  unfold tailWord_155861
  simp only [CollatzResearch.WordTrace]
  refine ⟨5684717688349690784667437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3789811792233127189778291 5684717688349690784667437)
  ·
    refine ⟨2131769133131134044250289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5684717688349690784667437 2131769133131134044250289)
    ·
      refine ⟨1598826849848350533187717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2131769133131134044250289 1598826849848350533187717)
      ·
        refine ⟨299780034346565724972697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1598826849848350533187717 299780034346565724972697)
        ·
          refine ⟨224835025759924293729523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299780034346565724972697 224835025759924293729523)
          ·
            refine ⟨337252538639886440594285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224835025759924293729523 337252538639886440594285)
            ·
              refine ⟨126469701989957415222857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337252538639886440594285 126469701989957415222857)
              ·
                refine ⟨94852276492468061417143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126469701989957415222857 94852276492468061417143)
                ·
                  refine ⟨142278414738702092125715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94852276492468061417143 142278414738702092125715)
                  ·
                    refine ⟨213417622108053138188573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142278414738702092125715 213417622108053138188573)
                    ·
                      refine ⟨80031608290519926820715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 213417622108053138188573 80031608290519926820715)
                      ·
                        rfl

theorem cell23_155861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_155861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155861 prefixEnd_155861 := by exact prefixLift 155861
  have htrace : WordTrace (prefixWord ++ tailWord_155861) baseStart_155861 baseEnd_155861 := by
    simpa [prefixWord, tailWord_155861, baseEnd_155861] using wordTrace_append hprefix tailTrace_155861
  have hstable : (prefixWord ++ tailWord_155861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155861).length < 2 ^ (prefixWord ++ tailWord_155861).sum := by decide
  have hdescent : baseEnd_155861 < baseStart_155861 := by decide
  rcases family_descends (prefixWord ++ tailWord_155861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155876 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_155876 : Nat := 118140960795 + 155876 * 2 ^ 59
def prefixEnd_155876 : Nat := 4983230072969 + 3 ^ 40 * 155876 * 2
def baseEnd_155876 : Nat := 80039310500337368133145

theorem tailTrace_155876 : CollatzResearch.WordTrace tailWord_155876 prefixEnd_155876 80039310500337368133145 := by
  unfold tailWord_155876
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842632391647674173231741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3790176522196898897642321 2842632391647674173231741)
  ·
    refine ⟨1065987146867877814961903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2842632391647674173231741 1065987146867877814961903)
    ·
      refine ⟨1598980720301816722442855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1065987146867877814961903 1598980720301816722442855)
      ·
        refine ⟨2398471080452725083664283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598980720301816722442855 2398471080452725083664283)
        ·
          refine ⟨3597706620679087625496425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2398471080452725083664283 3597706620679087625496425)
          ·
            refine ⟨2698279965509315719122319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3597706620679087625496425 2698279965509315719122319)
            ·
              refine ⟨4047419948263973578683479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698279965509315719122319 4047419948263973578683479)
              ·
                refine ⟨6071129922395960368025219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4047419948263973578683479 6071129922395960368025219)
                ·
                  refine ⟨9106694883593940552037829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6071129922395960368025219 9106694883593940552037829)
                  ·
                    refine ⟨1707505290673863853507093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9106694883593940552037829 1707505290673863853507093)
                    ·
                      refine ⟨80039310500337368133145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1707505290673863853507093 80039310500337368133145)
                      ·
                        rfl

theorem cell23_155876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_155876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155876 prefixEnd_155876 := by exact prefixLift 155876
  have htrace : WordTrace (prefixWord ++ tailWord_155876) baseStart_155876 baseEnd_155876 := by
    simpa [prefixWord, tailWord_155876, baseEnd_155876] using wordTrace_append hprefix tailTrace_155876
  have hstable : (prefixWord ++ tailWord_155876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155876).length < 2 ^ (prefixWord ++ tailWord_155876).sum := by decide
  have hdescent : baseEnd_155876 < baseStart_155876 := by decide
  rcases family_descends (prefixWord ++ tailWord_155876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155877 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 2, 4]
def baseStart_155877 : Nat := 118140960795 + 155877 * 2 ^ 59
def prefixEnd_155877 : Nat := 4983230072969 + 3 ^ 40 * 155877 * 2
def baseEnd_155877 : Nat := 26679941326997288073547

theorem tailTrace_155877 : CollatzResearch.WordTrace tailWord_155877 prefixEnd_155877 26679941326997288073547 := by
  unfold tailWord_155877
  simp only [CollatzResearch.WordTrace]
  refine ⟨5685301256291725517249885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3790200837527817011499923 5685301256291725517249885)
  ·
    refine ⟨2131987971109397068968707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5685301256291725517249885 2131987971109397068968707)
    ·
      refine ⟨3197981956664095603453061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2131987971109397068968707 3197981956664095603453061)
      ·
        refine ⟨599621616874517925647449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3197981956664095603453061 599621616874517925647449)
        ·
          refine ⟨449716212655888444235587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599621616874517925647449 449716212655888444235587)
          ·
            refine ⟨674574318983832666353381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449716212655888444235587 674574318983832666353381)
            ·
              refine ⟨126482684809468624941259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 674574318983832666353381 126482684809468624941259)
              ·
                refine ⟨189724027214202937411889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126482684809468624941259 189724027214202937411889)
                ·
                  refine ⟨142293020410652203058917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189724027214202937411889 142293020410652203058917)
                  ·
                    refine ⟨26679941326997288073547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142293020410652203058917 26679941326997288073547)
                    ·
                      rfl

theorem cell23_155877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_155877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155877 prefixEnd_155877 := by exact prefixLift 155877
  have htrace : WordTrace (prefixWord ++ tailWord_155877) baseStart_155877 baseEnd_155877 := by
    simpa [prefixWord, tailWord_155877, baseEnd_155877] using wordTrace_append hprefix tailTrace_155877
  have hstable : (prefixWord ++ tailWord_155877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155877).length < 2 ^ (prefixWord ++ tailWord_155877).sum := by decide
  have hdescent : baseEnd_155877 < baseStart_155877 := by decide
  rcases family_descends (prefixWord ++ tailWord_155877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155883 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 3]
def baseStart_155883 : Nat := 118140960795 + 155883 * 2 ^ 59
def prefixEnd_155883 : Nat := 4983230072969 + 3 ^ 40 * 155883 * 2
def baseEnd_155883 : Nat := 80042904864918840745613

theorem tailTrace_155883 : CollatzResearch.WordTrace tailWord_155883 prefixEnd_155883 80042904864918840745613 := by
  unfold tailWord_155883
  simp only [CollatzResearch.WordTrace]
  refine ⟨5685520094269988541968303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3790346729513325694645535 5685520094269988541968303)
  ·
    refine ⟨8528280141404982812952455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5685520094269988541968303 8528280141404982812952455)
    ·
      refine ⟨12792420212107474219428683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8528280141404982812952455 12792420212107474219428683)
      ·
        refine ⟨19188630318161211329143025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12792420212107474219428683 19188630318161211329143025)
        ·
          refine ⟨14391472738620908496857269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19188630318161211329143025 14391472738620908496857269)
          ·
            refine ⟨1349200569245710171580369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14391472738620908496857269 1349200569245710171580369)
            ·
              refine ⟨1011900426934282628685277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349200569245710171580369 1011900426934282628685277)
              ·
                refine ⟨379462660100355985756979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1011900426934282628685277 379462660100355985756979)
                ·
                  refine ⟨569193990150533978635469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379462660100355985756979 569193990150533978635469)
                  ·
                    refine ⟨213447746306450241988301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 569193990150533978635469 213447746306450241988301)
                    ·
                      refine ⟨80042904864918840745613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 213447746306450241988301 80042904864918840745613)
                      ·
                        rfl

theorem cell23_155883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 3].length) (baseStart_155883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155883 prefixEnd_155883 := by exact prefixLift 155883
  have htrace : WordTrace (prefixWord ++ tailWord_155883) baseStart_155883 baseEnd_155883 := by
    simpa [prefixWord, tailWord_155883, baseEnd_155883] using wordTrace_append hprefix tailTrace_155883
  have hstable : (prefixWord ++ tailWord_155883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155883).length < 2 ^ (prefixWord ++ tailWord_155883).sum := by decide
  have hdescent : baseEnd_155883 < baseStart_155883 := by decide
  rcases family_descends (prefixWord ++ tailWord_155883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155887 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 1, 2, 3]
def baseStart_155887 : Nat := 118140960795 + 155887 * 2 ^ 59
def prefixEnd_155887 : Nat := 4983230072969 + 3 ^ 40 * 155887 * 2
def baseEnd_155887 : Nat := 80044958787536825095595

theorem tailTrace_155887 : CollatzResearch.WordTrace tailWord_155887 prefixEnd_155887 80044958787536825095595 := by
  unfold tailWord_155887
  simp only [CollatzResearch.WordTrace]
  refine ⟨5685665986255497225113915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3790443990836998150075943 5685665986255497225113915)
  ·
    refine ⟨8528498979383245837670873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5685665986255497225113915 8528498979383245837670873)
    ·
      refine ⟨6396374234537434378253155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8528498979383245837670873 6396374234537434378253155)
      ·
        refine ⟨9594561351806151567379733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6396374234537434378253155 9594561351806151567379733)
        ·
          refine ⟨449745063365913354720925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9594561351806151567379733 449745063365913354720925)
          ·
            refine ⟨168654398762217508020347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 449745063365913354720925 168654398762217508020347)
            ·
              refine ⟨252981598143326262030521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168654398762217508020347 252981598143326262030521)
              ·
                refine ⟨189736198607494696522891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252981598143326262030521 189736198607494696522891)
                ·
                  refine ⟨284604297911242044784337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189736198607494696522891 284604297911242044784337)
                  ·
                    refine ⟨213453223433431533588253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 284604297911242044784337 213453223433431533588253)
                    ·
                      refine ⟨80044958787536825095595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 213453223433431533588253 80044958787536825095595)
                      ·
                        rfl

theorem cell23_155887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 2, 3].length) (baseStart_155887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155887 prefixEnd_155887 := by exact prefixLift 155887
  have htrace : WordTrace (prefixWord ++ tailWord_155887) baseStart_155887 baseEnd_155887 := by
    simpa [prefixWord, tailWord_155887, baseEnd_155887] using wordTrace_append hprefix tailTrace_155887
  have hstable : (prefixWord ++ tailWord_155887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155887).length < 2 ^ (prefixWord ++ tailWord_155887).sum := by decide
  have hdescent : baseEnd_155887 < baseStart_155887 := by decide
  rcases family_descends (prefixWord ++ tailWord_155887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155896 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_155896 : Nat := 118140960795 + 155896 * 2 ^ 59
def prefixEnd_155896 : Nat := 4983230072969 + 3 ^ 40 * 155896 * 2
def baseEnd_155896 : Nat := 80049580113427289883053

theorem tailTrace_155896 : CollatzResearch.WordTrace tailWord_155896 prefixEnd_155896 80049580113427289883053 := by
  unfold tailWord_155896
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842997121611445881095771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3790662828815261174794361 2842997121611445881095771)
  ·
    refine ⟨4264495682417168821643657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2842997121611445881095771 4264495682417168821643657)
    ·
      refine ⟨3198371761812876616232743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4264495682417168821643657 3198371761812876616232743)
      ·
        refine ⟨4797557642719314924349115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3198371761812876616232743 4797557642719314924349115)
        ·
          refine ⟨7196336464078972386523673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4797557642719314924349115 7196336464078972386523673)
          ·
            refine ⟨5397252348059229289892755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7196336464078972386523673 5397252348059229289892755)
            ·
              refine ⟨8095878522088843934839133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397252348059229289892755 8095878522088843934839133)
              ·
                refine ⟨3035954445783316475564675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8095878522088843934839133 3035954445783316475564675)
                ·
                  refine ⟨4553931668674974713347013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3035954445783316475564675 4553931668674974713347013)
                  ·
                    refine ⟨853862187876557758752565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4553931668674974713347013 853862187876557758752565)
                    ·
                      refine ⟨80049580113427289883053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 853862187876557758752565 80049580113427289883053)
                      ·
                        rfl

theorem cell23_155896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_155896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155896 prefixEnd_155896 := by exact prefixLift 155896
  have htrace : WordTrace (prefixWord ++ tailWord_155896) baseStart_155896 baseEnd_155896 := by
    simpa [prefixWord, tailWord_155896, baseEnd_155896] using wordTrace_append hprefix tailTrace_155896
  have hstable : (prefixWord ++ tailWord_155896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155896).length < 2 ^ (prefixWord ++ tailWord_155896).sum := by decide
  have hdescent : baseEnd_155896 < baseStart_155896 := by decide
  rcases family_descends (prefixWord ++ tailWord_155896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155900 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_155900 : Nat := 118140960795 + 155900 * 2 ^ 59
def prefixEnd_155900 : Nat := 4983230072969 + 3 ^ 40 * 155900 * 2
def baseEnd_155900 : Nat := 80051634036045274233035

theorem tailTrace_155900 : CollatzResearch.WordTrace tailWord_155900 prefixEnd_155900 80051634036045274233035 := by
  unfold tailWord_155900
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843070067604200222668577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3790760090138933630224769 2843070067604200222668577)
  ·
    refine ⟨2132302550703150167001433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2843070067604200222668577 2132302550703150167001433)
    ·
      refine ⟨1599226913027362625251075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2132302550703150167001433 1599226913027362625251075)
      ·
        refine ⟨2398840369541043937876613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599226913027362625251075 2398840369541043937876613)
        ·
          refine ⟨449782569288945738351865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2398840369541043937876613 449782569288945738351865)
          ·
            refine ⟨337336926966709303763899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449782569288945738351865 337336926966709303763899)
            ·
              refine ⟨506005390450063955645849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337336926966709303763899 506005390450063955645849)
              ·
                refine ⟨379504042837547966734387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506005390450063955645849 379504042837547966734387)
                ·
                  refine ⟨569256064256321950101581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379504042837547966734387 569256064256321950101581)
                  ·
                    refine ⟨213471024096120731288093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 569256064256321950101581 213471024096120731288093)
                    ·
                      refine ⟨80051634036045274233035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 213471024096120731288093 80051634036045274233035)
                      ·
                        rfl

theorem cell23_155900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_155900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155900 prefixEnd_155900 := by exact prefixLift 155900
  have htrace : WordTrace (prefixWord ++ tailWord_155900) baseStart_155900 baseEnd_155900 := by
    simpa [prefixWord, tailWord_155900, baseEnd_155900] using wordTrace_append hprefix tailTrace_155900
  have hstable : (prefixWord ++ tailWord_155900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155900).length < 2 ^ (prefixWord ++ tailWord_155900).sum := by decide
  have hdescent : baseEnd_155900 < baseStart_155900 := by decide
  rcases family_descends (prefixWord ++ tailWord_155900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155934 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_155934 : Nat := 118140960795 + 155934 * 2 ^ 59
def prefixEnd_155934 : Nat := 4983230072969 + 3 ^ 40 * 155934 * 2
def baseEnd_155934 : Nat := 80069092378298141207879

theorem tailTrace_155934 : CollatzResearch.WordTrace tailWord_155934 prefixEnd_155934 80069092378298141207879 := by
  unfold tailWord_155934
  simp only [CollatzResearch.WordTrace]
  refine ⟨710922527135653031509357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3791586811390149501383237 710922527135653031509357)
  ·
    refine ⟨266595947675869886816009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 710922527135653031509357 266595947675869886816009)
    ·
      refine ⟨199946960756902415112007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266595947675869886816009 199946960756902415112007)
      ·
        refine ⟨299920441135353622668011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199946960756902415112007 299920441135353622668011)
        ·
          refine ⟨449880661703030434002017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299920441135353622668011 449880661703030434002017)
          ·
            refine ⟨337410496277272825501513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449880661703030434002017 337410496277272825501513)
            ·
              refine ⟨253057872207954619126135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337410496277272825501513 253057872207954619126135)
              ·
                refine ⟨379586808311931928689203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253057872207954619126135 379586808311931928689203)
                ·
                  refine ⟨569380212467897893033805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379586808311931928689203 569380212467897893033805)
                  ·
                    refine ⟨213517579675461709887677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 569380212467897893033805 213517579675461709887677)
                    ·
                      refine ⟨80069092378298141207879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 213517579675461709887677 80069092378298141207879)
                      ·
                        rfl

theorem cell23_155934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_155934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155934 prefixEnd_155934 := by exact prefixLift 155934
  have htrace : WordTrace (prefixWord ++ tailWord_155934) baseStart_155934 baseEnd_155934 := by
    simpa [prefixWord, tailWord_155934, baseEnd_155934] using wordTrace_append hprefix tailTrace_155934
  have hstable : (prefixWord ++ tailWord_155934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155934).length < 2 ^ (prefixWord ++ tailWord_155934).sum := by decide
  have hdescent : baseEnd_155934 < baseStart_155934 := by decide
  rcases family_descends (prefixWord ++ tailWord_155934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155957 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_155957 : Nat := 118140960795 + 155957 * 2 ^ 59
def prefixEnd_155957 : Nat := 4983230072969 + 3 ^ 40 * 155957 * 2
def baseEnd_155957 : Nat := 80080902433351551220273

theorem tailTrace_155957 : CollatzResearch.WordTrace tailWord_155957 prefixEnd_155957 80080902433351551220273 := by
  unfold tailWord_155957
  simp only [CollatzResearch.WordTrace]
  refine ⟨5688219096001899180162125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3792146064001266120108083 5688219096001899180162125)
  ·
    refine ⟨2133082161000712192560797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5688219096001899180162125 2133082161000712192560797)
    ·
      refine ⟨799905810375267072210299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2133082161000712192560797 799905810375267072210299)
      ·
        refine ⟨1199858715562900608315449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799905810375267072210299 1199858715562900608315449)
        ·
          refine ⟨899894036672175456236587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1199858715562900608315449 899894036672175456236587)
          ·
            refine ⟨1349841055008263184354881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899894036672175456236587 1349841055008263184354881)
            ·
              refine ⟨1012380791256197388266161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349841055008263184354881 1012380791256197388266161)
              ·
                refine ⟨759285593442148041199621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012380791256197388266161 759285593442148041199621)
                ·
                  refine ⟨142366048770402757724929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 759285593442148041199621 142366048770402757724929)
                  ·
                    refine ⟨106774536577802068293697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142366048770402757724929 106774536577802068293697)
                    ·
                      refine ⟨80080902433351551220273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 106774536577802068293697 80080902433351551220273)
                      ·
                        rfl

theorem cell23_155957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_155957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155957 prefixEnd_155957 := by exact prefixLift 155957
  have htrace : WordTrace (prefixWord ++ tailWord_155957) baseStart_155957 baseEnd_155957 := by
    simpa [prefixWord, tailWord_155957, baseEnd_155957] using wordTrace_append hprefix tailTrace_155957
  have hstable : (prefixWord ++ tailWord_155957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155957).length < 2 ^ (prefixWord ++ tailWord_155957).sum := by decide
  have hdescent : baseEnd_155957 < baseStart_155957 := by decide
  rcases family_descends (prefixWord ++ tailWord_155957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155961 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 1, 3, 2]
def baseStart_155961 : Nat := 118140960795 + 155961 * 2 ^ 59
def prefixEnd_155961 : Nat := 4983230072969 + 3 ^ 40 * 155961 * 2
def baseEnd_155961 : Nat := 80082956355969535570255

theorem tailTrace_155961 : CollatzResearch.WordTrace tailWord_155961 prefixEnd_155961 80082956355969535570255 := by
  unfold tailWord_155961
  simp only [CollatzResearch.WordTrace]
  refine ⟨5688364987987407863307737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3792243325324938575538491 5688364987987407863307737)
  ·
    refine ⟨4266273740990555897480803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5688364987987407863307737 4266273740990555897480803)
    ·
      refine ⟨6399410611485833846221205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4266273740990555897480803 6399410611485833846221205)
      ·
        refine ⟨299972372413398461541619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6399410611485833846221205 299972372413398461541619)
        ·
          refine ⟨449958558620097692312429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299972372413398461541619 449958558620097692312429)
          ·
            refine ⟨168734459482536634617161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 449958558620097692312429 168734459482536634617161)
            ·
              refine ⟨126550844611902475962871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168734459482536634617161 126550844611902475962871)
              ·
                refine ⟨189826266917853713944307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126550844611902475962871 189826266917853713944307)
                ·
                  refine ⟨284739400376780570916461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189826266917853713944307 284739400376780570916461)
                  ·
                    refine ⟨106777275141292714093673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284739400376780570916461 106777275141292714093673)
                    ·
                      refine ⟨80082956355969535570255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 106777275141292714093673 80082956355969535570255)
                      ·
                        rfl

theorem cell23_155961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_155961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155961 prefixEnd_155961 := by exact prefixLift 155961
  have htrace : WordTrace (prefixWord ++ tailWord_155961) baseStart_155961 baseEnd_155961 := by
    simpa [prefixWord, tailWord_155961, baseEnd_155961] using wordTrace_append hprefix tailTrace_155961
  have hstable : (prefixWord ++ tailWord_155961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155961).length < 2 ^ (prefixWord ++ tailWord_155961).sum := by decide
  have hdescent : baseEnd_155961 < baseStart_155961 := by decide
  rcases family_descends (prefixWord ++ tailWord_155961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155980 : List Nat := [2, 2, 1, 3, 2, 1, 1, 6, 5]
def baseStart_155980 : Nat := 118140960795 + 155980 * 2 ^ 59
def prefixEnd_155980 : Nat := 4983230072969 + 3 ^ 40 * 155980 * 2
def baseEnd_155980 : Nat := 8899190276489440136963

theorem tailTrace_155980 : CollatzResearch.WordTrace tailWord_155980 prefixEnd_155980 8899190276489440136963 := by
  unfold tailWord_155980
  simp only [CollatzResearch.WordTrace]
  refine ⟨2844528987459287054124697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3792705316612382738832929 2844528987459287054124697)
  ·
    refine ⟨2133396740594465290593523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2844528987459287054124697 2133396740594465290593523)
    ·
      refine ⟨3200095110891697935890285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2133396740594465290593523 3200095110891697935890285)
      ·
        refine ⟨1200035666584386725958857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3200095110891697935890285 1200035666584386725958857)
        ·
          refine ⟨900026749938290044469143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1200035666584386725958857 900026749938290044469143)
          ·
            refine ⟨1350040124907435066703715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900026749938290044469143 1350040124907435066703715)
            ·
              refine ⟨2025060187361152600055573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350040124907435066703715 2025060187361152600055573)
              ·
                refine ⟨94924696282554028127605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2025060187361152600055573 94924696282554028127605)
                ·
                  refine ⟨8899190276489440136963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94924696282554028127605 8899190276489440136963)
                  ·
                    rfl

theorem cell23_155980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_155980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_155980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_155980 prefixEnd_155980 := by exact prefixLift 155980
  have htrace : WordTrace (prefixWord ++ tailWord_155980) baseStart_155980 baseEnd_155980 := by
    simpa [prefixWord, tailWord_155980, baseEnd_155980] using wordTrace_append hprefix tailTrace_155980
  have hstable : (prefixWord ++ tailWord_155980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155980).length < 2 ^ (prefixWord ++ tailWord_155980).sum := by decide
  have hdescent : baseEnd_155980 < baseStart_155980 := by decide
  rcases family_descends (prefixWord ++ tailWord_155980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156010 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_156010 : Nat := 118140960795 + 156010 * 2 ^ 59
def prefixEnd_156010 : Nat := 4983230072969 + 3 ^ 40 * 156010 * 2
def baseEnd_156010 : Nat := 26702705636013281285843

theorem tailTrace_156010 : CollatzResearch.WordTrace tailWord_156010 prefixEnd_156010 26702705636013281285843 := by
  unfold tailWord_156010
  simp only [CollatzResearch.WordTrace]
  refine ⟨1422538041202472307960371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3793434776539926154560989 1422538041202472307960371)
  ·
    refine ⟨2133807061803708461940557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1422538041202472307960371 2133807061803708461940557)
    ·
      refine ⟨800177648176390673227709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2133807061803708461940557 800177648176390673227709)
      ·
        refine ⟨300066618066146502460391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 800177648176390673227709 300066618066146502460391)
        ·
          refine ⟨450099927099219753690587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300066618066146502460391 450099927099219753690587)
          ·
            refine ⟨675149890648829630535881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450099927099219753690587 675149890648829630535881)
            ·
              refine ⟨506362417986622222901911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675149890648829630535881 506362417986622222901911)
              ·
                refine ⟨759543626979933334352867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506362417986622222901911 759543626979933334352867)
                ·
                  refine ⟨1139315440469900001529301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759543626979933334352867 1139315440469900001529301)
                  ·
                    refine ⟨26702705636013281285843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1139315440469900001529301 26702705636013281285843)
                    ·
                      rfl

theorem cell23_156010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_156010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156010 prefixEnd_156010 := by exact prefixLift 156010
  have htrace : WordTrace (prefixWord ++ tailWord_156010) baseStart_156010 baseEnd_156010 := by
    simpa [prefixWord, tailWord_156010, baseEnd_156010] using wordTrace_append hprefix tailTrace_156010
  have hstable : (prefixWord ++ tailWord_156010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156010).length < 2 ^ (prefixWord ++ tailWord_156010).sum := by decide
  have hdescent : baseEnd_156010 < baseStart_156010 := by decide
  rcases family_descends (prefixWord ++ tailWord_156010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156067 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 3]
def baseStart_156067 : Nat := 118140960795 + 156067 * 2 ^ 59
def prefixEnd_156067 : Nat := 4983230072969 + 3 ^ 40 * 156067 * 2
def baseEnd_156067 : Nat := 80137385305346120844767

theorem tailTrace_156067 : CollatzResearch.WordTrace tailWord_156067 prefixEnd_156067 80137385305346120844767 := by
  unfold tailWord_156067
  simp only [CollatzResearch.WordTrace]
  refine ⟨5692231125603387966666455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3794820750402258644444303 5692231125603387966666455)
  ·
    refine ⟨8538346688405081949999683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5692231125603387966666455 8538346688405081949999683)
    ·
      refine ⟨12807520032607622924999525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8538346688405081949999683 12807520032607622924999525)
      ·
        refine ⟨2401410006113929298437411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12807520032607622924999525 2401410006113929298437411)
        ·
          refine ⟨3602115009170893947656117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401410006113929298437411 3602115009170893947656117)
          ·
            refine ⟨337698282109771307592761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3602115009170893947656117 337698282109771307592761)
            ·
              refine ⟨253273711582328480694571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337698282109771307592761 253273711582328480694571)
              ·
                refine ⟨379910567373492721041857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253273711582328480694571 379910567373492721041857)
                ·
                  refine ⟨284932925530119540781393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379910567373492721041857 284932925530119540781393)
                  ·
                    refine ⟨213699694147589655586045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 284932925530119540781393 213699694147589655586045)
                    ·
                      refine ⟨80137385305346120844767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 213699694147589655586045 80137385305346120844767)
                      ·
                        rfl

theorem cell23_156067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_156067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156067 prefixEnd_156067 := by exact prefixLift 156067
  have htrace : WordTrace (prefixWord ++ tailWord_156067) baseStart_156067 baseEnd_156067 := by
    simpa [prefixWord, tailWord_156067, baseEnd_156067] using wordTrace_append hprefix tailTrace_156067
  have hstable : (prefixWord ++ tailWord_156067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156067).length < 2 ^ (prefixWord ++ tailWord_156067).sum := by decide
  have hdescent : baseEnd_156067 < baseStart_156067 := by decide
  rcases family_descends (prefixWord ++ tailWord_156067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156140 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_156140 : Nat := 118140960795 + 156140 * 2 ^ 59
def prefixEnd_156140 : Nat := 4983230072969 + 3 ^ 40 * 156140 * 2
def baseEnd_156140 : Nat := 80174869393124335231931

theorem tailTrace_156140 : CollatzResearch.WordTrace tailWord_156140 prefixEnd_156140 80174869393124335231931 := by
  unfold tailWord_156140
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847446827169460717036937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3796595769559280956049249 2847446827169460717036937)
  ·
    refine ⟨2135585120377095537777703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2847446827169460717036937 2135585120377095537777703)
    ·
      refine ⟨3203377680565643306666555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2135585120377095537777703 3203377680565643306666555)
      ·
        refine ⟨4805066520848464959999833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3203377680565643306666555 4805066520848464959999833)
        ·
          refine ⟨3603799890636348719999875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4805066520848464959999833 3603799890636348719999875)
          ·
            refine ⟨5405699835954523079999813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3603799890636348719999875 5405699835954523079999813)
            ·
              refine ⟨1013568719241473077499965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5405699835954523079999813 1013568719241473077499965)
              ·
                refine ⟨380088269715552404062487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1013568719241473077499965 380088269715552404062487)
                ·
                  refine ⟨570132404573328606093731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380088269715552404062487 570132404573328606093731)
                  ·
                    refine ⟨855198606859992909140597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 570132404573328606093731 855198606859992909140597)
                    ·
                      refine ⟨80174869393124335231931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 855198606859992909140597 80174869393124335231931)
                      ·
                        rfl

theorem cell23_156140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_156140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156140 prefixEnd_156140 := by exact prefixLift 156140
  have htrace : WordTrace (prefixWord ++ tailWord_156140) baseStart_156140 baseEnd_156140 := by
    simpa [prefixWord, tailWord_156140, baseEnd_156140] using wordTrace_append hprefix tailTrace_156140
  have hstable : (prefixWord ++ tailWord_156140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156140).length < 2 ^ (prefixWord ++ tailWord_156140).sum := by decide
  have hdescent : baseEnd_156140 < baseStart_156140 := by decide
  rcases family_descends (prefixWord ++ tailWord_156140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156164 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_156164 : Nat := 118140960795 + 156164 * 2 ^ 59
def prefixEnd_156164 : Nat := 4983230072969 + 3 ^ 40 * 156164 * 2
def baseEnd_156164 : Nat := 26729064309610747110607

theorem tailTrace_156164 : CollatzResearch.WordTrace tailWord_156164 prefixEnd_156164 26729064309610747110607 := by
  unfold tailWord_156164
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847884503125986766473773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3797179337501315688631697 2847884503125986766473773)
  ·
    refine ⟨1067956688672245037427665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2847884503125986766473773 1067956688672245037427665)
    ·
      refine ⟨800967516504183778070749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1067956688672245037427665 800967516504183778070749)
      ·
        refine ⟨300362818689068916776531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 800967516504183778070749 300362818689068916776531)
        ·
          refine ⟨450544228033603375164797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300362818689068916776531 450544228033603375164797)
          ·
            refine ⟨168954085512601265686799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 450544228033603375164797 168954085512601265686799)
            ·
              refine ⟨253431128268901898530199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168954085512601265686799 253431128268901898530199)
              ·
                refine ⟨380146692403352847795299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253431128268901898530199 380146692403352847795299)
                ·
                  refine ⟨570220038605029271692949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380146692403352847795299 570220038605029271692949)
                  ·
                    refine ⟨26729064309610747110607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 570220038605029271692949 26729064309610747110607)
                    ·
                      rfl

theorem cell23_156164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_156164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156164 prefixEnd_156164 := by exact prefixLift 156164
  have htrace : WordTrace (prefixWord ++ tailWord_156164) baseStart_156164 baseEnd_156164 := by
    simpa [prefixWord, tailWord_156164, baseEnd_156164] using wordTrace_append hprefix tailTrace_156164
  have hstable : (prefixWord ++ tailWord_156164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156164).length < 2 ^ (prefixWord ++ tailWord_156164).sum := by decide
  have hdescent : baseEnd_156164 < baseStart_156164 := by decide
  rcases family_descends (prefixWord ++ tailWord_156164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156167 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_156167 : Nat := 118140960795 + 156167 * 2 ^ 59
def prefixEnd_156167 : Nat := 4983230072969 + 3 ^ 40 * 156167 * 2
def baseEnd_156167 : Nat := 80188733370795729594307

theorem tailTrace_156167 : CollatzResearch.WordTrace tailWord_156167 prefixEnd_156167 80188733370795729594307 := by
  unfold tailWord_156167
  simp only [CollatzResearch.WordTrace]
  refine ⟨5695878425241105045306755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3797252283494070030204503 5695878425241105045306755)
  ·
    refine ⟨8543817637861657567960133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5695878425241105045306755 8543817637861657567960133)
    ·
      refine ⟨1601965807099060793992525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8543817637861657567960133 1601965807099060793992525)
      ·
        refine ⟨600737177662147797747197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1601965807099060793992525 600737177662147797747197)
        ·
          refine ⟨225276441623305424155199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 600737177662147797747197 225276441623305424155199)
          ·
            refine ⟨337914662434958136232799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225276441623305424155199 337914662434958136232799)
            ·
              refine ⟨506871993652437204349199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337914662434958136232799 506871993652437204349199)
              ·
                refine ⟨760307990478655806523799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506871993652437204349199 760307990478655806523799)
                ·
                  refine ⟨1140461985717983709785699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760307990478655806523799 1140461985717983709785699)
                  ·
                    refine ⟨1710692978576975564678549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1140461985717983709785699 1710692978576975564678549)
                    ·
                      refine ⟨80188733370795729594307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1710692978576975564678549 80188733370795729594307)
                      ·
                        rfl

theorem cell23_156167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_156167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156167 prefixEnd_156167 := by exact prefixLift 156167
  have htrace : WordTrace (prefixWord ++ tailWord_156167) baseStart_156167 baseEnd_156167 := by
    simpa [prefixWord, tailWord_156167, baseEnd_156167] using wordTrace_append hprefix tailTrace_156167
  have hstable : (prefixWord ++ tailWord_156167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156167).length < 2 ^ (prefixWord ++ tailWord_156167).sum := by decide
  have hdescent : baseEnd_156167 < baseStart_156167 := by decide
  rcases family_descends (prefixWord ++ tailWord_156167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156174 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_156174 : Nat := 118140960795 + 156174 * 2 ^ 59
def prefixEnd_156174 : Nat := 4983230072969 + 3 ^ 40 * 156174 * 2
def baseEnd_156174 : Nat := 80192327735377202206775

theorem tailTrace_156174 : CollatzResearch.WordTrace tailWord_156174 prefixEnd_156174 80192327735377202206775 := by
  unfold tailWord_156174
  simp only [CollatzResearch.WordTrace]
  refine ⟨712016717026968155101447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3797422490810496827207717 712016717026968155101447)
  ·
    refine ⟨1068025075540452232652171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 712016717026968155101447 1068025075540452232652171)
    ·
      refine ⟨1602037613310678348978257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068025075540452232652171 1602037613310678348978257)
      ·
        refine ⟨1201528209983008761733693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1602037613310678348978257 1201528209983008761733693)
        ·
          refine ⟨450573078743628285650135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1201528209983008761733693 450573078743628285650135)
          ·
            refine ⟨675859618115442428475203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450573078743628285650135 675859618115442428475203)
            ·
              refine ⟨1013789427173163642712805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675859618115442428475203 1013789427173163642712805)
              ·
                refine ⟨190085517594968183008651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1013789427173163642712805 190085517594968183008651)
                ·
                  refine ⟨285128276392452274512977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190085517594968183008651 285128276392452274512977)
                  ·
                    refine ⟨213846207294339205884733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 285128276392452274512977 213846207294339205884733)
                    ·
                      refine ⟨80192327735377202206775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 213846207294339205884733 80192327735377202206775)
                      ·
                        rfl

theorem cell23_156174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_156174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156174 prefixEnd_156174 := by exact prefixLift 156174
  have htrace : WordTrace (prefixWord ++ tailWord_156174) baseStart_156174 baseEnd_156174 := by
    simpa [prefixWord, tailWord_156174, baseEnd_156174] using wordTrace_append hprefix tailTrace_156174
  have hstable : (prefixWord ++ tailWord_156174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156174).length < 2 ^ (prefixWord ++ tailWord_156174).sum := by decide
  have hdescent : baseEnd_156174 < baseStart_156174 := by decide
  rcases family_descends (prefixWord ++ tailWord_156174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156188 : List Nat := [2, 2, 3, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_156188 : Nat := 118140960795 + 156188 * 2 ^ 59
def prefixEnd_156188 : Nat := 4983230072969 + 3 ^ 40 * 156188 * 2
def baseEnd_156188 : Nat := 80199516464540147431711

theorem tailTrace_156188 : CollatzResearch.WordTrace tailWord_156188 prefixEnd_156188 80199516464540147431711 := by
  unfold tailWord_156188
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848322179082512815910609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3797762905443350421214145 2848322179082512815910609)
  ·
    refine ⟨2136241634311884611932957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2848322179082512815910609 2136241634311884611932957)
    ·
      refine ⟨801090612866956729474859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2136241634311884611932957 801090612866956729474859)
      ·
        refine ⟨1201635919300435094212289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801090612866956729474859 1201635919300435094212289)
        ·
          refine ⟨901226939475326320659217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1201635919300435094212289 901226939475326320659217)
          ·
            refine ⟨675920204606494740494413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 901226939475326320659217 675920204606494740494413)
            ·
              refine ⟨253470076727435527685405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 675920204606494740494413 253470076727435527685405)
              ·
                refine ⟨95051278772788322882027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253470076727435527685405 95051278772788322882027)
                ·
                  refine ⟨142576918159182484323041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95051278772788322882027 142576918159182484323041)
                  ·
                    refine ⟨106932688619386863242281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142576918159182484323041 106932688619386863242281)
                    ·
                      refine ⟨80199516464540147431711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 106932688619386863242281 80199516464540147431711)
                      ·
                        rfl

theorem cell23_156188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_156188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156188 prefixEnd_156188 := by exact prefixLift 156188
  have htrace : WordTrace (prefixWord ++ tailWord_156188) baseStart_156188 baseEnd_156188 := by
    simpa [prefixWord, tailWord_156188, baseEnd_156188] using wordTrace_append hprefix tailTrace_156188
  have hstable : (prefixWord ++ tailWord_156188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156188).length < 2 ^ (prefixWord ++ tailWord_156188).sum := by decide
  have hdescent : baseEnd_156188 < baseStart_156188 := by decide
  rcases family_descends (prefixWord ++ tailWord_156188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156221 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_156221 : Nat := 118140960795 + 156221 * 2 ^ 59
def prefixEnd_156221 : Nat := 4983230072969 + 3 ^ 40 * 156221 * 2
def baseEnd_156221 : Nat := 80216461326138518319059

theorem tailTrace_156221 : CollatzResearch.WordTrace tailWord_156221 prefixEnd_156221 80216461326138518319059 := by
  unfold tailWord_156221
  simp only [CollatzResearch.WordTrace]
  refine ⟨5697847967045472267772517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3798565311363648178515011 5697847967045472267772517)
  ·
    refine ⟨1068346493821026050207347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5697847967045472267772517 1068346493821026050207347)
    ·
      refine ⟨1602519740731539075311021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068346493821026050207347 1602519740731539075311021)
      ·
        refine ⟨600944902774327153241633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1602519740731539075311021 600944902774327153241633)
        ·
          refine ⟨450708677080745364931225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600944902774327153241633 450708677080745364931225)
          ·
            refine ⟨338031507810559023698419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450708677080745364931225 338031507810559023698419)
            ·
              refine ⟨507047261715838535547629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338031507810559023698419 507047261715838535547629)
              ·
                refine ⟨190142723143439450830361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507047261715838535547629 190142723143439450830361)
                ·
                  refine ⟨142607042357579588122771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190142723143439450830361 142607042357579588122771)
                  ·
                    refine ⟨213910563536369382184157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142607042357579588122771 213910563536369382184157)
                    ·
                      refine ⟨80216461326138518319059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 213910563536369382184157 80216461326138518319059)
                      ·
                        rfl

theorem cell23_156221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_156221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156221 prefixEnd_156221 := by exact prefixLift 156221
  have htrace : WordTrace (prefixWord ++ tailWord_156221) baseStart_156221 baseEnd_156221 := by
    simpa [prefixWord, tailWord_156221, baseEnd_156221] using wordTrace_append hprefix tailTrace_156221
  have hstable : (prefixWord ++ tailWord_156221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156221).length < 2 ^ (prefixWord ++ tailWord_156221).sum := by decide
  have hdescent : baseEnd_156221 < baseStart_156221 := by decide
  rcases family_descends (prefixWord ++ tailWord_156221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156227 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 5, 4, 2]
def baseStart_156227 : Nat := 118140960795 + 156227 * 2 ^ 59
def prefixEnd_156227 : Nat := 4983230072969 + 3 ^ 40 * 156227 * 2
def baseEnd_156227 : Nat := 80219542210065494844031

theorem tailTrace_156227 : CollatzResearch.WordTrace tailWord_156227 prefixEnd_156227 80219542210065494844031 := by
  unfold tailWord_156227
  simp only [CollatzResearch.WordTrace]
  refine ⟨5698066805023735292490935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3798711203349156861660623 5698066805023735292490935)
  ·
    refine ⟨8547100207535602938736403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5698066805023735292490935 8547100207535602938736403)
    ·
      refine ⟨12820650311303404408104605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8547100207535602938736403 12820650311303404408104605)
      ·
        refine ⟨4807743866738776653039227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12820650311303404408104605 4807743866738776653039227)
        ·
          refine ⟨7211615800108164979558841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4807743866738776653039227 7211615800108164979558841)
          ·
            refine ⟨5408711850081123734669131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7211615800108164979558841 5408711850081123734669131)
            ·
              refine ⟨8113067775121685602003697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5408711850081123734669131 8113067775121685602003697)
              ·
                refine ⟨6084800831341264201502773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8113067775121685602003697 6084800831341264201502773)
                ·
                  refine ⟨570450077938243518890885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6084800831341264201502773 570450077938243518890885)
                  ·
                    refine ⟨106959389613420659792041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 570450077938243518890885 106959389613420659792041)
                    ·
                      refine ⟨80219542210065494844031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 106959389613420659792041 80219542210065494844031)
                      ·
                        rfl

theorem cell23_156227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 4, 2].length) (baseStart_156227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156227 prefixEnd_156227 := by exact prefixLift 156227
  have htrace : WordTrace (prefixWord ++ tailWord_156227) baseStart_156227 baseEnd_156227 := by
    simpa [prefixWord, tailWord_156227, baseEnd_156227] using wordTrace_append hprefix tailTrace_156227
  have hstable : (prefixWord ++ tailWord_156227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156227).length < 2 ^ (prefixWord ++ tailWord_156227).sum := by decide
  have hdescent : baseEnd_156227 < baseStart_156227 := by decide
  rcases family_descends (prefixWord ++ tailWord_156227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156231 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 1, 3, 2]
def baseStart_156231 : Nat := 118140960795 + 156231 * 2 ^ 59
def prefixEnd_156231 : Nat := 4983230072969 + 3 ^ 40 * 156231 * 2
def baseEnd_156231 : Nat := 80221596132683479194013

theorem tailTrace_156231 : CollatzResearch.WordTrace tailWord_156231 prefixEnd_156231 80221596132683479194013 := by
  unfold tailWord_156231
  simp only [CollatzResearch.WordTrace]
  refine ⟨5698212697009243975636547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3798808464672829317091031 5698212697009243975636547)
  ·
    refine ⟨8547319045513865963454821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5698212697009243975636547 8547319045513865963454821)
    ·
      refine ⟨1602622321033849868147779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8547319045513865963454821 1602622321033849868147779)
      ·
        refine ⟨2403933481550774802221669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602622321033849868147779 2403933481550774802221669)
        ·
          refine ⟨450737527790770275416563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2403933481550774802221669 450737527790770275416563)
          ·
            refine ⟨676106291686155413124845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450737527790770275416563 676106291686155413124845)
            ·
              refine ⟨253539859382308279921817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676106291686155413124845 253539859382308279921817)
              ·
                refine ⟨190154894536731209941363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253539859382308279921817 190154894536731209941363)
                ·
                  refine ⟨285232341805096814912045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190154894536731209941363 285232341805096814912045)
                  ·
                    refine ⟨106962128176911305592017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285232341805096814912045 106962128176911305592017)
                    ·
                      refine ⟨80221596132683479194013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 106962128176911305592017 80221596132683479194013)
                      ·
                        rfl

theorem cell23_156231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_156231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156231 prefixEnd_156231 := by exact prefixLift 156231
  have htrace : WordTrace (prefixWord ++ tailWord_156231) baseStart_156231 baseEnd_156231 := by
    simpa [prefixWord, tailWord_156231, baseEnd_156231] using wordTrace_append hprefix tailTrace_156231
  have hstable : (prefixWord ++ tailWord_156231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156231).length < 2 ^ (prefixWord ++ tailWord_156231).sum := by decide
  have hdescent : baseEnd_156231 < baseStart_156231 := by decide
  rcases family_descends (prefixWord ++ tailWord_156231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156240 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 4]
def baseStart_156240 : Nat := 118140960795 + 156240 * 2 ^ 59
def prefixEnd_156240 : Nat := 4983230072969 + 3 ^ 40 * 156240 * 2
def baseEnd_156240 : Nat := 80226217458573943981471

theorem tailTrace_156240 : CollatzResearch.WordTrace tailWord_156240 prefixEnd_156240 80226217458573943981471 := by
  unfold tailWord_156240
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849270476988319256357087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3799027302651092341809449 2849270476988319256357087)
  ·
    refine ⟨4273905715482478884535631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2849270476988319256357087 4273905715482478884535631)
    ·
      refine ⟨6410858573223718326803447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4273905715482478884535631 6410858573223718326803447)
      ·
        refine ⟨9616287859835577490205171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6410858573223718326803447 9616287859835577490205171)
        ·
          refine ⟨14424431789753366235307757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9616287859835577490205171 14424431789753366235307757)
          ·
            refine ⟨5409161921157512338240409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14424431789753366235307757 5409161921157512338240409)
            ·
              refine ⟨4056871440868134253680307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5409161921157512338240409 4056871440868134253680307)
              ·
                refine ⟨6085307161302201380520461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4056871440868134253680307 6085307161302201380520461)
                ·
                  refine ⟨2281990185488325517695173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6085307161302201380520461 2281990185488325517695173)
                  ·
                    refine ⟨427873159779061034567845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2281990185488325517695173 427873159779061034567845)
                    ·
                      refine ⟨80226217458573943981471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 427873159779061034567845 80226217458573943981471)
                      ·
                        rfl

theorem cell23_156240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_156240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156240 prefixEnd_156240 := by exact prefixLift 156240
  have htrace : WordTrace (prefixWord ++ tailWord_156240) baseStart_156240 baseEnd_156240 := by
    simpa [prefixWord, tailWord_156240, baseEnd_156240] using wordTrace_append hprefix tailTrace_156240
  have hstable : (prefixWord ++ tailWord_156240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156240).length < 2 ^ (prefixWord ++ tailWord_156240).sum := by decide
  have hdescent : baseEnd_156240 < baseStart_156240 := by decide
  rcases family_descends (prefixWord ++ tailWord_156240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156244 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_156244 : Nat := 118140960795 + 156244 * 2 ^ 59
def prefixEnd_156244 : Nat := 4983230072969 + 3 ^ 40 * 156244 * 2
def baseEnd_156244 : Nat := 80228271381191928331453

theorem tailTrace_156244 : CollatzResearch.WordTrace tailWord_156244 prefixEnd_156244 80228271381191928331453 := by
  unfold tailWord_156244
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849343422981073597929893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3799124563974764797239857 2849343422981073597929893)
  ·
    refine ⟨534251891808951299611855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2849343422981073597929893 534251891808951299611855)
    ·
      refine ⟨801377837713426949417783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534251891808951299611855 801377837713426949417783)
      ·
        refine ⟨1202066756570140424126675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801377837713426949417783 1202066756570140424126675)
        ·
          refine ⟨1803100134855210636190013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1202066756570140424126675 1803100134855210636190013)
          ·
            refine ⟨676162550570703988571255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1803100134855210636190013 676162550570703988571255)
            ·
              refine ⟨1014243825856055982856883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676162550570703988571255 1014243825856055982856883)
              ·
                refine ⟨1521365738784083974285325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014243825856055982856883 1521365738784083974285325)
                ·
                  refine ⟨570512152044031490356997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1521365738784083974285325 570512152044031490356997)
                  ·
                    refine ⟨106971028508255904441937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 570512152044031490356997 106971028508255904441937)
                    ·
                      refine ⟨80228271381191928331453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 106971028508255904441937 80228271381191928331453)
                      ·
                        rfl

theorem cell23_156244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_156244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156244 prefixEnd_156244 := by exact prefixLift 156244
  have htrace : WordTrace (prefixWord ++ tailWord_156244) baseStart_156244 baseEnd_156244 := by
    simpa [prefixWord, tailWord_156244, baseEnd_156244] using wordTrace_append hprefix tailTrace_156244
  have hstable : (prefixWord ++ tailWord_156244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156244).length < 2 ^ (prefixWord ++ tailWord_156244).sum := by decide
  have hdescent : baseEnd_156244 < baseStart_156244 := by decide
  rcases family_descends (prefixWord ++ tailWord_156244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156274 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_156274 : Nat := 118140960795 + 156274 * 2 ^ 59
def prefixEnd_156274 : Nat := 4983230072969 + 3 ^ 40 * 156274 * 2
def baseEnd_156274 : Nat := 80243675800826810956315

theorem tailTrace_156274 : CollatzResearch.WordTrace tailWord_156274 prefixEnd_156274 80243675800826810956315 := by
  unfold tailWord_156274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424945258963365579862969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3799854023902308212967917 1424945258963365579862969)
  ·
    refine ⟨1068708944222524184897227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1424945258963365579862969 1068708944222524184897227)
    ·
      refine ⟨1603063416333786277345841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068708944222524184897227 1603063416333786277345841)
      ·
        refine ⟨1202297562250339708009381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1603063416333786277345841 1202297562250339708009381)
        ·
          refine ⟨225430792921938695251759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1202297562250339708009381 225430792921938695251759)
          ·
            refine ⟨338146189382908042877639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225430792921938695251759 338146189382908042877639)
            ·
              refine ⟨507219284074362064316459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338146189382908042877639 507219284074362064316459)
              ·
                refine ⟨760828926111543096474689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507219284074362064316459 760828926111543096474689)
                ·
                  refine ⟨570621694583657322356017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 760828926111543096474689 570621694583657322356017)
                  ·
                    refine ⟨427966270937742991767013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 570621694583657322356017 427966270937742991767013)
                    ·
                      refine ⟨80243675800826810956315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 427966270937742991767013 80243675800826810956315)
                      ·
                        rfl

theorem cell23_156274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_156274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156274 prefixEnd_156274 := by exact prefixLift 156274
  have htrace : WordTrace (prefixWord ++ tailWord_156274) baseStart_156274 baseEnd_156274 := by
    simpa [prefixWord, tailWord_156274, baseEnd_156274] using wordTrace_append hprefix tailTrace_156274
  have hstable : (prefixWord ++ tailWord_156274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156274).length < 2 ^ (prefixWord ++ tailWord_156274).sum := by decide
  have hdescent : baseEnd_156274 < baseStart_156274 := by decide
  rcases family_descends (prefixWord ++ tailWord_156274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156278 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_156278 : Nat := 118140960795 + 156278 * 2 ^ 59
def prefixEnd_156278 : Nat := 4983230072969 + 3 ^ 40 * 156278 * 2
def baseEnd_156278 : Nat := 80245729723444795306297

theorem tailTrace_156278 : CollatzResearch.WordTrace tailWord_156278 prefixEnd_156278 80245729723444795306297 := by
  unfold tailWord_156278
  simp only [CollatzResearch.WordTrace]
  refine ⟨356245432989935687662343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3799951285225980668398325 356245432989935687662343)
  ·
    refine ⟨534368149484903531493515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 356245432989935687662343 534368149484903531493515)
    ·
      refine ⟨801552224227355297240273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534368149484903531493515 801552224227355297240273)
      ·
        refine ⟨601164168170516472930205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 801552224227355297240273 601164168170516472930205)
        ·
          refine ⟨225436563063943677348827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 601164168170516472930205 225436563063943677348827)
          ·
            refine ⟨338154844595915516023241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225436563063943677348827 338154844595915516023241)
            ·
              refine ⟨253616133446936637017431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338154844595915516023241 253616133446936637017431)
              ·
                refine ⟨380424200170404955526147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253616133446936637017431 380424200170404955526147)
                ·
                  refine ⟨570636300255607433289221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380424200170404955526147 570636300255607433289221)
                  ·
                    refine ⟨106994306297926393741729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 570636300255607433289221 106994306297926393741729)
                    ·
                      refine ⟨80245729723444795306297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 106994306297926393741729 80245729723444795306297)
                      ·
                        rfl

theorem cell23_156278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_156278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156278 prefixEnd_156278 := by exact prefixLift 156278
  have htrace : WordTrace (prefixWord ++ tailWord_156278) baseStart_156278 baseEnd_156278 := by
    simpa [prefixWord, tailWord_156278, baseEnd_156278] using wordTrace_append hprefix tailTrace_156278
  have hstable : (prefixWord ++ tailWord_156278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156278).length < 2 ^ (prefixWord ++ tailWord_156278).sum := by decide
  have hdescent : baseEnd_156278 < baseStart_156278 := by decide
  rcases family_descends (prefixWord ++ tailWord_156278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156280 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 3, 7]
def baseStart_156280 : Nat := 118140960795 + 156280 * 2 ^ 59
def prefixEnd_156280 : Nat := 4983230072969 + 3 ^ 40 * 156280 * 2
def baseEnd_156280 : Nat := 26748918894917929160429

theorem tailTrace_156280 : CollatzResearch.WordTrace tailWord_156280 prefixEnd_156280 26748918894917929160429 := by
  unfold tailWord_156280
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849999936915862672085147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3799999915887816896113529 2849999936915862672085147)
  ·
    refine ⟨4274999905373794008127721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2849999936915862672085147 4274999905373794008127721)
    ·
      refine ⟨3206249929030345506095791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4274999905373794008127721 3206249929030345506095791)
      ·
        refine ⟨4809374893545518259143687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3206249929030345506095791 4809374893545518259143687)
        ·
          refine ⟨7214062340318277388715531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4809374893545518259143687 7214062340318277388715531)
          ·
            refine ⟨10821093510477416083073297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7214062340318277388715531 10821093510477416083073297)
            ·
              refine ⟨8115820132858062062304973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10821093510477416083073297 8115820132858062062304973)
              ·
                refine ⟨3043432549821773273364365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8115820132858062062304973 3043432549821773273364365)
                ·
                  refine ⟨1141287206183164977511637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3043432549821773273364365 1141287206183164977511637)
                  ·
                    refine ⟨26748918894917929160429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1141287206183164977511637 26748918894917929160429)
                    ·
                      rfl

theorem cell23_156280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_156280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156280 prefixEnd_156280 := by exact prefixLift 156280
  have htrace : WordTrace (prefixWord ++ tailWord_156280) baseStart_156280 baseEnd_156280 := by
    simpa [prefixWord, tailWord_156280, baseEnd_156280] using wordTrace_append hprefix tailTrace_156280
  have hstable : (prefixWord ++ tailWord_156280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156280).length < 2 ^ (prefixWord ++ tailWord_156280).sum := by decide
  have hdescent : baseEnd_156280 < baseStart_156280 := by decide
  rcases family_descends (prefixWord ++ tailWord_156280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156378 : List Nat := [3, 1, 1, 2, 2, 2, 5, 2, 1, 4]
def baseStart_156378 : Nat := 118140960795 + 156378 * 2 ^ 59
def prefixEnd_156378 : Nat := 4983230072969 + 3 ^ 40 * 156378 * 2
def baseEnd_156378 : Nat := 26765692596298134685279

theorem tailTrace_156378 : CollatzResearch.WordTrace tailWord_156378 prefixEnd_156378 26765692596298134685279 := by
  unfold tailWord_156378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1425893556869172020309447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3802382818317792054158525 1425893556869172020309447)
  ·
    refine ⟨2138840335303758030464171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1425893556869172020309447 2138840335303758030464171)
    ·
      refine ⟨3208260502955637045696257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2138840335303758030464171 3208260502955637045696257)
      ·
        refine ⟨2406195377216727784272193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3208260502955637045696257 2406195377216727784272193)
        ·
          refine ⟨1804646532912545838204145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2406195377216727784272193 1804646532912545838204145)
          ·
            refine ⟨1353484899684409378653109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1804646532912545838204145 1353484899684409378653109)
            ·
              refine ⟨126889209345413379248729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1353484899684409378653109 126889209345413379248729)
              ·
                refine ⟨95166907009060034436547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126889209345413379248729 95166907009060034436547)
                ·
                  refine ⟨142750360513590051654821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95166907009060034436547 142750360513590051654821)
                  ·
                    refine ⟨26765692596298134685279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142750360513590051654821 26765692596298134685279)
                    ·
                      rfl

theorem cell23_156378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_156378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156378 prefixEnd_156378 := by exact prefixLift 156378
  have htrace : WordTrace (prefixWord ++ tailWord_156378) baseStart_156378 baseEnd_156378 := by
    simpa [prefixWord, tailWord_156378, baseEnd_156378] using wordTrace_append hprefix tailTrace_156378
  have hstable : (prefixWord ++ tailWord_156378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156378).length < 2 ^ (prefixWord ++ tailWord_156378).sum := by decide
  have hdescent : baseEnd_156378 < baseStart_156378 := by decide
  rcases family_descends (prefixWord ++ tailWord_156378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156481 : List Nat := [1, 2, 5, 3, 1, 1, 10]
def baseStart_156481 : Nat := 118140960795 + 156481 * 2 ^ 59
def prefixEnd_156481 : Nat := 4983230072969 + 3 ^ 40 * 156481 * 2
def baseEnd_156481 : Nat := 991974892547006186023

theorem tailTrace_156481 : CollatzResearch.WordTrace tailWord_156481 prefixEnd_156481 991974892547006186023 := by
  unfold tailWord_156481
  simp only [CollatzResearch.WordTrace]
  refine ⟨5707330946103536672237297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3804887297402357781491531 5707330946103536672237297)
  ·
    refine ⟨4280498209577652504177973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5707330946103536672237297 4280498209577652504177973)
    ·
      refine ⟨401296707147904922266685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4280498209577652504177973 401296707147904922266685)
      ·
        refine ⟨150486265180464345850007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 401296707147904922266685 150486265180464345850007)
        ·
          refine ⟨225729397770696518775011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150486265180464345850007 225729397770696518775011)
          ·
            refine ⟨338594096656044778162517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225729397770696518775011 338594096656044778162517)
            ·
              refine ⟨991974892547006186023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 338594096656044778162517 991974892547006186023)
              ·
                rfl

theorem cell23_156481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 10].length) (baseStart_156481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156481 prefixEnd_156481 := by exact prefixLift 156481
  have htrace : WordTrace (prefixWord ++ tailWord_156481) baseStart_156481 baseEnd_156481 := by
    simpa [prefixWord, tailWord_156481, baseEnd_156481] using wordTrace_append hprefix tailTrace_156481
  have hstable : (prefixWord ++ tailWord_156481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156481).length < 2 ^ (prefixWord ++ tailWord_156481).sum := by decide
  have hdescent : baseEnd_156481 < baseStart_156481 := by decide
  rcases family_descends (prefixWord ++ tailWord_156481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156507 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 7, 8]
def baseStart_156507 : Nat := 118140960795 + 156507 * 2 ^ 59
def prefixEnd_156507 : Nat := 4983230072969 + 3 ^ 40 * 156507 * 2
def baseEnd_156507 : Nat := 26787772264441466447581

theorem tailTrace_156507 : CollatzResearch.WordTrace tailWord_156507 prefixEnd_156507 26787772264441466447581 := by
  unfold tailWord_156507
  simp only [CollatzResearch.WordTrace]
  refine ⟨5708279244009343112683775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3805519496006228741789183 5708279244009343112683775)
  ·
    refine ⟨8562418866014014669025663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5708279244009343112683775 8562418866014014669025663)
    ·
      refine ⟨12843628299021022003538495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8562418866014014669025663 12843628299021022003538495)
      ·
        refine ⟨19265442448531533005307743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12843628299021022003538495 19265442448531533005307743)
        ·
          refine ⟨28898163672797299507961615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19265442448531533005307743 28898163672797299507961615)
          ·
            refine ⟨43347245509195949261942423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28898163672797299507961615 43347245509195949261942423)
            ·
              refine ⟨65020868263793923892913635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43347245509195949261942423 65020868263793923892913635)
              ·
                refine ⟨97531302395690885839370453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65020868263793923892913635 97531302395690885839370453)
                ·
                  refine ⟨2285889899899005136860245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 97531302395690885839370453 2285889899899005136860245)
                  ·
                    refine ⟨26787772264441466447581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2285889899899005136860245 26787772264441466447581)
                    ·
                      rfl

theorem cell23_156507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 8].length) (baseStart_156507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156507 prefixEnd_156507 := by exact prefixLift 156507
  have htrace : WordTrace (prefixWord ++ tailWord_156507) baseStart_156507 baseEnd_156507 := by
    simpa [prefixWord, tailWord_156507, baseEnd_156507] using wordTrace_append hprefix tailTrace_156507
  have hstable : (prefixWord ++ tailWord_156507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156507).length < 2 ^ (prefixWord ++ tailWord_156507).sum := by decide
  have hdescent : baseEnd_156507 < baseStart_156507 := by decide
  rcases family_descends (prefixWord ++ tailWord_156507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156508 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_156508 : Nat := 118140960795 + 156508 * 2 ^ 59
def prefixEnd_156508 : Nat := 4983230072969 + 3 ^ 40 * 156508 * 2
def baseEnd_156508 : Nat := 80363830273978895430239

theorem tailTrace_156508 : CollatzResearch.WordTrace tailWord_156508 prefixEnd_156508 80363830273978895430239 := by
  unfold tailWord_156508
  simp only [CollatzResearch.WordTrace]
  refine ⟨2854157858502860141735089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3805543811337146855646785 2854157858502860141735089)
  ·
    refine ⟨2140618393877145106301317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2854157858502860141735089 2140618393877145106301317)
    ·
      refine ⟨401365948851964707431497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2140618393877145106301317 401365948851964707431497)
      ·
        refine ⟨301024461638973530573623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401365948851964707431497 301024461638973530573623)
        ·
          refine ⟨451536692458460295860435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301024461638973530573623 451536692458460295860435)
          ·
            refine ⟨677305038687690443790653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451536692458460295860435 677305038687690443790653)
            ·
              refine ⟨253989389507883916421495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 677305038687690443790653 253989389507883916421495)
              ·
                refine ⟨380984084261825874632243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253989389507883916421495 380984084261825874632243)
                ·
                  refine ⟨571476126392738811948365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380984084261825874632243 571476126392738811948365)
                  ·
                    refine ⟨214303547397277054480637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 571476126392738811948365 214303547397277054480637)
                    ·
                      refine ⟨80363830273978895430239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 214303547397277054480637 80363830273978895430239)
                      ·
                        rfl

theorem cell23_156508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_156508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156508 prefixEnd_156508 := by exact prefixLift 156508
  have htrace : WordTrace (prefixWord ++ tailWord_156508) baseStart_156508 baseEnd_156508 := by
    simpa [prefixWord, tailWord_156508, baseEnd_156508] using wordTrace_append hprefix tailTrace_156508
  have hstable : (prefixWord ++ tailWord_156508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156508).length < 2 ^ (prefixWord ++ tailWord_156508).sum := by decide
  have hdescent : baseEnd_156508 < baseStart_156508 := by decide
  rcases family_descends (prefixWord ++ tailWord_156508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156526 : List Nat := [4, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_156526 : Nat := 118140960795 + 156526 * 2 ^ 59
def prefixEnd_156526 : Nat := 4983230072969 + 3 ^ 40 * 156526 * 2
def baseEnd_156526 : Nat := 80373072925759825005157

theorem tailTrace_156526 : CollatzResearch.WordTrace tailWord_156526 prefixEnd_156526 80373072925759825005157 := by
  unfold tailWord_156526
  simp only [CollatzResearch.WordTrace]
  refine ⟨713621528867563669703179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3805981487293672905083621 713621528867563669703179)
  ·
    refine ⟨1070432293301345504554769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 713621528867563669703179 1070432293301345504554769)
    ·
      refine ⟨802824219976009128416077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1070432293301345504554769 802824219976009128416077)
      ·
        refine ⟨301059082491003423156029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 802824219976009128416077 301059082491003423156029)
        ·
          refine ⟨112897155934126283683511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301059082491003423156029 112897155934126283683511)
          ·
            refine ⟨169345733901189425525267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112897155934126283683511 169345733901189425525267)
            ·
              refine ⟨254018600851784138287901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169345733901189425525267 254018600851784138287901)
              ·
                refine ⟨95256975319419051857963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254018600851784138287901 95256975319419051857963)
                ·
                  refine ⟨142885462979128577786945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95256975319419051857963 142885462979128577786945)
                  ·
                    refine ⟨107164097234346433340209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142885462979128577786945 107164097234346433340209)
                    ·
                      refine ⟨80373072925759825005157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107164097234346433340209 80373072925759825005157)
                      ·
                        rfl

theorem cell23_156526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_156526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156526 prefixEnd_156526 := by exact prefixLift 156526
  have htrace : WordTrace (prefixWord ++ tailWord_156526) baseStart_156526 baseEnd_156526 := by
    simpa [prefixWord, tailWord_156526, baseEnd_156526] using wordTrace_append hprefix tailTrace_156526
  have hstable : (prefixWord ++ tailWord_156526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156526).length < 2 ^ (prefixWord ++ tailWord_156526).sum := by decide
  have hdescent : baseEnd_156526 < baseStart_156526 := by decide
  rcases family_descends (prefixWord ++ tailWord_156526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156531 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 1, 4, 2]
def baseStart_156531 : Nat := 118140960795 + 156531 * 2 ^ 59
def prefixEnd_156531 : Nat := 4983230072969 + 3 ^ 40 * 156531 * 2
def baseEnd_156531 : Nat := 80375640329032305442633

theorem tailTrace_156531 : CollatzResearch.WordTrace tailWord_156531 prefixEnd_156531 80375640329032305442633 := by
  unfold tailWord_156531
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709154595922395211557447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3806103063948263474371631 5709154595922395211557447)
  ·
    refine ⟨8563731893883592817336171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5709154595922395211557447 8563731893883592817336171)
    ·
      refine ⟨12845597840825389226004257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8563731893883592817336171 12845597840825389226004257)
      ·
        refine ⟨9634198380619041919503193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12845597840825389226004257 9634198380619041919503193)
        ·
          refine ⟨7225648785464281439627395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9634198380619041919503193 7225648785464281439627395)
          ·
            refine ⟨10838473178196422159441093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7225648785464281439627395 10838473178196422159441093)
            ·
              refine ⟨2032213720911829154895205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10838473178196422159441093 2032213720911829154895205)
              ·
                refine ⟨381040072670967966542851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2032213720911829154895205 381040072670967966542851)
                ·
                  refine ⟨571560109006451949814277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381040072670967966542851 571560109006451949814277)
                  ·
                    refine ⟨107167520438709740590177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 571560109006451949814277 107167520438709740590177)
                    ·
                      refine ⟨80375640329032305442633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107167520438709740590177 80375640329032305442633)
                      ·
                        rfl

theorem cell23_156531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 4, 2].length) (baseStart_156531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156531 prefixEnd_156531 := by exact prefixLift 156531
  have htrace : WordTrace (prefixWord ++ tailWord_156531) baseStart_156531 baseEnd_156531 := by
    simpa [prefixWord, tailWord_156531, baseEnd_156531] using wordTrace_append hprefix tailTrace_156531
  have hstable : (prefixWord ++ tailWord_156531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156531).length < 2 ^ (prefixWord ++ tailWord_156531).sum := by decide
  have hdescent : baseEnd_156531 < baseStart_156531 := by decide
  rcases family_descends (prefixWord ++ tailWord_156531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156544 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 4]
def baseStart_156544 : Nat := 118140960795 + 156544 * 2 ^ 59
def prefixEnd_156544 : Nat := 4983230072969 + 3 ^ 40 * 156544 * 2
def baseEnd_156544 : Nat := 80382315577540754580073

theorem tailTrace_156544 : CollatzResearch.WordTrace tailWord_156544 prefixEnd_156544 80382315577540754580073 := by
  unfold tailWord_156544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2854814372437649215890343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3806419163250198954520457 2854814372437649215890343)
  ·
    refine ⟨4282221558656473823835515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2854814372437649215890343 4282221558656473823835515)
    ·
      refine ⟨6423332337984710735753273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4282221558656473823835515 6423332337984710735753273)
      ·
        refine ⟨4817499253488533051814955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6423332337984710735753273 4817499253488533051814955)
        ·
          refine ⟨7226248880232799577722433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4817499253488533051814955 7226248880232799577722433)
          ·
            refine ⟨5419686660174599683291825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7226248880232799577722433 5419686660174599683291825)
            ·
              refine ⟨4064764995130949762468869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5419686660174599683291825 4064764995130949762468869)
              ·
                refine ⟨762143436587053080462913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4064764995130949762468869 762143436587053080462913)
                ·
                  refine ⟨571607577440289810347185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 762143436587053080462913 571607577440289810347185)
                  ·
                    refine ⟨428705683080217357760389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 571607577440289810347185 428705683080217357760389)
                    ·
                      refine ⟨80382315577540754580073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 428705683080217357760389 80382315577540754580073)
                      ·
                        rfl

theorem cell23_156544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_156544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156544 prefixEnd_156544 := by exact prefixLift 156544
  have htrace : WordTrace (prefixWord ++ tailWord_156544) baseStart_156544 baseEnd_156544 := by
    simpa [prefixWord, tailWord_156544, baseEnd_156544] using wordTrace_append hprefix tailTrace_156544
  have hstable : (prefixWord ++ tailWord_156544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156544).length < 2 ^ (prefixWord ++ tailWord_156544).sum := by decide
  have hdescent : baseEnd_156544 < baseStart_156544 := by decide
  rcases family_descends (prefixWord ++ tailWord_156544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156565 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 2, 2, 2]
def baseStart_156565 : Nat := 118140960795 + 156565 * 2 ^ 59
def prefixEnd_156565 : Nat := 4983230072969 + 3 ^ 40 * 156565 * 2
def baseEnd_156565 : Nat := 80393098671285172417477

theorem tailTrace_156565 : CollatzResearch.WordTrace tailWord_156565 prefixEnd_156565 80393098671285172417477 := by
  unfold tailWord_156565
  simp only [CollatzResearch.WordTrace]
  refine ⟨5710394677799219018295149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3806929785199479345530099 5710394677799219018295149)
  ·
    refine ⟨2141398004174707131860681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5710394677799219018295149 2141398004174707131860681)
    ·
      refine ⟨1606048503131030348895511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2141398004174707131860681 1606048503131030348895511)
      ·
        refine ⟨2409072754696545523343267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1606048503131030348895511 2409072754696545523343267)
        ·
          refine ⟨3613609132044818285014901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2409072754696545523343267 3613609132044818285014901)
          ·
            refine ⟨338775856129201714220147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3613609132044818285014901 338775856129201714220147)
            ·
              refine ⟨508163784193802571330221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338775856129201714220147 508163784193802571330221)
              ·
                refine ⟨190561419072675964248833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 508163784193802571330221 190561419072675964248833)
                ·
                  refine ⟨142921064304506973186625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190561419072675964248833 142921064304506973186625)
                  ·
                    refine ⟨107190798228380229889969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142921064304506973186625 107190798228380229889969)
                    ·
                      refine ⟨80393098671285172417477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107190798228380229889969 80393098671285172417477)
                      ·
                        rfl

theorem cell23_156565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_156565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156565 prefixEnd_156565 := by exact prefixLift 156565
  have htrace : WordTrace (prefixWord ++ tailWord_156565) baseStart_156565 baseEnd_156565 := by
    simpa [prefixWord, tailWord_156565, baseEnd_156565] using wordTrace_append hprefix tailTrace_156565
  have hstable : (prefixWord ++ tailWord_156565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156565).length < 2 ^ (prefixWord ++ tailWord_156565).sum := by decide
  have hdescent : baseEnd_156565 < baseStart_156565 := by decide
  rcases family_descends (prefixWord ++ tailWord_156565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156601 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 2, 5]
def baseStart_156601 : Nat := 118140960795 + 156601 * 2 ^ 59
def prefixEnd_156601 : Nat := 4983230072969 + 3 ^ 40 * 156601 * 2
def baseEnd_156601 : Nat := 26803861324949010522437

theorem tailTrace_156601 : CollatzResearch.WordTrace tailWord_156601 prefixEnd_156601 26803861324949010522437 := by
  unfold tailWord_156601
  simp only [CollatzResearch.WordTrace]
  refine ⟨5711707705668797166605657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3807805137112531444403771 5711707705668797166605657)
  ·
    refine ⟨4283780779251597874954243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5711707705668797166605657 4283780779251597874954243)
    ·
      refine ⟨6425671168877396812431365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4283780779251597874954243 6425671168877396812431365)
      ·
        refine ⟨1204813344164511902330881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6425671168877396812431365 1204813344164511902330881)
        ·
          refine ⟨903610008123383926748161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1204813344164511902330881 903610008123383926748161)
          ·
            refine ⟨677707506092537945061121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903610008123383926748161 677707506092537945061121)
            ·
              refine ⟨508280629569403458795841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677707506092537945061121 508280629569403458795841)
              ·
                refine ⟨381210472177052594096881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508280629569403458795841 381210472177052594096881)
                ·
                  refine ⟨285907854132789445572661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381210472177052594096881 285907854132789445572661)
                  ·
                    refine ⟨26803861324949010522437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 285907854132789445572661 26803861324949010522437)
                    ·
                      rfl

theorem cell23_156601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_156601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156601 prefixEnd_156601 := by exact prefixLift 156601
  have htrace : WordTrace (prefixWord ++ tailWord_156601) baseStart_156601 baseEnd_156601 := by
    simpa [prefixWord, tailWord_156601, baseEnd_156601] using wordTrace_append hprefix tailTrace_156601
  have hstable : (prefixWord ++ tailWord_156601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156601).length < 2 ^ (prefixWord ++ tailWord_156601).sum := by decide
  have hdescent : baseEnd_156601 < baseStart_156601 := by decide
  rcases family_descends (prefixWord ++ tailWord_156601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156698 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2]
def baseStart_156698 : Nat := 118140960795 + 156698 * 2 ^ 59
def prefixEnd_156698 : Nat := 4983230072969 + 3 ^ 40 * 156698 * 2
def baseEnd_156698 : Nat := 80461391598333152054365

theorem tailTrace_156698 : CollatzResearch.WordTrace tailWord_156698 prefixEnd_156698 80461391598333152054365 := by
  unfold tailWord_156698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1428811396579345683221687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3810163724211588488591165 1428811396579345683221687)
  ·
    refine ⟨2143217094869018524832531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1428811396579345683221687 2143217094869018524832531)
    ·
      refine ⟨3214825642303527787248797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2143217094869018524832531 3214825642303527787248797)
      ·
        refine ⟨1205559615863822920218299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3214825642303527787248797 1205559615863822920218299)
        ·
          refine ⟨1808339423795734380327449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205559615863822920218299 1808339423795734380327449)
          ·
            refine ⟨1356254567846800785245587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1808339423795734380327449 1356254567846800785245587)
            ·
              refine ⟨2034381851770201177868381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356254567846800785245587 2034381851770201177868381)
              ·
                refine ⟨762893194413825441700643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2034381851770201177868381 762893194413825441700643)
                ·
                  refine ⟨1144339791620738162550965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762893194413825441700643 1144339791620738162550965)
                  ·
                    refine ⟨107281855464444202739153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1144339791620738162550965 107281855464444202739153)
                    ·
                      refine ⟨80461391598333152054365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107281855464444202739153 80461391598333152054365)
                      ·
                        rfl

theorem cell23_156698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_156698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156698 prefixEnd_156698 := by exact prefixLift 156698
  have htrace : WordTrace (prefixWord ++ tailWord_156698) baseStart_156698 baseEnd_156698 := by
    simpa [prefixWord, tailWord_156698, baseEnd_156698] using wordTrace_append hprefix tailTrace_156698
  have hstable : (prefixWord ++ tailWord_156698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156698).length < 2 ^ (prefixWord ++ tailWord_156698).sum := by decide
  have hdescent : baseEnd_156698 < baseStart_156698 := by decide
  rcases family_descends (prefixWord ++ tailWord_156698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156741 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_156741 : Nat := 118140960795 + 156741 * 2 ^ 59
def prefixEnd_156741 : Nat := 4983230072969 + 3 ^ 40 * 156741 * 2
def baseEnd_156741 : Nat := 80483471266476483816667

theorem tailTrace_156741 : CollatzResearch.WordTrace tailWord_156741 prefixEnd_156741 80483471266476483816667 := by
  unfold tailWord_156741
  simp only [CollatzResearch.WordTrace]
  refine ⟨5716813925161601076702077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3811209283441067384468051 5716813925161601076702077)
  ·
    refine ⟨2143805221935600403763279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5716813925161601076702077 2143805221935600403763279)
    ·
      refine ⟨3215707832903400605644919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2143805221935600403763279 3215707832903400605644919)
      ·
        refine ⟨4823561749355100908467379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3215707832903400605644919 4823561749355100908467379)
        ·
          refine ⟨7235342624032651362701069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4823561749355100908467379 7235342624032651362701069)
          ·
            refine ⟨2713253484012244261012901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7235342624032651362701069 2713253484012244261012901)
            ·
              refine ⟨508735028252295798939919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2713253484012244261012901 508735028252295798939919)
              ·
                refine ⟨763102542378443698409879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508735028252295798939919 763102542378443698409879)
                ·
                  refine ⟨1144653813567665547614819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763102542378443698409879 1144653813567665547614819)
                  ·
                    refine ⟨1716980720351498321422229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1144653813567665547614819 1716980720351498321422229)
                    ·
                      refine ⟨80483471266476483816667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1716980720351498321422229 80483471266476483816667)
                      ·
                        rfl

theorem cell23_156741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_156741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156741 prefixEnd_156741 := by exact prefixLift 156741
  have htrace : WordTrace (prefixWord ++ tailWord_156741) baseStart_156741 baseEnd_156741 := by
    simpa [prefixWord, tailWord_156741, baseEnd_156741] using wordTrace_append hprefix tailTrace_156741
  have hstable : (prefixWord ++ tailWord_156741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156741).length < 2 ^ (prefixWord ++ tailWord_156741).sum := by decide
  have hdescent : baseEnd_156741 < baseStart_156741 := by decide
  rcases family_descends (prefixWord ++ tailWord_156741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156742 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_156742 : Nat := 118140960795 + 156742 * 2 ^ 59
def prefixEnd_156742 : Nat := 4983230072969 + 3 ^ 40 * 156742 * 2
def baseEnd_156742 : Nat := 26827994915710326634721

theorem tailTrace_156742 : CollatzResearch.WordTrace tailWord_156742 prefixEnd_156742 26827994915710326634721 := by
  unfold tailWord_156742
  simp only [CollatzResearch.WordTrace]
  refine ⟨178651574942436820234015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3811233598771985498325653 178651574942436820234015)
  ·
    refine ⟨267977362413655230351023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178651574942436820234015 267977362413655230351023)
    ·
      refine ⟨401966043620482845526535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267977362413655230351023 401966043620482845526535)
      ·
        refine ⟨602949065430724268289803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401966043620482845526535 602949065430724268289803)
        ·
          refine ⟨904423598146086402434705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602949065430724268289803 904423598146086402434705)
          ·
            refine ⟨678317698609564801826029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904423598146086402434705 678317698609564801826029)
            ·
              refine ⟨254369136978586800684761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 678317698609564801826029 254369136978586800684761)
              ·
                refine ⟨190776852733940100513571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254369136978586800684761 190776852733940100513571)
                ·
                  refine ⟨286165279100910150770357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190776852733940100513571 286165279100910150770357)
                  ·
                    refine ⟨26827994915710326634721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 286165279100910150770357 26827994915710326634721)
                    ·
                      rfl

theorem cell23_156742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_156742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156742 prefixEnd_156742 := by exact prefixLift 156742
  have htrace : WordTrace (prefixWord ++ tailWord_156742) baseStart_156742 baseEnd_156742 := by
    simpa [prefixWord, tailWord_156742, baseEnd_156742] using wordTrace_append hprefix tailTrace_156742
  have hstable : (prefixWord ++ tailWord_156742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156742).length < 2 ^ (prefixWord ++ tailWord_156742).sum := by decide
  have hdescent : baseEnd_156742 < baseStart_156742 := by decide
  rcases family_descends (prefixWord ++ tailWord_156742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156828 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_156828 : Nat := 118140960795 + 156828 * 2 ^ 59
def prefixEnd_156828 : Nat := 4983230072969 + 3 ^ 40 * 156828 * 2
def baseEnd_156828 : Nat := 26842714694472547809589

theorem tailTrace_156828 : CollatzResearch.WordTrace tailWord_156828 prefixEnd_156828 26842714694472547809589 := by
  unfold tailWord_156828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859993537923207467559569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3813324717230943290079425 2859993537923207467559569)
  ·
    refine ⟨2144995153442405600669677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2859993537923207467559569 2144995153442405600669677)
    ·
      refine ⟨804373182540902100251129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2144995153442405600669677 804373182540902100251129)
      ·
        refine ⟨603279886905676575188347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 804373182540902100251129 603279886905676575188347)
        ·
          refine ⟨904919830358514862782521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603279886905676575188347 904919830358514862782521)
          ·
            refine ⟨678689872768886147086891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904919830358514862782521 678689872768886147086891)
            ·
              refine ⟨1018034809153329220630337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678689872768886147086891 1018034809153329220630337)
              ·
                refine ⟨763526106864996915472753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018034809153329220630337 763526106864996915472753)
                ·
                  refine ⟨572644580148747686604565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 763526106864996915472753 572644580148747686604565)
                  ·
                    refine ⟨26842714694472547809589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 572644580148747686604565 26842714694472547809589)
                    ·
                      rfl

theorem cell23_156828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_156828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156828 prefixEnd_156828 := by exact prefixLift 156828
  have htrace : WordTrace (prefixWord ++ tailWord_156828) baseStart_156828 baseEnd_156828 := by
    simpa [prefixWord, tailWord_156828, baseEnd_156828] using wordTrace_append hprefix tailTrace_156828
  have hstable : (prefixWord ++ tailWord_156828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156828).length < 2 ^ (prefixWord ++ tailWord_156828).sum := by decide
  have hdescent : baseEnd_156828 < baseStart_156828 := by decide
  rcases family_descends (prefixWord ++ tailWord_156828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156903 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_156903 : Nat := 118140960795 + 156903 * 2 ^ 59
def prefixEnd_156903 : Nat := 4983230072969 + 3 ^ 40 * 156903 * 2
def baseEnd_156903 : Nat := 80566655132504849990923

theorem tailTrace_156903 : CollatzResearch.WordTrace tailWord_156903 prefixEnd_156903 80566655132504849990923 := by
  unfold tailWord_156903
  simp only [CollatzResearch.WordTrace]
  refine ⟨5722722550574702744099363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3815148367049801829399575 5722722550574702744099363)
  ·
    refine ⟨8584083825862054116149045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5722722550574702744099363 8584083825862054116149045)
    ·
      refine ⟨804757858674567573388973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8584083825862054116149045 804757858674567573388973)
      ·
        refine ⟨301784197002962840020865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 804757858674567573388973 301784197002962840020865)
        ·
          refine ⟨226338147752222130015649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301784197002962840020865 226338147752222130015649)
          ·
            refine ⟨169753610814166597511737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226338147752222130015649 169753610814166597511737)
            ·
              refine ⟨127315208110624948133803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169753610814166597511737 127315208110624948133803)
              ·
                refine ⟨190972812165937422200705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127315208110624948133803 190972812165937422200705)
                ·
                  refine ⟨143229609124453066650529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190972812165937422200705 143229609124453066650529)
                  ·
                    refine ⟨107422206843339799987897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 143229609124453066650529 107422206843339799987897)
                    ·
                      refine ⟨80566655132504849990923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107422206843339799987897 80566655132504849990923)
                      ·
                        rfl

theorem cell23_156903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_156903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156903 prefixEnd_156903 := by exact prefixLift 156903
  have htrace : WordTrace (prefixWord ++ tailWord_156903) baseStart_156903 baseEnd_156903 := by
    simpa [prefixWord, tailWord_156903, baseEnd_156903] using wordTrace_append hprefix tailTrace_156903
  have hstable : (prefixWord ++ tailWord_156903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156903).length < 2 ^ (prefixWord ++ tailWord_156903).sum := by decide
  have hdescent : baseEnd_156903 < baseStart_156903 := by decide
  rcases family_descends (prefixWord ++ tailWord_156903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156925 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 6, 4, 2]
def baseStart_156925 : Nat := 118140960795 + 156925 * 2 ^ 59
def prefixEnd_156925 : Nat := 4983230072969 + 3 ^ 40 * 156925 * 2
def baseEnd_156925 : Nat := 80577951706903763915821

theorem tailTrace_156925 : CollatzResearch.WordTrace tailWord_156925 prefixEnd_156925 80577951706903763915821 := by
  unfold tailWord_156925
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723524956495000501400229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3815683304330000334266819 5723524956495000501400229)
  ·
    refine ⟨1073160929342812594012543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5723524956495000501400229 1073160929342812594012543)
    ·
      refine ⟨1609741394014218891018815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1073160929342812594012543 1609741394014218891018815)
      ·
        refine ⟨2414612091021328336528223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609741394014218891018815 2414612091021328336528223)
        ·
          refine ⟨3621918136531992504792335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414612091021328336528223 3621918136531992504792335)
          ·
            refine ⟨5432877204797988757188503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3621918136531992504792335 5432877204797988757188503)
            ·
              refine ⟨8149315807196983135782755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5432877204797988757188503 8149315807196983135782755)
              ·
                refine ⟨12223973710795474703674133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8149315807196983135782755 12223973710795474703674133)
                ·
                  refine ⟨572998767693537876734725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12223973710795474703674133 572998767693537876734725)
                  ·
                    refine ⟨107437268942538351887761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 572998767693537876734725 107437268942538351887761)
                    ·
                      refine ⟨80577951706903763915821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107437268942538351887761 80577951706903763915821)
                      ·
                        rfl

theorem cell23_156925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_156925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156925 prefixEnd_156925 := by exact prefixLift 156925
  have htrace : WordTrace (prefixWord ++ tailWord_156925) baseStart_156925 baseEnd_156925 := by
    simpa [prefixWord, tailWord_156925, baseEnd_156925] using wordTrace_append hprefix tailTrace_156925
  have hstable : (prefixWord ++ tailWord_156925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156925).length < 2 ^ (prefixWord ++ tailWord_156925).sum := by decide
  have hdescent : baseEnd_156925 < baseStart_156925 := by decide
  rcases family_descends (prefixWord ++ tailWord_156925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156938 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_156938 : Nat := 118140960795 + 156938 * 2 ^ 59
def prefixEnd_156938 : Nat := 4983230072969 + 3 ^ 40 * 156938 * 2
def baseEnd_156938 : Nat := 80584626955412213053261

theorem tailTrace_156938 : CollatzResearch.WordTrace tailWord_156938 prefixEnd_156938 80584626955412213053261 := by
  unfold tailWord_156938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430999776361975930405867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3815999403631935814415645 1430999776361975930405867)
  ·
    refine ⟨2146499664542963895608801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1430999776361975930405867 2146499664542963895608801)
    ·
      refine ⟨1609874748407222921706601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2146499664542963895608801 1609874748407222921706601)
      ·
        refine ⟨1207406061305417191279951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1609874748407222921706601 1207406061305417191279951)
        ·
          refine ⟨1811109091958125786919927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207406061305417191279951 1811109091958125786919927)
          ·
            refine ⟨2716663637937188680379891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811109091958125786919927 2716663637937188680379891)
            ·
              refine ⟨4074995456905783020569837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716663637937188680379891 4074995456905783020569837)
              ·
                refine ⟨1528123296339668632713689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4074995456905783020569837 1528123296339668632713689)
                ·
                  refine ⟨1146092472254751474535267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1528123296339668632713689 1146092472254751474535267)
                  ·
                    refine ⟨1719138708382127211802901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1146092472254751474535267 1719138708382127211802901)
                    ·
                      refine ⟨80584626955412213053261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1719138708382127211802901 80584626955412213053261)
                      ·
                        rfl

theorem cell23_156938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_156938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156938 prefixEnd_156938 := by exact prefixLift 156938
  have htrace : WordTrace (prefixWord ++ tailWord_156938) baseStart_156938 baseEnd_156938 := by
    simpa [prefixWord, tailWord_156938, baseEnd_156938] using wordTrace_append hprefix tailTrace_156938
  have hstable : (prefixWord ++ tailWord_156938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156938).length < 2 ^ (prefixWord ++ tailWord_156938).sum := by decide
  have hdescent : baseEnd_156938 < baseStart_156938 := by decide
  rcases family_descends (prefixWord ++ tailWord_156938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156945 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 3]
def baseStart_156945 : Nat := 118140960795 + 156945 * 2 ^ 59
def prefixEnd_156945 : Nat := 4983230072969 + 3 ^ 40 * 156945 * 2
def baseEnd_156945 : Nat := 80588221319993685665729

theorem tailTrace_156945 : CollatzResearch.WordTrace tailWord_156945 prefixEnd_156945 80588221319993685665729 := by
  unfold tailWord_156945
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724254416422543917128289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3816169610948362611418859 5724254416422543917128289)
  ·
    refine ⟨4293190812316907937846217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5724254416422543917128289 4293190812316907937846217)
    ·
      refine ⟨3219893109237680953384663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4293190812316907937846217 3219893109237680953384663)
      ·
        refine ⟨4829839663856521430076995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219893109237680953384663 4829839663856521430076995)
        ·
          refine ⟨7244759495784782145115493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829839663856521430076995 7244759495784782145115493)
          ·
            refine ⟨1358392405459646652209155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7244759495784782145115493 1358392405459646652209155)
            ·
              refine ⟨2037588608189469978313733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358392405459646652209155 2037588608189469978313733)
              ·
                refine ⟨382047864035525620933825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2037588608189469978313733 382047864035525620933825)
                ·
                  refine ⟨286535898026644215700369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382047864035525620933825 286535898026644215700369)
                  ·
                    refine ⟨214901923519983161775277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 286535898026644215700369 214901923519983161775277)
                    ·
                      refine ⟨80588221319993685665729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 214901923519983161775277 80588221319993685665729)
                      ·
                        rfl

theorem cell23_156945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_156945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156945 prefixEnd_156945 := by exact prefixLift 156945
  have htrace : WordTrace (prefixWord ++ tailWord_156945) baseStart_156945 baseEnd_156945 := by
    simpa [prefixWord, tailWord_156945, baseEnd_156945] using wordTrace_append hprefix tailTrace_156945
  have hstable : (prefixWord ++ tailWord_156945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156945).length < 2 ^ (prefixWord ++ tailWord_156945).sum := by decide
  have hdescent : baseEnd_156945 < baseStart_156945 := by decide
  rcases family_descends (prefixWord ++ tailWord_156945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156965 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 6]
def baseStart_156965 : Nat := 118140960795 + 156965 * 2 ^ 59
def prefixEnd_156965 : Nat := 4983230072969 + 3 ^ 40 * 156965 * 2
def baseEnd_156965 : Nat := 8955387881453734157293

theorem tailTrace_156965 : CollatzResearch.WordTrace tailWord_156965 prefixEnd_156965 8955387881453734157293 := by
  unfold tailWord_156965
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724983876350087332856349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3816655917566724888570899 5724983876350087332856349)
  ·
    refine ⟨2146868953631282749821131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5724983876350087332856349 2146868953631282749821131)
    ·
      refine ⟨3220303430446924124731697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146868953631282749821131 3220303430446924124731697)
      ·
        refine ⟨2415227572835193093548773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3220303430446924124731697 2415227572835193093548773)
        ·
          refine ⟨452855169906598705040395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2415227572835193093548773 452855169906598705040395)
          ·
            refine ⟨679282754859898057560593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452855169906598705040395 679282754859898057560593)
            ·
              refine ⟨509462066144923543170445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679282754859898057560593 509462066144923543170445)
              ·
                refine ⟨191048274804346328688917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 509462066144923543170445 191048274804346328688917)
                ·
                  refine ⟨8955387881453734157293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 191048274804346328688917 8955387881453734157293)
                  ·
                    rfl

theorem cell23_156965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_156965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_156965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_156965 prefixEnd_156965 := by exact prefixLift 156965
  have htrace : WordTrace (prefixWord ++ tailWord_156965) baseStart_156965 baseEnd_156965 := by
    simpa [prefixWord, tailWord_156965, baseEnd_156965] using wordTrace_append hprefix tailTrace_156965
  have hstable : (prefixWord ++ tailWord_156965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156965).length < 2 ^ (prefixWord ++ tailWord_156965).sum := by decide
  have hdescent : baseEnd_156965 < baseStart_156965 := by decide
  rcases family_descends (prefixWord ++ tailWord_156965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157002 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2]
def baseStart_157002 : Nat := 118140960795 + 157002 * 2 ^ 59
def prefixEnd_157002 : Nat := 4983230072969 + 3 ^ 40 * 157002 * 2
def baseEnd_157002 : Nat := 80617489717299962652967

theorem tailTrace_157002 : CollatzResearch.WordTrace tailWord_157002 prefixEnd_157002 80617489717299962652967 := by
  unfold tailWord_157002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1431583344304010662988315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3817555584810695101302173 1431583344304010662988315)
  ·
    refine ⟨2147375016456015994482473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1431583344304010662988315 2147375016456015994482473)
    ·
      refine ⟨1610531262342011995861855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2147375016456015994482473 1610531262342011995861855)
      ·
        refine ⟨2415796893513017993792783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1610531262342011995861855 2415796893513017993792783)
        ·
          refine ⟨3623695340269526990689175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2415796893513017993792783 3623695340269526990689175)
          ·
            refine ⟨5435543010404290486033763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3623695340269526990689175 5435543010404290486033763)
            ·
              refine ⟨8153314515606435729050645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435543010404290486033763 8153314515606435729050645)
              ·
                refine ⟨382186617919051674799249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8153314515606435729050645 382186617919051674799249)
                ·
                  refine ⟨286639963439288756099437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382186617919051674799249 286639963439288756099437)
                  ·
                    refine ⟨107489986289733283537289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286639963439288756099437 107489986289733283537289)
                    ·
                      refine ⟨80617489717299962652967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107489986289733283537289 80617489717299962652967)
                      ·
                        rfl

theorem cell23_157002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_157002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157002 prefixEnd_157002 := by exact prefixLift 157002
  have htrace : WordTrace (prefixWord ++ tailWord_157002) baseStart_157002 baseEnd_157002 := by
    simpa [prefixWord, tailWord_157002, baseEnd_157002] using wordTrace_append hprefix tailTrace_157002
  have hstable : (prefixWord ++ tailWord_157002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157002).length < 2 ^ (prefixWord ++ tailWord_157002).sum := by decide
  have hdescent : baseEnd_157002 < baseStart_157002 := by decide
  rcases family_descends (prefixWord ++ tailWord_157002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157009 : List Nat := [1, 2, 2, 1, 4, 1, 1, 6, 1, 1, 3]
def baseStart_157009 : Nat := 118140960795 + 157009 * 2 ^ 59
def prefixEnd_157009 : Nat := 4983230072969 + 3 ^ 40 * 157009 * 2
def baseEnd_157009 : Nat := 80621084081881435265435

theorem tailTrace_157009 : CollatzResearch.WordTrace tailWord_157009 prefixEnd_157009 80621084081881435265435 := by
  unfold tailWord_157009
  simp only [CollatzResearch.WordTrace]
  refine ⟨5726588688190682847458081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3817725792127121898305387 5726588688190682847458081)
  ·
    refine ⟨4294941516143012135593561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5726588688190682847458081 4294941516143012135593561)
    ·
      refine ⟨3221206137107259101695171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4294941516143012135593561 3221206137107259101695171)
      ·
        refine ⟨4831809205660888652542757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3221206137107259101695171 4831809205660888652542757)
        ·
          refine ⟨905964226061416622351767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4831809205660888652542757 905964226061416622351767)
          ·
            refine ⟨1358946339092124933527651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905964226061416622351767 1358946339092124933527651)
            ·
              refine ⟨2038419508638187400291477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358946339092124933527651 2038419508638187400291477)
              ·
                refine ⟨95550914467415034388663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2038419508638187400291477 95550914467415034388663)
                ·
                  refine ⟨143326371701122551582995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95550914467415034388663 143326371701122551582995)
                  ·
                    refine ⟨214989557551683827374493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 143326371701122551582995 214989557551683827374493)
                    ·
                      refine ⟨80621084081881435265435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 214989557551683827374493 80621084081881435265435)
                      ·
                        rfl

theorem cell23_157009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 1, 1, 3].length) (baseStart_157009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157009 prefixEnd_157009 := by exact prefixLift 157009
  have htrace : WordTrace (prefixWord ++ tailWord_157009) baseStart_157009 baseEnd_157009 := by
    simpa [prefixWord, tailWord_157009, baseEnd_157009] using wordTrace_append hprefix tailTrace_157009
  have hstable : (prefixWord ++ tailWord_157009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157009).length < 2 ^ (prefixWord ++ tailWord_157009).sum := by decide
  have hdescent : baseEnd_157009 < baseStart_157009 := by decide
  rcases family_descends (prefixWord ++ tailWord_157009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157052 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_157052 : Nat := 118140960795 + 157052 * 2 ^ 59
def prefixEnd_157052 : Nat := 4983230072969 + 3 ^ 40 * 157052 * 2
def baseEnd_157052 : Nat := 80643163750024767027737

theorem tailTrace_157052 : CollatzResearch.WordTrace tailWord_157052 prefixEnd_157052 80643163750024767027737 := by
  unfold tailWord_157052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864078513517450595636705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3818771351356600794182273 2864078513517450595636705)
  ·
    refine ⟨2148058885138087946727529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2864078513517450595636705 2148058885138087946727529)
    ·
      refine ⟨1611044163853565960045647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2148058885138087946727529 1611044163853565960045647)
      ·
        refine ⟨2416566245780348940068471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1611044163853565960045647 2416566245780348940068471)
        ·
          refine ⟨3624849368670523410102707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416566245780348940068471 3624849368670523410102707)
          ·
            refine ⟨5437274053005785115154061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624849368670523410102707 5437274053005785115154061)
            ·
              refine ⟨2038977769877169418182773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5437274053005785115154061 2038977769877169418182773)
              ·
                refine ⟨191154165925984632954635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2038977769877169418182773 191154165925984632954635)
                ·
                  refine ⟨286731248888976949431953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191154165925984632954635 286731248888976949431953)
                  ·
                    refine ⟨215048436666732712073965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 286731248888976949431953 215048436666732712073965)
                    ·
                      refine ⟨80643163750024767027737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 215048436666732712073965 80643163750024767027737)
                      ·
                        rfl

theorem cell23_157052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_157052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157052 prefixEnd_157052 := by exact prefixLift 157052
  have htrace : WordTrace (prefixWord ++ tailWord_157052) baseStart_157052 baseEnd_157052 := by
    simpa [prefixWord, tailWord_157052, baseEnd_157052] using wordTrace_append hprefix tailTrace_157052
  have hstable : (prefixWord ++ tailWord_157052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157052).length < 2 ^ (prefixWord ++ tailWord_157052).sum := by decide
  have hdescent : baseEnd_157052 < baseStart_157052 := by decide
  rcases family_descends (prefixWord ++ tailWord_157052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157076 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_157076 : Nat := 118140960795 + 157076 * 2 ^ 59
def prefixEnd_157076 : Nat := 4983230072969 + 3 ^ 40 * 157076 * 2
def baseEnd_157076 : Nat := 26885162428577557709209

theorem tailTrace_157076 : CollatzResearch.WordTrace tailWord_157076 prefixEnd_157076 26885162428577557709209 := by
  unfold tailWord_157076
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864516189473976645073541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3819354919298635526764721 2864516189473976645073541)
  ·
    refine ⟨537096785526370620951289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2864516189473976645073541 537096785526370620951289)
    ·
      refine ⟨402822589144777965713467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 537096785526370620951289 402822589144777965713467)
      ·
        refine ⟨604233883717166948570201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402822589144777965713467 604233883717166948570201)
        ·
          refine ⟨453175412787875211427651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 604233883717166948570201 453175412787875211427651)
          ·
            refine ⟨679763119181812817141477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453175412787875211427651 679763119181812817141477)
            ·
              refine ⟨127455584846589903214027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 679763119181812817141477 127455584846589903214027)
              ·
                refine ⟨191183377269884854821041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127455584846589903214027 191183377269884854821041)
                ·
                  refine ⟨143387532952413641115781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191183377269884854821041 143387532952413641115781)
                  ·
                    refine ⟨26885162428577557709209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143387532952413641115781 26885162428577557709209)
                    ·
                      rfl

theorem cell23_157076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_157076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157076 prefixEnd_157076 := by exact prefixLift 157076
  have htrace : WordTrace (prefixWord ++ tailWord_157076) baseStart_157076 baseEnd_157076 := by
    simpa [prefixWord, tailWord_157076, baseEnd_157076] using wordTrace_append hprefix tailTrace_157076
  have hstable : (prefixWord ++ tailWord_157076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157076).length < 2 ^ (prefixWord ++ tailWord_157076).sum := by decide
  have hdescent : baseEnd_157076 < baseStart_157076 := by decide
  rcases family_descends (prefixWord ++ tailWord_157076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157082 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3]
def baseStart_157082 : Nat := 118140960795 + 157082 * 2 ^ 59
def prefixEnd_157082 : Nat := 4983230072969 + 3 ^ 40 * 157082 * 2
def baseEnd_157082 : Nat := 80658568169659649652599

theorem tailTrace_157082 : CollatzResearch.WordTrace tailWord_157082 prefixEnd_157082 80658568169659649652599 := by
  unfold tailWord_157082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432312804231554078716375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3819500811284144209910333 1432312804231554078716375)
  ·
    refine ⟨2148469206347331118074563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1432312804231554078716375 2148469206347331118074563)
    ·
      refine ⟨3222703809520996677111845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2148469206347331118074563 3222703809520996677111845)
      ·
        refine ⟨604256964285186876958471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3222703809520996677111845 604256964285186876958471)
        ·
          refine ⟨906385446427780315437707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604256964285186876958471 906385446427780315437707)
          ·
            refine ⟨1359578169641670473156561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906385446427780315437707 1359578169641670473156561)
            ·
              refine ⟨1019683627231252854867421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359578169641670473156561 1019683627231252854867421)
              ·
                refine ⟨382381360211719820575283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1019683627231252854867421 382381360211719820575283)
                ·
                  refine ⟨573572040317579730862925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382381360211719820575283 573572040317579730862925)
                  ·
                    refine ⟨215089515119092399073597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 573572040317579730862925 215089515119092399073597)
                    ·
                      refine ⟨80658568169659649652599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 215089515119092399073597 80658568169659649652599)
                      ·
                        rfl

theorem cell23_157082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_157082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157082 prefixEnd_157082 := by exact prefixLift 157082
  have htrace : WordTrace (prefixWord ++ tailWord_157082) baseStart_157082 baseEnd_157082 := by
    simpa [prefixWord, tailWord_157082, baseEnd_157082] using wordTrace_append hprefix tailTrace_157082
  have hstable : (prefixWord ++ tailWord_157082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157082).length < 2 ^ (prefixWord ++ tailWord_157082).sum := by decide
  have hdescent : baseEnd_157082 < baseStart_157082 := by decide
  rcases family_descends (prefixWord ++ tailWord_157082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157086 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_157086 : Nat := 118140960795 + 157086 * 2 ^ 59
def prefixEnd_157086 : Nat := 4983230072969 + 3 ^ 40 * 157086 * 2
def baseEnd_157086 : Nat := 80660622092277634002581

theorem tailTrace_157086 : CollatzResearch.WordTrace tailWord_157086 prefixEnd_157086 80660622092277634002581 := by
  unfold tailWord_157086
  simp only [CollatzResearch.WordTrace]
  refine ⟨716174638613965624751389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3819598072607816665340741 716174638613965624751389)
  ·
    refine ⟨268565489480237109281771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 716174638613965624751389 268565489480237109281771)
    ·
      refine ⟨402848234220355663922657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268565489480237109281771 402848234220355663922657)
      ·
        refine ⟨302136175665266747941993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402848234220355663922657 302136175665266747941993)
        ·
          refine ⟨226602131748950060956495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302136175665266747941993 226602131748950060956495)
          ·
            refine ⟨339903197623425091434743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226602131748950060956495 339903197623425091434743)
            ·
              refine ⟨509854796435137637152115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339903197623425091434743 509854796435137637152115)
              ·
                refine ⟨764782194652706455728173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509854796435137637152115 764782194652706455728173)
                ·
                  refine ⟨286793322994764920898065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764782194652706455728173 286793322994764920898065)
                  ·
                    refine ⟨215094992246073690673549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 286793322994764920898065 215094992246073690673549)
                    ·
                      refine ⟨80660622092277634002581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 215094992246073690673549 80660622092277634002581)
                      ·
                        rfl

theorem cell23_157086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_157086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157086 prefixEnd_157086 := by exact prefixLift 157086
  have htrace : WordTrace (prefixWord ++ tailWord_157086) baseStart_157086 baseEnd_157086 := by
    simpa [prefixWord, tailWord_157086, baseEnd_157086] using wordTrace_append hprefix tailTrace_157086
  have hstable : (prefixWord ++ tailWord_157086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157086).length < 2 ^ (prefixWord ++ tailWord_157086).sum := by decide
  have hdescent : baseEnd_157086 < baseStart_157086 := by decide
  rcases family_descends (prefixWord ++ tailWord_157086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157132 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_157132 : Nat := 118140960795 + 157132 * 2 ^ 59
def prefixEnd_157132 : Nat := 4983230072969 + 3 ^ 40 * 157132 * 2
def baseEnd_157132 : Nat := 26894747400794818009123

theorem tailTrace_157132 : CollatzResearch.WordTrace tailWord_157132 prefixEnd_157132 26894747400794818009123 := by
  unfold tailWord_157132
  simp only [CollatzResearch.WordTrace]
  refine ⟨2865537433372537427092825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3820716577830049902790433 2865537433372537427092825)
  ·
    refine ⟨2149153075029403070319619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2865537433372537427092825 2149153075029403070319619)
    ·
      refine ⟨3223729612544104605479429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2149153075029403070319619 3223729612544104605479429)
      ·
        refine ⟨604449302352019613527393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3223729612544104605479429 604449302352019613527393)
        ·
          refine ⟨453336976764014710145545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 604449302352019613527393 453336976764014710145545)
          ·
            refine ⟨340002732573011032609159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453336976764014710145545 340002732573011032609159)
            ·
              refine ⟨510004098859516548913739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340002732573011032609159 510004098859516548913739)
              ·
                refine ⟨765006148289274823370609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510004098859516548913739 765006148289274823370609)
                ·
                  refine ⟨573754611216956117527957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765006148289274823370609 573754611216956117527957)
                  ·
                    refine ⟨26894747400794818009123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 573754611216956117527957 26894747400794818009123)
                    ·
                      rfl

theorem cell23_157132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_157132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157132 prefixEnd_157132 := by exact prefixLift 157132
  have htrace : WordTrace (prefixWord ++ tailWord_157132) baseStart_157132 baseEnd_157132 := by
    simpa [prefixWord, tailWord_157132, baseEnd_157132] using wordTrace_append hprefix tailTrace_157132
  have hstable : (prefixWord ++ tailWord_157132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157132).length < 2 ^ (prefixWord ++ tailWord_157132).sum := by decide
  have hdescent : baseEnd_157132 < baseStart_157132 := by decide
  rcases family_descends (prefixWord ++ tailWord_157132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157135 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 4]
def baseStart_157135 : Nat := 118140960795 + 157135 * 2 ^ 59
def prefixEnd_157135 : Nat := 4983230072969 + 3 ^ 40 * 157135 * 2
def baseEnd_157135 : Nat := 80685782644347942289855

theorem tailTrace_157135 : CollatzResearch.WordTrace tailWord_157135 prefixEnd_157135 80685782644347942289855 := by
  unfold tailWord_157135
  simp only [CollatzResearch.WordTrace]
  refine ⟨5731184285734206366544859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3820789523822804244363239 5731184285734206366544859)
  ·
    refine ⟨8596776428601309549817289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5731184285734206366544859 8596776428601309549817289)
    ·
      refine ⟨6447582321450982162362967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8596776428601309549817289 6447582321450982162362967)
      ·
        refine ⟨9671373482176473243544451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6447582321450982162362967 9671373482176473243544451)
        ·
          refine ⟨14507060223264709865316677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9671373482176473243544451 14507060223264709865316677)
          ·
            refine ⟨2720073791862133099746877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14507060223264709865316677 2720073791862133099746877)
            ·
              refine ⟨1020027671948299912405079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2720073791862133099746877 1020027671948299912405079)
              ·
                refine ⟨1530041507922449868607619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020027671948299912405079 1530041507922449868607619)
                ·
                  refine ⟨2295062261883674802911429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530041507922449868607619 2295062261883674802911429)
                  ·
                    refine ⟨430324174103189025545893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2295062261883674802911429 430324174103189025545893)
                    ·
                      refine ⟨80685782644347942289855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 430324174103189025545893 80685782644347942289855)
                      ·
                        rfl

theorem cell23_157135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_157135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157135 prefixEnd_157135 := by exact prefixLift 157135
  have htrace : WordTrace (prefixWord ++ tailWord_157135) baseStart_157135 baseEnd_157135 := by
    simpa [prefixWord, tailWord_157135, baseEnd_157135] using wordTrace_append hprefix tailTrace_157135
  have hstable : (prefixWord ++ tailWord_157135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157135).length < 2 ^ (prefixWord ++ tailWord_157135).sum := by decide
  have hdescent : baseEnd_157135 < baseStart_157135 := by decide
  rcases family_descends (prefixWord ++ tailWord_157135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157145 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 9]
def baseStart_157145 : Nat := 118140960795 + 157145 * 2 ^ 59
def prefixEnd_157145 : Nat := 4983230072969 + 3 ^ 40 * 157145 * 2
def baseEnd_157145 : Nat := 8965657494543655907201

theorem tailTrace_157145 : CollatzResearch.WordTrace tailWord_157145 prefixEnd_157145 8965657494543655907201 := by
  unfold tailWord_157145
  simp only [CollatzResearch.WordTrace]
  refine ⟨5731549015697978074408889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3821032677131985382939259 5731549015697978074408889)
  ·
    refine ⟨4298661761773483555806667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5731549015697978074408889 4298661761773483555806667)
    ·
      refine ⟨6447992642660225333710001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4298661761773483555806667 6447992642660225333710001)
      ·
        refine ⟨4835994481995169000282501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6447992642660225333710001 4835994481995169000282501)
        ·
          refine ⟨906748965374094187552969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4835994481995169000282501 906748965374094187552969)
          ·
            refine ⟨680061724030570640664727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 906748965374094187552969 680061724030570640664727)
            ·
              refine ⟨1020092586045855960997091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680061724030570640664727 1020092586045855960997091)
              ·
                refine ⟨1530138879068783941495637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020092586045855960997091 1530138879068783941495637)
                ·
                  refine ⟨8965657494543655907201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1530138879068783941495637 8965657494543655907201)
                  ·
                    rfl

theorem cell23_157145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 9].length) (baseStart_157145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157145 prefixEnd_157145 := by exact prefixLift 157145
  have htrace : WordTrace (prefixWord ++ tailWord_157145) baseStart_157145 baseEnd_157145 := by
    simpa [prefixWord, tailWord_157145, baseEnd_157145] using wordTrace_append hprefix tailTrace_157145
  have hstable : (prefixWord ++ tailWord_157145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157145).length < 2 ^ (prefixWord ++ tailWord_157145).sum := by decide
  have hdescent : baseEnd_157145 < baseStart_157145 := by decide
  rcases family_descends (prefixWord ++ tailWord_157145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157173 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_157173 : Nat := 118140960795 + 157173 * 2 ^ 59
def prefixEnd_157173 : Nat := 4983230072969 + 3 ^ 40 * 157173 * 2
def baseEnd_157173 : Nat := 80705294909218793614681

theorem tailTrace_157173 : CollatzResearch.WordTrace tailWord_157173 prefixEnd_157173 80705294909218793614681 := by
  unfold tailWord_157173
  simp only [CollatzResearch.WordTrace]
  refine ⟨5732570259596538856428173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3821713506397692570952115 5732570259596538856428173)
  ·
    refine ⟨2149713847348702071160565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5732570259596538856428173 2149713847348702071160565)
    ·
      refine ⟨201535673188940819171303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2149713847348702071160565 201535673188940819171303)
      ·
        refine ⟨302303509783411228756955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201535673188940819171303 302303509783411228756955)
        ·
          refine ⟨453455264675116843135433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302303509783411228756955 453455264675116843135433)
          ·
            refine ⟨340091448506337632351575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453455264675116843135433 340091448506337632351575)
            ·
              refine ⟨510137172759506448527363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340091448506337632351575 510137172759506448527363)
              ·
                refine ⟨765205759139259672791045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510137172759506448527363 765205759139259672791045)
                ·
                  refine ⟨143476079838611188648321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765205759139259672791045 143476079838611188648321)
                  ·
                    refine ⟨107607059878958391486241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 143476079838611188648321 107607059878958391486241)
                    ·
                      refine ⟨80705294909218793614681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107607059878958391486241 80705294909218793614681)
                      ·
                        rfl

theorem cell23_157173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_157173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157173 prefixEnd_157173 := by exact prefixLift 157173
  have htrace : WordTrace (prefixWord ++ tailWord_157173) baseStart_157173 baseEnd_157173 := by
    simpa [prefixWord, tailWord_157173, baseEnd_157173] using wordTrace_append hprefix tailTrace_157173
  have hstable : (prefixWord ++ tailWord_157173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157173).length < 2 ^ (prefixWord ++ tailWord_157173).sum := by decide
  have hdescent : baseEnd_157173 < baseStart_157173 := by decide
  rcases family_descends (prefixWord ++ tailWord_157173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157212 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_157212 : Nat := 118140960795 + 157212 * 2 ^ 59
def prefixEnd_157212 : Nat := 4983230072969 + 3 ^ 40 * 157212 * 2
def baseEnd_157212 : Nat := 80725320654744141027001

theorem tailTrace_157212 : CollatzResearch.WordTrace tailWord_157212 prefixEnd_157212 80725320654744141027001 := by
  unfold tailWord_157212
  simp only [CollatzResearch.WordTrace]
  refine ⟨2866996353227624258548945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3822661804303499011398593 2866996353227624258548945)
  ·
    refine ⟨2150247264920718193911709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2866996353227624258548945 2150247264920718193911709)
    ·
      refine ⟨806342724345269322716891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2150247264920718193911709 806342724345269322716891)
      ·
        refine ⟨1209514086517903984075337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806342724345269322716891 1209514086517903984075337)
        ·
          refine ⟨907135564888427988056503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1209514086517903984075337 907135564888427988056503)
          ·
            refine ⟨1360703347332641982084755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907135564888427988056503 1360703347332641982084755)
            ·
              refine ⟨2041055020998962973127133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360703347332641982084755 2041055020998962973127133)
              ·
                refine ⟨765395632874611114922675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2041055020998962973127133 765395632874611114922675)
                ·
                  refine ⟨1148093449311916672384013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765395632874611114922675 1148093449311916672384013)
                  ·
                    refine ⟨430535043491968752144005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1148093449311916672384013 430535043491968752144005)
                    ·
                      refine ⟨80725320654744141027001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 430535043491968752144005 80725320654744141027001)
                      ·
                        rfl

theorem cell23_157212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_157212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157212 prefixEnd_157212 := by exact prefixLift 157212
  have htrace : WordTrace (prefixWord ++ tailWord_157212) baseStart_157212 baseEnd_157212 := by
    simpa [prefixWord, tailWord_157212, baseEnd_157212] using wordTrace_append hprefix tailTrace_157212
  have hstable : (prefixWord ++ tailWord_157212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157212).length < 2 ^ (prefixWord ++ tailWord_157212).sum := by decide
  have hdescent : baseEnd_157212 < baseStart_157212 := by decide
  rcases family_descends (prefixWord ++ tailWord_157212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157239 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 3, 4]
def baseStart_157239 : Nat := 118140960795 + 157239 * 2 ^ 59
def prefixEnd_157239 : Nat := 4983230072969 + 3 ^ 40 * 157239 * 2
def baseEnd_157239 : Nat := 26913061544138511796459

theorem tailTrace_157239 : CollatzResearch.WordTrace tailWord_157239 prefixEnd_157239 26913061544138511796459 := by
  unfold tailWord_157239
  simp only [CollatzResearch.WordTrace]
  refine ⟨5734977477357432128330771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3823318318238288085553847 5734977477357432128330771)
  ·
    refine ⟨8602466216036148192496157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5734977477357432128330771 8602466216036148192496157)
    ·
      refine ⟨3225924831013555572186059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8602466216036148192496157 3225924831013555572186059)
      ·
        refine ⟨4838887246520333358279089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3225924831013555572186059 4838887246520333358279089)
        ·
          refine ⟨3629165434890250018709317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4838887246520333358279089 3629165434890250018709317)
          ·
            refine ⟨680468519041921878507997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3629165434890250018709317 680468519041921878507997)
            ·
              refine ⟨255175694640720704440499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 680468519041921878507997 255175694640720704440499)
              ·
                refine ⟨382763541961081056660749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255175694640720704440499 382763541961081056660749)
                ·
                  refine ⟨143536328235405396247781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382763541961081056660749 143536328235405396247781)
                  ·
                    refine ⟨26913061544138511796459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143536328235405396247781 26913061544138511796459)
                    ·
                      rfl

theorem cell23_157239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_157239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157239 prefixEnd_157239 := by exact prefixLift 157239
  have htrace : WordTrace (prefixWord ++ tailWord_157239) baseStart_157239 baseEnd_157239 := by
    simpa [prefixWord, tailWord_157239, baseEnd_157239] using wordTrace_append hprefix tailTrace_157239
  have hstable : (prefixWord ++ tailWord_157239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157239).length < 2 ^ (prefixWord ++ tailWord_157239).sum := by decide
  have hdescent : baseEnd_157239 < baseStart_157239 := by decide
  rcases family_descends (prefixWord ++ tailWord_157239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157249 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_157249 : Nat := 118140960795 + 157249 * 2 ^ 59
def prefixEnd_157249 : Nat := 4983230072969 + 3 ^ 40 * 157249 * 2
def baseEnd_157249 : Nat := 80744319438960496264331

theorem tailTrace_157249 : CollatzResearch.WordTrace tailWord_157249 prefixEnd_157249 80744319438960496264331 := by
  unfold tailWord_157249
  simp only [CollatzResearch.WordTrace]
  refine ⟨5735342207321203836194801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3823561471547469224129867 5735342207321203836194801)
  ·
    refine ⟨4301506655490902877146101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5735342207321203836194801 4301506655490902877146101)
    ·
      refine ⟨403266248952272144732447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4301506655490902877146101 403266248952272144732447)
      ·
        refine ⟨604899373428408217098671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403266248952272144732447 604899373428408217098671)
        ·
          refine ⟨907349060142612325648007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604899373428408217098671 907349060142612325648007)
          ·
            refine ⟨1361023590213918488472011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907349060142612325648007 1361023590213918488472011)
            ·
              refine ⟨2041535385320877732708017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361023590213918488472011 2041535385320877732708017)
              ·
                refine ⟨1531151538990658299531013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041535385320877732708017 1531151538990658299531013)
                ·
                  refine ⟨287090913560748431162065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531151538990658299531013 287090913560748431162065)
                  ·
                    refine ⟨215318185170561323371549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 287090913560748431162065 215318185170561323371549)
                    ·
                      refine ⟨80744319438960496264331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 215318185170561323371549 80744319438960496264331)
                      ·
                        rfl

theorem cell23_157249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_157249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157249 prefixEnd_157249 := by exact prefixLift 157249
  have htrace : WordTrace (prefixWord ++ tailWord_157249) baseStart_157249 baseEnd_157249 := by
    simpa [prefixWord, tailWord_157249, baseEnd_157249] using wordTrace_append hprefix tailTrace_157249
  have hstable : (prefixWord ++ tailWord_157249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157249).length < 2 ^ (prefixWord ++ tailWord_157249).sum := by decide
  have hdescent : baseEnd_157249 < baseStart_157249 := by decide
  rcases family_descends (prefixWord ++ tailWord_157249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157266 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_157266 : Nat := 118140960795 + 157266 * 2 ^ 59
def prefixEnd_157266 : Nat := 4983230072969 + 3 ^ 40 * 157266 * 2
def baseEnd_157266 : Nat := 80753048610086929751753

theorem tailTrace_157266 : CollatzResearch.WordTrace tailWord_157266 prefixEnd_157266 80753048610086929751753 := by
  unfold tailWord_157266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433990562064903934890913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3823974832173077159709101 1433990562064903934890913)
  ·
    refine ⟨1075492921548677951168185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1433990562064903934890913 1075492921548677951168185)
    ·
      refine ⟨806619691161508463376139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1075492921548677951168185 806619691161508463376139)
      ·
        refine ⟨1209929536742262695064209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806619691161508463376139 1209929536742262695064209)
        ·
          refine ⟨907447152556697021298157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1209929536742262695064209 907447152556697021298157)
          ·
            refine ⟨340292682208761382986809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 907447152556697021298157 340292682208761382986809)
            ·
              refine ⟨255219511656571037240107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340292682208761382986809 255219511656571037240107)
              ·
                refine ⟨382829267484856555860161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255219511656571037240107 382829267484856555860161)
                ·
                  refine ⟨287121950613642416895121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382829267484856555860161 287121950613642416895121)
                  ·
                    refine ⟨215341462960231812671341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 287121950613642416895121 215341462960231812671341)
                    ·
                      refine ⟨80753048610086929751753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 215341462960231812671341 80753048610086929751753)
                      ·
                        rfl

theorem cell23_157266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_157266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157266 prefixEnd_157266 := by exact prefixLift 157266
  have htrace : WordTrace (prefixWord ++ tailWord_157266) baseStart_157266 baseEnd_157266 := by
    simpa [prefixWord, tailWord_157266, baseEnd_157266] using wordTrace_append hprefix tailTrace_157266
  have hstable : (prefixWord ++ tailWord_157266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157266).length < 2 ^ (prefixWord ++ tailWord_157266).sum := by decide
  have hdescent : baseEnd_157266 < baseStart_157266 := by decide
  rcases family_descends (prefixWord ++ tailWord_157266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157290 : List Nat := [3, 1, 3, 2, 1, 4, 2, 2, 1, 4]
def baseStart_157290 : Nat := 118140960795 + 157290 * 2 ^ 59
def prefixEnd_157290 : Nat := 4983230072969 + 3 ^ 40 * 157290 * 2
def baseEnd_157290 : Nat := 26921790715264945283881

theorem tailTrace_157290 : CollatzResearch.WordTrace tailWord_157290 prefixEnd_157290 26921790715264945283881 := by
  unfold tailWord_157290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434209400043166959609331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3824558400115111892291549 1434209400043166959609331)
  ·
    refine ⟨2151314100064750439413997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1434209400043166959609331 2151314100064750439413997)
    ·
      refine ⟨806742787524281414780249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2151314100064750439413997 806742787524281414780249)
      ·
        refine ⟨605057090643211061085187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 806742787524281414780249 605057090643211061085187)
        ·
          refine ⟨907585635964816591627781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605057090643211061085187 907585635964816591627781)
          ·
            refine ⟨170172306743403110930209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 907585635964816591627781 170172306743403110930209)
            ·
              refine ⟨127629230057552333197657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170172306743403110930209 127629230057552333197657)
              ·
                refine ⟨95721922543164249898243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127629230057552333197657 95721922543164249898243)
                ·
                  refine ⟨143582883814746374847365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95721922543164249898243 143582883814746374847365)
                  ·
                    refine ⟨26921790715264945283881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143582883814746374847365 26921790715264945283881)
                    ·
                      rfl

theorem cell23_157290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_157290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157290 prefixEnd_157290 := by exact prefixLift 157290
  have htrace : WordTrace (prefixWord ++ tailWord_157290) baseStart_157290 baseEnd_157290 := by
    simpa [prefixWord, tailWord_157290, baseEnd_157290] using wordTrace_append hprefix tailTrace_157290
  have hstable : (prefixWord ++ tailWord_157290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157290).length < 2 ^ (prefixWord ++ tailWord_157290).sum := by decide
  have hdescent : baseEnd_157290 < baseStart_157290 := by decide
  rcases family_descends (prefixWord ++ tailWord_157290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157319 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_157319 : Nat := 118140960795 + 157319 * 2 ^ 59
def prefixEnd_157319 : Nat := 4983230072969 + 3 ^ 40 * 157319 * 2
def baseEnd_157319 : Nat := 80780263084775222389009

theorem tailTrace_157319 : CollatzResearch.WordTrace tailWord_157319 prefixEnd_157319 80780263084775222389009 := by
  unfold tailWord_157319
  simp only [CollatzResearch.WordTrace]
  refine ⟨5737895317067605791243011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3825263544711737194162007 5737895317067605791243011)
  ·
    refine ⟨8606842975601408686864517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5737895317067605791243011 8606842975601408686864517)
    ·
      refine ⟨1613783057925264128787097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8606842975601408686864517 1613783057925264128787097)
      ·
        refine ⟨1210337293443948096590323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1613783057925264128787097 1210337293443948096590323)
        ·
          refine ⟨1815505940165922144885485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210337293443948096590323 1815505940165922144885485)
          ·
            refine ⟨680814727562220804332057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1815505940165922144885485 680814727562220804332057)
            ·
              refine ⟨510611045671665603249043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680814727562220804332057 510611045671665603249043)
              ·
                refine ⟨765916568507498404873565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510611045671665603249043 765916568507498404873565)
                ·
                  refine ⟨287218713190311901827587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765916568507498404873565 287218713190311901827587)
                  ·
                    refine ⟨430828069785467852741381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287218713190311901827587 430828069785467852741381)
                    ·
                      refine ⟨80780263084775222389009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 430828069785467852741381 80780263084775222389009)
                      ·
                        rfl

theorem cell23_157319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_157319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157319 prefixEnd_157319 := by exact prefixLift 157319
  have htrace : WordTrace (prefixWord ++ tailWord_157319) baseStart_157319 baseEnd_157319 := by
    simpa [prefixWord, tailWord_157319, baseEnd_157319] using wordTrace_append hprefix tailTrace_157319
  have hstable : (prefixWord ++ tailWord_157319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157319).length < 2 ^ (prefixWord ++ tailWord_157319).sum := by decide
  have hdescent : baseEnd_157319 < baseStart_157319 := by decide
  rcases family_descends (prefixWord ++ tailWord_157319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157336 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 1, 1, 4]
def baseStart_157336 : Nat := 118140960795 + 157336 * 2 ^ 59
def prefixEnd_157336 : Nat := 4983230072969 + 3 ^ 40 * 157336 * 2
def baseEnd_157336 : Nat := 80788992255901655876431

theorem tailTrace_157336 : CollatzResearch.WordTrace tailWord_157336 prefixEnd_157336 80788992255901655876431 := by
  unfold tailWord_157336
  simp only [CollatzResearch.WordTrace]
  refine ⟨2869257679003008847305931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3825676905337345129741241 2869257679003008847305931)
  ·
    refine ⟨4303886518504513270958897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2869257679003008847305931 4303886518504513270958897)
    ·
      refine ⟨3227914888878384953219173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4303886518504513270958897 3227914888878384953219173)
      ·
        refine ⟨605234041664697178728595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3227914888878384953219173 605234041664697178728595)
        ·
          refine ⟨907851062497045768092893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605234041664697178728595 907851062497045768092893)
          ·
            refine ⟨340444148436392163034835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 907851062497045768092893 340444148436392163034835)
            ·
              refine ⟨510666222654588244552253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340444148436392163034835 510666222654588244552253)
              ·
                refine ⟨191499833495470591707095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 510666222654588244552253 191499833495470591707095)
                ·
                  refine ⟨287249750243205887560643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191499833495470591707095 287249750243205887560643)
                  ·
                    refine ⟨430874625364808831340965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287249750243205887560643 430874625364808831340965)
                    ·
                      refine ⟨80788992255901655876431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 430874625364808831340965 80788992255901655876431)
                      ·
                        rfl

theorem cell23_157336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_157336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157336 prefixEnd_157336 := by exact prefixLift 157336
  have htrace : WordTrace (prefixWord ++ tailWord_157336) baseStart_157336 baseEnd_157336 := by
    simpa [prefixWord, tailWord_157336, baseEnd_157336] using wordTrace_append hprefix tailTrace_157336
  have hstable : (prefixWord ++ tailWord_157336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157336).length < 2 ^ (prefixWord ++ tailWord_157336).sum := by decide
  have hdescent : baseEnd_157336 < baseStart_157336 := by decide
  rcases family_descends (prefixWord ++ tailWord_157336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157379 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 4, 7, 2]
def baseStart_157379 : Nat := 118140960795 + 157379 * 2 ^ 59
def prefixEnd_157379 : Nat := 4983230072969 + 3 ^ 40 * 157379 * 2
def baseEnd_157379 : Nat := 80811071924044987638733

theorem tailTrace_157379 : CollatzResearch.WordTrace tailWord_157379 prefixEnd_157379 80811071924044987638733 := by
  unfold tailWord_157379
  simp only [CollatzResearch.WordTrace]
  refine ⟨5740083696850236038427191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3826722464566824025618127 5740083696850236038427191)
  ·
    refine ⟨8610125545275354057640787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5740083696850236038427191 8610125545275354057640787)
    ·
      refine ⟨12915188317913031086461181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8610125545275354057640787 12915188317913031086461181)
      ·
        refine ⟨4843195619217386657422943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12915188317913031086461181 4843195619217386657422943)
        ·
          refine ⟨7264793428826079986134415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4843195619217386657422943 7264793428826079986134415)
          ·
            refine ⟨10897190143239119979201623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7264793428826079986134415 10897190143239119979201623)
            ·
              refine ⟨16345785214858679968802435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10897190143239119979201623 16345785214858679968802435)
              ·
                refine ⟨24518677822288019953203653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16345785214858679968802435 24518677822288019953203653)
                ·
                  refine ⟨4597252091679003741225685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24518677822288019953203653 4597252091679003741225685)
                  ·
                    refine ⟨107748095898726650184977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4597252091679003741225685 107748095898726650184977)
                    ·
                      refine ⟨80811071924044987638733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107748095898726650184977 80811071924044987638733)
                      ·
                        rfl

theorem cell23_157379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 7, 2].length) (baseStart_157379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157379 prefixEnd_157379 := by exact prefixLift 157379
  have htrace : WordTrace (prefixWord ++ tailWord_157379) baseStart_157379 baseEnd_157379 := by
    simpa [prefixWord, tailWord_157379, baseEnd_157379] using wordTrace_append hprefix tailTrace_157379
  have hstable : (prefixWord ++ tailWord_157379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157379).length < 2 ^ (prefixWord ++ tailWord_157379).sum := by decide
  have hdescent : baseEnd_157379 < baseStart_157379 := by decide
  rcases family_descends (prefixWord ++ tailWord_157379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157404 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_157404 : Nat := 118140960795 + 157404 * 2 ^ 59
def prefixEnd_157404 : Nat := 4983230072969 + 3 ^ 40 * 157404 * 2
def baseEnd_157404 : Nat := 80823908940407389826119

theorem tailTrace_157404 : CollatzResearch.WordTrace tailWord_157404 prefixEnd_157404 80823908940407389826119 := by
  unfold tailWord_157404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2870497760879832654043633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3827330347839776872058177 2870497760879832654043633)
  ·
    refine ⟨2152873320659874490532725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2870497760879832654043633 2152873320659874490532725)
    ·
      refine ⟨201831873811863233487443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2152873320659874490532725 201831873811863233487443)
      ·
        refine ⟨302747810717794850231165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201831873811863233487443 302747810717794850231165)
        ·
          refine ⟨113530429019173068836687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302747810717794850231165 113530429019173068836687)
          ·
            refine ⟨170295643528759603255031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113530429019173068836687 170295643528759603255031)
            ·
              refine ⟨255443465293139404882547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170295643528759603255031 255443465293139404882547)
              ·
                refine ⟨383165197939709107323821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255443465293139404882547 383165197939709107323821)
                ·
                  refine ⟨143686949227390915246433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 383165197939709107323821 143686949227390915246433)
                  ·
                    refine ⟨107765211920543186434825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 143686949227390915246433 107765211920543186434825)
                    ·
                      refine ⟨80823908940407389826119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107765211920543186434825 80823908940407389826119)
                      ·
                        rfl

theorem cell23_157404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_157404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157404 prefixEnd_157404 := by exact prefixLift 157404
  have htrace : WordTrace (prefixWord ++ tailWord_157404) baseStart_157404 baseEnd_157404 := by
    simpa [prefixWord, tailWord_157404, baseEnd_157404] using wordTrace_append hprefix tailTrace_157404
  have hstable : (prefixWord ++ tailWord_157404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157404).length < 2 ^ (prefixWord ++ tailWord_157404).sum := by decide
  have hdescent : baseEnd_157404 < baseStart_157404 := by decide
  rcases family_descends (prefixWord ++ tailWord_157404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157430 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_157430 : Nat := 118140960795 + 157430 * 2 ^ 59
def prefixEnd_157430 : Nat := 4983230072969 + 3 ^ 40 * 157430 * 2
def baseEnd_157430 : Nat := 80837259437424288100999

theorem tailTrace_157430 : CollatzResearch.WordTrace tailWord_157430 prefixEnd_157430 80837259437424288100999 := by
  unfold tailWord_157430
  simp only [CollatzResearch.WordTrace]
  refine ⟨358871488729091984283359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3827962546443647832355829 358871488729091984283359)
  ·
    refine ⟨538307233093637976425039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 358871488729091984283359 538307233093637976425039)
    ·
      refine ⟨807460849640456964637559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 538307233093637976425039 807460849640456964637559)
      ·
        refine ⟨1211191274460685446956339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807460849640456964637559 1211191274460685446956339)
        ·
          refine ⟨1816786911691028170434509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211191274460685446956339 1816786911691028170434509)
          ·
            refine ⟨681295091884135563912941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1816786911691028170434509 681295091884135563912941)
            ·
              refine ⟨255485659456550836467353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 681295091884135563912941 255485659456550836467353)
              ·
                refine ⟨191614244592413127350515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255485659456550836467353 191614244592413127350515)
                ·
                  refine ⟨287421366888619691025773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191614244592413127350515 287421366888619691025773)
                  ·
                    refine ⟨107783012583232384134665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 287421366888619691025773 107783012583232384134665)
                    ·
                      refine ⟨80837259437424288100999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107783012583232384134665 80837259437424288100999)
                      ·
                        rfl

theorem cell23_157430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_157430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157430 prefixEnd_157430 := by exact prefixLift 157430
  have htrace : WordTrace (prefixWord ++ tailWord_157430) baseStart_157430 baseEnd_157430 := by
    simpa [prefixWord, tailWord_157430, baseEnd_157430] using wordTrace_append hprefix tailTrace_157430
  have hstable : (prefixWord ++ tailWord_157430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157430).length < 2 ^ (prefixWord ++ tailWord_157430).sum := by decide
  have hdescent : baseEnd_157430 < baseStart_157430 := by decide
  rcases family_descends (prefixWord ++ tailWord_157430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157447 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 1, 3, 2]
def baseStart_157447 : Nat := 118140960795 + 157447 * 2 ^ 59
def prefixEnd_157447 : Nat := 4983230072969 + 3 ^ 40 * 157447 * 2
def baseEnd_157447 : Nat := 80845988608550721588421

theorem tailTrace_157447 : CollatzResearch.WordTrace tailWord_157447 prefixEnd_157447 80845988608550721588421 := by
  unfold tailWord_157447
  simp only [CollatzResearch.WordTrace]
  refine ⟨5742563860603883651902595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3828375907069255767935063 5742563860603883651902595)
  ·
    refine ⟨8613845790905825477853893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5742563860603883651902595 8613845790905825477853893)
    ·
      refine ⟨1615096085794842277097605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8613845790905825477853893 1615096085794842277097605)
      ·
        refine ⟨302830516086532926955801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1615096085794842277097605 302830516086532926955801)
        ·
          refine ⟨227122887064899695216851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302830516086532926955801 227122887064899695216851)
          ·
            refine ⟨340684330597349542825277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227122887064899695216851 340684330597349542825277)
            ·
              refine ⟨127756623974006078559479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 340684330597349542825277 127756623974006078559479)
              ·
                refine ⟨191634935961009117839219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127756623974006078559479 191634935961009117839219)
                ·
                  refine ⟨287452403941513676758829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191634935961009117839219 287452403941513676758829)
                  ·
                    refine ⟨107794651478067628784561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 287452403941513676758829 107794651478067628784561)
                    ·
                      refine ⟨80845988608550721588421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107794651478067628784561 80845988608550721588421)
                      ·
                        rfl

theorem cell23_157447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_157447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157447 prefixEnd_157447 := by exact prefixLift 157447
  have htrace : WordTrace (prefixWord ++ tailWord_157447) baseStart_157447 baseEnd_157447 := by
    simpa [prefixWord, tailWord_157447, baseEnd_157447] using wordTrace_append hprefix tailTrace_157447
  have hstable : (prefixWord ++ tailWord_157447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157447).length < 2 ^ (prefixWord ++ tailWord_157447).sum := by decide
  have hdescent : baseEnd_157447 < baseStart_157447 := by decide
  rcases family_descends (prefixWord ++ tailWord_157447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157470 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_157470 : Nat := 118140960795 + 157470 * 2 ^ 59
def prefixEnd_157470 : Nat := 4983230072969 + 3 ^ 40 * 157470 * 2
def baseEnd_157470 : Nat := 26952599554534710533605

theorem tailTrace_157470 : CollatzResearch.WordTrace tailWord_157470 prefixEnd_157470 26952599554534710533605 := by
  unfold tailWord_157470
  simp only [CollatzResearch.WordTrace]
  refine ⟨717925342440069822498733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3828935159680372386659909 717925342440069822498733)
  ·
    refine ⟨269222003415026183437025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 717925342440069822498733 269222003415026183437025)
    ·
      refine ⟨201916502561269637577769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269222003415026183437025 201916502561269637577769)
      ·
        refine ⟨151437376920952228183327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201916502561269637577769 151437376920952228183327)
        ·
          refine ⟨227156065381428342274991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151437376920952228183327 227156065381428342274991)
          ·
            refine ⟨340734098072142513412487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227156065381428342274991 340734098072142513412487)
            ·
              refine ⟨511101147108213770118731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340734098072142513412487 511101147108213770118731)
              ·
                refine ⟨766651720662320655178097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511101147108213770118731 766651720662320655178097)
                ·
                  refine ⟨574988790496740491383573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 766651720662320655178097 574988790496740491383573)
                  ·
                    refine ⟨26952599554534710533605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 574988790496740491383573 26952599554534710533605)
                    ·
                      rfl

theorem cell23_157470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_157470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157470 prefixEnd_157470 := by exact prefixLift 157470
  have htrace : WordTrace (prefixWord ++ tailWord_157470) baseStart_157470 baseEnd_157470 := by
    simpa [prefixWord, tailWord_157470, baseEnd_157470] using wordTrace_append hprefix tailTrace_157470
  have hstable : (prefixWord ++ tailWord_157470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157470).length < 2 ^ (prefixWord ++ tailWord_157470).sum := by decide
  have hdescent : baseEnd_157470 < baseStart_157470 := by decide
  rcases family_descends (prefixWord ++ tailWord_157470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157476 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_157476 : Nat := 118140960795 + 157476 * 2 ^ 59
def prefixEnd_157476 : Nat := 4983230072969 + 3 ^ 40 * 157476 * 2
def baseEnd_157476 : Nat := 80860879547531108125787

theorem tailTrace_157476 : CollatzResearch.WordTrace tailWord_157476 prefixEnd_157476 80860879547531108125787 := by
  unfold tailWord_157476
  simp only [CollatzResearch.WordTrace]
  refine ⟨2871810788749410802354141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3829081051665881069805521 2871810788749410802354141)
  ·
    refine ⟨1076929045781029050882803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2871810788749410802354141 1076929045781029050882803)
    ·
      refine ⟨1615393568671543576324205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1076929045781029050882803 1615393568671543576324205)
      ·
        refine ⟨605772588251828841121577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1615393568671543576324205 605772588251828841121577)
        ·
          refine ⟨454329441188871630841183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605772588251828841121577 454329441188871630841183)
          ·
            refine ⟨681494161783307446261775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454329441188871630841183 681494161783307446261775)
            ·
              refine ⟨1022241242674961169392663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681494161783307446261775 1022241242674961169392663)
              ·
                refine ⟨1533361864012441754088995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022241242674961169392663 1533361864012441754088995)
                ·
                  refine ⟨2300042796018662631133493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533361864012441754088995 2300042796018662631133493)
                  ·
                    refine ⟨215629012126749621668765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2300042796018662631133493 215629012126749621668765)
                    ·
                      refine ⟨80860879547531108125787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 215629012126749621668765 80860879547531108125787)
                      ·
                        rfl

theorem cell23_157476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_157476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157476 prefixEnd_157476 := by exact prefixLift 157476
  have htrace : WordTrace (prefixWord ++ tailWord_157476) baseStart_157476 baseEnd_157476 := by
    simpa [prefixWord, tailWord_157476, baseEnd_157476] using wordTrace_append hprefix tailTrace_157476
  have hstable : (prefixWord ++ tailWord_157476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157476).length < 2 ^ (prefixWord ++ tailWord_157476).sum := by decide
  have hdescent : baseEnd_157476 < baseStart_157476 := by decide
  rcases family_descends (prefixWord ++ tailWord_157476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157496 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 2, 5]
def baseStart_157496 : Nat := 118140960795 + 157496 * 2 ^ 59
def prefixEnd_157496 : Nat := 4983230072969 + 3 ^ 40 * 157496 * 2
def baseEnd_157496 : Nat := 26957049720207009958565

theorem tailTrace_157496 : CollatzResearch.WordTrace tailWord_157496 prefixEnd_157496 26957049720207009958565 := by
  unfold tailWord_157496
  simp only [CollatzResearch.WordTrace]
  refine ⟨2872175518713182510218171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3829567358284243346957561 2872175518713182510218171)
  ·
    refine ⟨4308263278069773765327257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2872175518713182510218171 4308263278069773765327257)
    ·
      refine ⟨3231197458552330323995443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4308263278069773765327257 3231197458552330323995443)
      ·
        refine ⟨4846796187828495485993165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231197458552330323995443 4846796187828495485993165)
        ·
          refine ⟨1817548570435685807247437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4846796187828495485993165 1817548570435685807247437)
          ·
            refine ⟨681580713913382177717789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1817548570435685807247437 681580713913382177717789)
            ·
              refine ⟨255592767717518316644171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 681580713913382177717789 255592767717518316644171)
              ·
                refine ⟨383389151576277474966257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255592767717518316644171 383389151576277474966257)
                ·
                  refine ⟨287541863682208106224693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383389151576277474966257 287541863682208106224693)
                  ·
                    refine ⟨26957049720207009958565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 287541863682208106224693 26957049720207009958565)
                    ·
                      rfl

theorem cell23_157496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_157496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157496 prefixEnd_157496 := by exact prefixLift 157496
  have htrace : WordTrace (prefixWord ++ tailWord_157496) baseStart_157496 baseEnd_157496 := by
    simpa [prefixWord, tailWord_157496, baseEnd_157496] using wordTrace_append hprefix tailTrace_157496
  have hstable : (prefixWord ++ tailWord_157496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157496).length < 2 ^ (prefixWord ++ tailWord_157496).sum := by decide
  have hdescent : baseEnd_157496 < baseStart_157496 := by decide
  rcases family_descends (prefixWord ++ tailWord_157496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157510 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_157510 : Nat := 118140960795 + 157510 * 2 ^ 59
def prefixEnd_157510 : Nat := 4983230072969 + 3 ^ 40 * 157510 * 2
def baseEnd_157510 : Nat := 80878337889783975100631

theorem tailTrace_157510 : CollatzResearch.WordTrace tailWord_157510 prefixEnd_157510 80878337889783975100631 := by
  unfold tailWord_157510
  simp only [CollatzResearch.WordTrace]
  refine ⟨179526926855488919107687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3829907772917096940963989 179526926855488919107687)
  ·
    refine ⟨269290390283233378661531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179526926855488919107687 269290390283233378661531)
    ·
      refine ⟨403935585424850067992297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269290390283233378661531 403935585424850067992297)
      ·
        refine ⟨302951689068637550994223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403935585424850067992297 302951689068637550994223)
        ·
          refine ⟨454427533602956326491335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302951689068637550994223 454427533602956326491335)
          ·
            refine ⟨681641300404434489737003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454427533602956326491335 681641300404434489737003)
            ·
              refine ⟨1022461950606651734605505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681641300404434489737003 1022461950606651734605505)
              ·
                refine ⟨766846462954988800954129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022461950606651734605505 766846462954988800954129)
                ·
                  refine ⟨575134847216241600715597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 766846462954988800954129 575134847216241600715597)
                  ·
                    refine ⟨215675567706090600268349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 575134847216241600715597 215675567706090600268349)
                    ·
                      refine ⟨80878337889783975100631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 215675567706090600268349 80878337889783975100631)
                      ·
                        rfl

theorem cell23_157510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_157510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157510 prefixEnd_157510 := by exact prefixLift 157510
  have htrace : WordTrace (prefixWord ++ tailWord_157510) baseStart_157510 baseEnd_157510 := by
    simpa [prefixWord, tailWord_157510, baseEnd_157510] using wordTrace_append hprefix tailTrace_157510
  have hstable : (prefixWord ++ tailWord_157510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157510).length < 2 ^ (prefixWord ++ tailWord_157510).sum := by decide
  have hdescent : baseEnd_157510 < baseStart_157510 := by decide
  rcases family_descends (prefixWord ++ tailWord_157510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157529 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_157529 : Nat := 118140960795 + 157529 * 2 ^ 59
def prefixEnd_157529 : Nat := 4983230072969 + 3 ^ 40 * 157529 * 2
def baseEnd_157529 : Nat := 80888094022219400763043

theorem tailTrace_157529 : CollatzResearch.WordTrace tailWord_157529 prefixEnd_157529 80888094022219400763043 := by
  unfold tailWord_157529
  simp only [CollatzResearch.WordTrace]
  refine ⟨5745554646306811656387641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3830369764204541104258427 5745554646306811656387641)
  ·
    refine ⟨4309165984730108742290731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5745554646306811656387641 4309165984730108742290731)
    ·
      refine ⟨6463748977095163113436097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4309165984730108742290731 6463748977095163113436097)
      ·
        refine ⟨4847811732821372335077073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6463748977095163113436097 4847811732821372335077073)
        ·
          refine ⟨3635858799616029251307805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4847811732821372335077073 3635858799616029251307805)
          ·
            refine ⟨1363447049856010969240427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3635858799616029251307805 1363447049856010969240427)
            ·
              refine ⟨2045170574784016453860641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363447049856010969240427 2045170574784016453860641)
              ·
                refine ⟨1533877931088012340395481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2045170574784016453860641 1533877931088012340395481)
                ·
                  refine ⟨1150408448316009255296611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1533877931088012340395481 1150408448316009255296611)
                  ·
                    refine ⟨1725612672474013882944917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1150408448316009255296611 1725612672474013882944917)
                    ·
                      refine ⟨80888094022219400763043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1725612672474013882944917 80888094022219400763043)
                      ·
                        rfl

theorem cell23_157529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_157529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157529 prefixEnd_157529 := by exact prefixLift 157529
  have htrace : WordTrace (prefixWord ++ tailWord_157529) baseStart_157529 baseEnd_157529 := by
    simpa [prefixWord, tailWord_157529, baseEnd_157529] using wordTrace_append hprefix tailTrace_157529
  have hstable : (prefixWord ++ tailWord_157529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157529).length < 2 ^ (prefixWord ++ tailWord_157529).sum := by decide
  have hdescent : baseEnd_157529 < baseStart_157529 := by decide
  rcases family_descends (prefixWord ++ tailWord_157529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157536 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 3]
def baseStart_157536 : Nat := 118140960795 + 157536 * 2 ^ 59
def prefixEnd_157536 : Nat := 4983230072969 + 3 ^ 40 * 157536 * 2
def baseEnd_157536 : Nat := 80891688386800873375511

theorem tailTrace_157536 : CollatzResearch.WordTrace tailWord_157536 prefixEnd_157536 80891688386800873375511 := by
  unfold tailWord_157536
  simp only [CollatzResearch.WordTrace]
  refine ⟨2872904978640725925946231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3830539971520967901261641 2872904978640725925946231)
  ·
    refine ⟨4309357467961088888919347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2872904978640725925946231 4309357467961088888919347)
    ·
      refine ⟨6464036201941633333379021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4309357467961088888919347 6464036201941633333379021)
      ·
        refine ⟨2424013575728112500017133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6464036201941633333379021 2424013575728112500017133)
        ·
          refine ⟨909005090898042187506425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2424013575728112500017133 909005090898042187506425)
          ·
            refine ⟨681753818173531640629819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909005090898042187506425 681753818173531640629819)
            ·
              refine ⟨1022630727260297460944729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681753818173531640629819 1022630727260297460944729)
              ·
                refine ⟨766973045445223095708547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022630727260297460944729 766973045445223095708547)
                ·
                  refine ⟨1150459568167834643562821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766973045445223095708547 1150459568167834643562821)
                  ·
                    refine ⟨215711169031468995668029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1150459568167834643562821 215711169031468995668029)
                    ·
                      refine ⟨80891688386800873375511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 215711169031468995668029 80891688386800873375511)
                      ·
                        rfl

theorem cell23_157536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_157536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157536 prefixEnd_157536 := by exact prefixLift 157536
  have htrace : WordTrace (prefixWord ++ tailWord_157536) baseStart_157536 baseEnd_157536 := by
    simpa [prefixWord, tailWord_157536, baseEnd_157536] using wordTrace_append hprefix tailTrace_157536
  have hstable : (prefixWord ++ tailWord_157536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157536).length < 2 ^ (prefixWord ++ tailWord_157536).sum := by decide
  have hdescent : baseEnd_157536 < baseStart_157536 := by decide
  rcases family_descends (prefixWord ++ tailWord_157536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157579 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 7]
def baseStart_157579 : Nat := 118140960795 + 157579 * 2 ^ 59
def prefixEnd_157579 : Nat := 4983230072969 + 3 ^ 40 * 157579 * 2
def baseEnd_157579 : Nat := 80913768054944205137813

theorem tailTrace_157579 : CollatzResearch.WordTrace tailWord_157579 prefixEnd_157579 80913768054944205137813 := by
  unfold tailWord_157579
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747378296125670195707791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3831585530750446797138527 5747378296125670195707791)
  ·
    refine ⟨8621067444188505293561687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5747378296125670195707791 8621067444188505293561687)
    ·
      refine ⟨12931601166282757940342531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8621067444188505293561687 12931601166282757940342531)
      ·
        refine ⟨19397401749424136910513797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12931601166282757940342531 19397401749424136910513797)
        ·
          refine ⟨3637012828017025670721337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19397401749424136910513797 3637012828017025670721337)
          ·
            refine ⟨2727759621012769253041003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3637012828017025670721337 2727759621012769253041003)
            ·
              refine ⟨4091639431519153879561505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727759621012769253041003 4091639431519153879561505)
              ·
                refine ⟨3068729573639365409671129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4091639431519153879561505 3068729573639365409671129)
                ·
                  refine ⟨2301547180229524057253347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3068729573639365409671129 2301547180229524057253347)
                  ·
                    refine ⟨3452320770344286085880021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2301547180229524057253347 3452320770344286085880021)
                    ·
                      refine ⟨80913768054944205137813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3452320770344286085880021 80913768054944205137813)
                      ·
                        rfl

theorem cell23_157579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_157579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157579 prefixEnd_157579 := by exact prefixLift 157579
  have htrace : WordTrace (prefixWord ++ tailWord_157579) baseStart_157579 baseEnd_157579 := by
    simpa [prefixWord, tailWord_157579, baseEnd_157579] using wordTrace_append hprefix tailTrace_157579
  have hstable : (prefixWord ++ tailWord_157579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157579).length < 2 ^ (prefixWord ++ tailWord_157579).sum := by decide
  have hdescent : baseEnd_157579 < baseStart_157579 := by decide
  rcases family_descends (prefixWord ++ tailWord_157579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157626 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_157626 : Nat := 118140960795 + 157626 * 2 ^ 59
def prefixEnd_157626 : Nat := 4983230072969 + 3 ^ 40 * 157626 * 2
def baseEnd_157626 : Nat := 80937901645705521250097

theorem tailTrace_157626 : CollatzResearch.WordTrace tailWord_157626 prefixEnd_157626 80937901645705521250097 := by
  unfold tailWord_157626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437273131738849305667183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3832728351303598148445821 1437273131738849305667183)
  ·
    refine ⟨2155909697608273958500775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1437273131738849305667183 2155909697608273958500775)
    ·
      refine ⟨3233864546412410937751163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2155909697608273958500775 3233864546412410937751163)
      ·
        refine ⟨4850796819618616406626745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233864546412410937751163 4850796819618616406626745)
        ·
          refine ⟨3638097614713962304970059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4850796819618616406626745 3638097614713962304970059)
          ·
            refine ⟨5457146422070943457455089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3638097614713962304970059 5457146422070943457455089)
            ·
              refine ⟨4092859816553207593091317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5457146422070943457455089 4092859816553207593091317)
              ·
                refine ⟨383705607801863211852311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4092859816553207593091317 383705607801863211852311)
                ·
                  refine ⟨575558411702794817778467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383705607801863211852311 575558411702794817778467)
                  ·
                    refine ⟨863337617554192226667701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 575558411702794817778467 863337617554192226667701)
                    ·
                      refine ⟨80937901645705521250097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 863337617554192226667701 80937901645705521250097)
                      ·
                        rfl

theorem cell23_157626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_157626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157626 prefixEnd_157626 := by exact prefixLift 157626
  have htrace : WordTrace (prefixWord ++ tailWord_157626) baseStart_157626 baseEnd_157626 := by
    simpa [prefixWord, tailWord_157626, baseEnd_157626] using wordTrace_append hprefix tailTrace_157626
  have hstable : (prefixWord ++ tailWord_157626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157626).length < 2 ^ (prefixWord ++ tailWord_157626).sum := by decide
  have hdescent : baseEnd_157626 < baseStart_157626 := by decide
  rcases family_descends (prefixWord ++ tailWord_157626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157650 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_157650 : Nat := 118140960795 + 157650 * 2 ^ 59
def prefixEnd_157650 : Nat := 4983230072969 + 3 ^ 40 * 157650 * 2
def baseEnd_157650 : Nat := 26983408393804475783329

theorem tailTrace_157650 : CollatzResearch.WordTrace tailWord_157650 prefixEnd_157650 26983408393804475783329 := by
  unfold tailWord_157650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437491969717112330385601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3833311919245632881028269 1437491969717112330385601)
  ·
    refine ⟨1078118977287834247789201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1437491969717112330385601 1078118977287834247789201)
    ·
      refine ⟨808589232965875685841901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1078118977287834247789201 808589232965875685841901)
      ·
        refine ⟨303220962362203382190713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 808589232965875685841901 303220962362203382190713)
        ·
          refine ⟨227415721771652536643035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303220962362203382190713 227415721771652536643035)
          ·
            refine ⟨341123582657478804964553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227415721771652536643035 341123582657478804964553)
            ·
              refine ⟨255842686993109103723415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341123582657478804964553 255842686993109103723415)
              ·
                refine ⟨383764030489663655585123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255842686993109103723415 383764030489663655585123)
                ·
                  refine ⟨575646045734495483377685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383764030489663655585123 575646045734495483377685)
                  ·
                    refine ⟨26983408393804475783329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 575646045734495483377685 26983408393804475783329)
                    ·
                      rfl

theorem cell23_157650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_157650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157650 prefixEnd_157650 := by exact prefixLift 157650
  have htrace : WordTrace (prefixWord ++ tailWord_157650) baseStart_157650 baseEnd_157650 := by
    simpa [prefixWord, tailWord_157650, baseEnd_157650] using wordTrace_append hprefix tailTrace_157650
  have hstable : (prefixWord ++ tailWord_157650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157650).length < 2 ^ (prefixWord ++ tailWord_157650).sum := by decide
  have hdescent : baseEnd_157650 < baseStart_157650 := by decide
  rcases family_descends (prefixWord ++ tailWord_157650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157653 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_157653 : Nat := 118140960795 + 157653 * 2 ^ 59
def prefixEnd_157653 : Nat := 4983230072969 + 3 ^ 40 * 157653 * 2
def baseEnd_157653 : Nat := 80951765623376915612473

theorem tailTrace_157653 : CollatzResearch.WordTrace tailWord_157653 prefixEnd_157653 80951765623376915612473 := by
  unfold tailWord_157653
  simp only [CollatzResearch.WordTrace]
  refine ⟨5750077297857580833901613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3833384865238387222601075 5750077297857580833901613)
  ·
    refine ⟨2156278986696592812713105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5750077297857580833901613 2156278986696592812713105)
    ·
      refine ⟨1617209240022444609534829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2156278986696592812713105 1617209240022444609534829)
      ·
        refine ⟨606453465008416728575561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1617209240022444609534829 606453465008416728575561)
        ·
          refine ⟨454840098756312546431671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606453465008416728575561 454840098756312546431671)
          ·
            refine ⟨682260148134468819647507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454840098756312546431671 682260148134468819647507)
            ·
              refine ⟨1023390222201703229471261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682260148134468819647507 1023390222201703229471261)
              ·
                refine ⟨383771333325638711051723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1023390222201703229471261 383771333325638711051723)
                ·
                  refine ⟨575656999988458066577585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383771333325638711051723 575656999988458066577585)
                  ·
                    refine ⟨431742749991343549933189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 575656999988458066577585 431742749991343549933189)
                    ·
                      refine ⟨80951765623376915612473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 431742749991343549933189 80951765623376915612473)
                      ·
                        rfl

theorem cell23_157653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_157653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157653 prefixEnd_157653 := by exact prefixLift 157653
  have htrace : WordTrace (prefixWord ++ tailWord_157653) baseStart_157653 baseEnd_157653 := by
    simpa [prefixWord, tailWord_157653, baseEnd_157653] using wordTrace_append hprefix tailTrace_157653
  have hstable : (prefixWord ++ tailWord_157653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157653).length < 2 ^ (prefixWord ++ tailWord_157653).sum := by decide
  have hdescent : baseEnd_157653 < baseStart_157653 := by decide
  rcases family_descends (prefixWord ++ tailWord_157653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157657 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 3, 2, 2]
def baseStart_157657 : Nat := 118140960795 + 157657 * 2 ^ 59
def prefixEnd_157657 : Nat := 4983230072969 + 3 ^ 40 * 157657 * 2
def baseEnd_157657 : Nat := 80953819545994899962455

theorem tailTrace_157657 : CollatzResearch.WordTrace tailWord_157657 prefixEnd_157657 80953819545994899962455 := by
  unfold tailWord_157657
  simp only [CollatzResearch.WordTrace]
  refine ⟨5750223189843089517047225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3833482126562059678031483 5750223189843089517047225)
  ·
    refine ⟨4312667392382317137785419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5750223189843089517047225 4312667392382317137785419)
    ·
      refine ⟨6469001088573475706678129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4312667392382317137785419 6469001088573475706678129)
      ·
        refine ⟨4851750816430106780008597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6469001088573475706678129 4851750816430106780008597)
        ·
          refine ⟨227425819520161255312903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4851750816430106780008597 227425819520161255312903)
          ·
            refine ⟨341138729280241882969355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227425819520161255312903 341138729280241882969355)
            ·
              refine ⟨511708093920362824454033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341138729280241882969355 511708093920362824454033)
              ·
                refine ⟨383781070440272118340525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511708093920362824454033 383781070440272118340525)
                ·
                  refine ⟨143917901415102044377697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 383781070440272118340525 143917901415102044377697)
                  ·
                    refine ⟨107938426061326533283273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 143917901415102044377697 107938426061326533283273)
                    ·
                      refine ⟨80953819545994899962455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107938426061326533283273 80953819545994899962455)
                      ·
                        rfl

theorem cell23_157657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 2, 2].length) (baseStart_157657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157657 prefixEnd_157657 := by exact prefixLift 157657
  have htrace : WordTrace (prefixWord ++ tailWord_157657) baseStart_157657 baseEnd_157657 := by
    simpa [prefixWord, tailWord_157657, baseEnd_157657] using wordTrace_append hprefix tailTrace_157657
  have hstable : (prefixWord ++ tailWord_157657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157657).length < 2 ^ (prefixWord ++ tailWord_157657).sum := by decide
  have hdescent : baseEnd_157657 < baseStart_157657 := by decide
  rcases family_descends (prefixWord ++ tailWord_157657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157663 : List Nat := [1, 1, 2, 3, 4, 2, 3, 7]
def baseStart_157663 : Nat := 118140960795 + 157663 * 2 ^ 59
def prefixEnd_157663 : Nat := 4983230072969 + 3 ^ 40 * 157663 * 2
def baseEnd_157663 : Nat := 2998403719626736166201

theorem tailTrace_157663 : CollatzResearch.WordTrace tailWord_157663 prefixEnd_157663 2998403719626736166201 := by
  unfold tailWord_157663
  simp only [CollatzResearch.WordTrace]
  refine ⟨5750442027821352541765643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3833628018547568361177095 5750442027821352541765643)
  ·
    refine ⟨8625663041732028812648465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5750442027821352541765643 8625663041732028812648465)
    ·
      refine ⟨6469247281299021609486349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8625663041732028812648465 6469247281299021609486349)
      ·
        refine ⟨2425967730487133103557381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6469247281299021609486349 2425967730487133103557381)
        ·
          refine ⟨454868949466337456917009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2425967730487133103557381 454868949466337456917009)
          ·
            refine ⟨341151712099753092687757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454868949466337456917009 341151712099753092687757)
            ·
              refine ⟨127931892037407409757909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341151712099753092687757 127931892037407409757909)
              ·
                refine ⟨2998403719626736166201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 127931892037407409757909 2998403719626736166201)
                ·
                  rfl

theorem cell23_157663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 7].length) (baseStart_157663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157663 prefixEnd_157663 := by exact prefixLift 157663
  have htrace : WordTrace (prefixWord ++ tailWord_157663) baseStart_157663 baseEnd_157663 := by
    simpa [prefixWord, tailWord_157663, baseEnd_157663] using wordTrace_append hprefix tailTrace_157663
  have hstable : (prefixWord ++ tailWord_157663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157663).length < 2 ^ (prefixWord ++ tailWord_157663).sum := by decide
  have hdescent : baseEnd_157663 < baseStart_157663 := by decide
  rcases family_descends (prefixWord ++ tailWord_157663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157674 : List Nat := [3, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_157674 : Nat := 118140960795 + 157674 * 2 ^ 59
def prefixEnd_157674 : Nat := 4983230072969 + 3 ^ 40 * 157674 * 2
def baseEnd_157674 : Nat := 80962548717121333449877

theorem tailTrace_157674 : CollatzResearch.WordTrace tailWord_157674 prefixEnd_157674 80962548717121333449877 := by
  unfold tailWord_157674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437710807695375355104019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3833895487187667613610717 1437710807695375355104019)
  ·
    refine ⟨2156566211543063032656029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1437710807695375355104019 2156566211543063032656029)
    ·
      refine ⟨808712329328648637246011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2156566211543063032656029 808712329328648637246011)
      ·
        refine ⟨1213068493992972955869017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808712329328648637246011 1213068493992972955869017)
        ·
          refine ⟨909801370494729716901763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1213068493992972955869017 909801370494729716901763)
          ·
            refine ⟨1364702055742094575352645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909801370494729716901763 1364702055742094575352645)
            ·
              refine ⟨255881635451642732878621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1364702055742094575352645 255881635451642732878621)
              ·
                refine ⟨95955613294366024829483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255881635451642732878621 95955613294366024829483)
                ·
                  refine ⟨143933419941549037244225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95955613294366024829483 143933419941549037244225)
                  ·
                    refine ⟨107950064956161777933169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 143933419941549037244225 107950064956161777933169)
                    ·
                      refine ⟨80962548717121333449877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107950064956161777933169 80962548717121333449877)
                      ·
                        rfl

theorem cell23_157674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_157674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157674 prefixEnd_157674 := by exact prefixLift 157674
  have htrace : WordTrace (prefixWord ++ tailWord_157674) baseStart_157674 baseEnd_157674 := by
    simpa [prefixWord, tailWord_157674, baseEnd_157674] using wordTrace_append hprefix tailTrace_157674
  have hstable : (prefixWord ++ tailWord_157674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157674).length < 2 ^ (prefixWord ++ tailWord_157674).sum := by decide
  have hdescent : baseEnd_157674 < baseStart_157674 := by decide
  rcases family_descends (prefixWord ++ tailWord_157674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157696 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 4]
def baseStart_157696 : Nat := 118140960795 + 157696 * 2 ^ 59
def prefixEnd_157696 : Nat := 4983230072969 + 3 ^ 40 * 157696 * 2
def baseEnd_157696 : Nat := 80973845291520247374775

theorem tailTrace_157696 : CollatzResearch.WordTrace tailWord_157696 prefixEnd_157696 80973845291520247374775 := by
  unfold tailWord_157696
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875822818350899588858471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3834430424467866118477961 2875822818350899588858471)
  ·
    refine ⟨4313734227526349383287707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2875822818350899588858471 4313734227526349383287707)
    ·
      refine ⟨6470601341289524074931561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4313734227526349383287707 6470601341289524074931561)
      ·
        refine ⟨4852951005967143056198671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6470601341289524074931561 4852951005967143056198671)
        ·
          refine ⟨7279426508950714584298007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4852951005967143056198671 7279426508950714584298007)
          ·
            refine ⟨10919139763426071876447011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7279426508950714584298007 10919139763426071876447011)
            ·
              refine ⟨16378709645139107814670517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10919139763426071876447011 16378709645139107814670517)
              ·
                refine ⟨1535504029231791357625361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16378709645139107814670517 1535504029231791357625361)
                ·
                  refine ⟨1151628021923843518219021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1535504029231791357625361 1151628021923843518219021)
                  ·
                    refine ⟨431860508221441319332133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151628021923843518219021 431860508221441319332133)
                    ·
                      refine ⟨80973845291520247374775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 431860508221441319332133 80973845291520247374775)
                      ·
                        rfl

theorem cell23_157696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_157696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157696 prefixEnd_157696 := by exact prefixLift 157696
  have htrace : WordTrace (prefixWord ++ tailWord_157696) baseStart_157696 baseEnd_157696 := by
    simpa [prefixWord, tailWord_157696, baseEnd_157696] using wordTrace_append hprefix tailTrace_157696
  have hstable : (prefixWord ++ tailWord_157696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157696).length < 2 ^ (prefixWord ++ tailWord_157696).sum := by decide
  have hdescent : baseEnd_157696 < baseStart_157696 := by decide
  rcases family_descends (prefixWord ++ tailWord_157696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157707 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 2, 1, 3]
def baseStart_157707 : Nat := 118140960795 + 157707 * 2 ^ 59
def prefixEnd_157707 : Nat := 4983230072969 + 3 ^ 40 * 157707 * 2
def baseEnd_157707 : Nat := 80979493578719704337225

theorem tailTrace_157707 : CollatzResearch.WordTrace tailWord_157707 prefixEnd_157707 80979493578719704337225 := by
  unfold tailWord_157707
  simp only [CollatzResearch.WordTrace]
  refine ⟨5752046839661948056367375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3834697893107965370911583 5752046839661948056367375)
  ·
    refine ⟨8628070259492922084551063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5752046839661948056367375 8628070259492922084551063)
    ·
      refine ⟨12942105389239383126826595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8628070259492922084551063 12942105389239383126826595)
      ·
        refine ⟨19413158083859074690239893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12942105389239383126826595 19413158083859074690239893)
        ·
          refine ⟨909991785180894126104995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19413158083859074690239893 909991785180894126104995)
          ·
            refine ⟨1364987677771341189157493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909991785180894126104995 1364987677771341189157493)
            ·
              refine ⟨127967594791063236483515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1364987677771341189157493 127967594791063236483515)
              ·
                refine ⟨191951392186594854725273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127967594791063236483515 191951392186594854725273)
                ·
                  refine ⟨143963544139946141043955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191951392186594854725273 143963544139946141043955)
                  ·
                    refine ⟨215945316209919211565933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 143963544139946141043955 215945316209919211565933)
                    ·
                      refine ⟨80979493578719704337225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 215945316209919211565933 80979493578719704337225)
                      ·
                        rfl

theorem cell23_157707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 2, 1, 3].length) (baseStart_157707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157707 prefixEnd_157707 := by exact prefixLift 157707
  have htrace : WordTrace (prefixWord ++ tailWord_157707) baseStart_157707 baseEnd_157707 := by
    simpa [prefixWord, tailWord_157707, baseEnd_157707] using wordTrace_append hprefix tailTrace_157707
  have hstable : (prefixWord ++ tailWord_157707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157707).length < 2 ^ (prefixWord ++ tailWord_157707).sum := by decide
  have hdescent : baseEnd_157707 < baseStart_157707 := by decide
  rcases family_descends (prefixWord ++ tailWord_157707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157730 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_157730 : Nat := 118140960795 + 157730 * 2 ^ 59
def prefixEnd_157730 : Nat := 4983230072969 + 3 ^ 40 * 157730 * 2
def baseEnd_157730 : Nat := 80991303633773114349619

theorem tailTrace_157730 : CollatzResearch.WordTrace tailWord_157730 prefixEnd_157730 80991303633773114349619 := by
  unfold tailWord_157730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438221429644655746113661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3835257145719081989636429 1438221429644655746113661)
  ·
    refine ⟨539333036116745904792623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1438221429644655746113661 539333036116745904792623)
    ·
      refine ⟨808999554175118857188935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 539333036116745904792623 808999554175118857188935)
      ·
        refine ⟨1213499331262678285783403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808999554175118857188935 1213499331262678285783403)
        ·
          refine ⟨1820248996894017428675105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213499331262678285783403 1820248996894017428675105)
          ·
            refine ⟨1365186747670513071506329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1820248996894017428675105 1365186747670513071506329)
            ·
              refine ⟨1023890060752884803629747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1365186747670513071506329 1023890060752884803629747)
              ·
                refine ⟨1535835091129327205444621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023890060752884803629747 1535835091129327205444621)
                ·
                  refine ⟨575938159173497702041733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1535835091129327205444621 575938159173497702041733)
                  ·
                    refine ⟨107988404845030819132825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575938159173497702041733 107988404845030819132825)
                    ·
                      refine ⟨80991303633773114349619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 107988404845030819132825 80991303633773114349619)
                      ·
                        rfl

theorem cell23_157730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_157730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157730 prefixEnd_157730 := by exact prefixLift 157730
  have htrace : WordTrace (prefixWord ++ tailWord_157730) baseStart_157730 baseEnd_157730 := by
    simpa [prefixWord, tailWord_157730, baseEnd_157730] using wordTrace_append hprefix tailTrace_157730
  have hstable : (prefixWord ++ tailWord_157730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157730).length < 2 ^ (prefixWord ++ tailWord_157730).sum := by decide
  have hdescent : baseEnd_157730 < baseStart_157730 := by decide
  rcases family_descends (prefixWord ++ tailWord_157730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157733 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_157733 : Nat := 118140960795 + 157733 * 2 ^ 59
def prefixEnd_157733 : Nat := 4983230072969 + 3 ^ 40 * 157733 * 2
def baseEnd_157733 : Nat := 80992844075736602612105

theorem tailTrace_157733 : CollatzResearch.WordTrace tailWord_157733 prefixEnd_157733 80992844075736602612105 := by
  unfold tailWord_157733
  simp only [CollatzResearch.WordTrace]
  refine ⟨5752995137567754496813853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3835330091711836331209235 5752995137567754496813853)
  ·
    refine ⟨2157373176587907936305195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5752995137567754496813853 2157373176587907936305195)
    ·
      refine ⟨3236059764881861904457793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2157373176587907936305195 3236059764881861904457793)
      ·
        refine ⟨2427044823661396428343345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3236059764881861904457793 2427044823661396428343345)
        ·
          refine ⟨1820283617746047321257509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2427044823661396428343345 1820283617746047321257509)
          ·
            refine ⟨341303178327383872735783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1820283617746047321257509 341303178327383872735783)
            ·
              refine ⟨511954767491075809103675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341303178327383872735783 511954767491075809103675)
              ·
                refine ⟨767932151236613713655513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511954767491075809103675 767932151236613713655513)
                ·
                  refine ⟨575949113427460285241635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 767932151236613713655513 575949113427460285241635)
                  ·
                    refine ⟨863923670141190427862453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 575949113427460285241635 863923670141190427862453)
                    ·
                      refine ⟨80992844075736602612105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 863923670141190427862453 80992844075736602612105)
                      ·
                        rfl

theorem cell23_157733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_157733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157733 prefixEnd_157733 := by exact prefixLift 157733
  have htrace : WordTrace (prefixWord ++ tailWord_157733) baseStart_157733 baseEnd_157733 := by
    simpa [prefixWord, tailWord_157733, baseEnd_157733] using wordTrace_append hprefix tailTrace_157733
  have hstable : (prefixWord ++ tailWord_157733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157733).length < 2 ^ (prefixWord ++ tailWord_157733).sum := by decide
  have hdescent : baseEnd_157733 < baseStart_157733 := by decide
  rcases family_descends (prefixWord ++ tailWord_157733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157750 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_157750 : Nat := 118140960795 + 157750 * 2 ^ 59
def prefixEnd_157750 : Nat := 4983230072969 + 3 ^ 40 * 157750 * 2
def baseEnd_157750 : Nat := 81001573246863036099527

theorem tailTrace_157750 : CollatzResearch.WordTrace tailWord_157750 prefixEnd_157750 81001573246863036099527 := by
  unfold tailWord_157750
  simp only [CollatzResearch.WordTrace]
  refine ⟨359600948656635400011419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3835743452337444266788469 359600948656635400011419)
  ·
    refine ⟨539401422984953100017129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 359600948656635400011419 539401422984953100017129)
    ·
      refine ⟨404551067238714825012847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 539401422984953100017129 404551067238714825012847)
      ·
        refine ⟨606826600858072237519271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404551067238714825012847 606826600858072237519271)
        ·
          refine ⟨910239901287108356278907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606826600858072237519271 910239901287108356278907)
          ·
            refine ⟨1365359851930662534418361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910239901287108356278907 1365359851930662534418361)
            ·
              refine ⟨1024019888947996900813771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1365359851930662534418361 1024019888947996900813771)
              ·
                refine ⟨1536029833421995351220657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024019888947996900813771 1536029833421995351220657)
                ·
                  refine ⟨1152022375066496513415493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1536029833421995351220657 1152022375066496513415493)
                  ·
                    refine ⟨216004195324968096265405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1152022375066496513415493 216004195324968096265405)
                    ·
                      refine ⟨81001573246863036099527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 216004195324968096265405 81001573246863036099527)
                      ·
                        rfl

theorem cell23_157750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_157750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157750 prefixEnd_157750 := by exact prefixLift 157750
  have htrace : WordTrace (prefixWord ++ tailWord_157750) baseStart_157750 baseEnd_157750 := by
    simpa [prefixWord, tailWord_157750, baseEnd_157750] using wordTrace_append hprefix tailTrace_157750
  have hstable : (prefixWord ++ tailWord_157750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157750).length < 2 ^ (prefixWord ++ tailWord_157750).sum := by decide
  have hdescent : baseEnd_157750 < baseStart_157750 := by decide
  rcases family_descends (prefixWord ++ tailWord_157750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157758 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_157758 : Nat := 118140960795 + 157758 * 2 ^ 59
def prefixEnd_157758 : Nat := 4983230072969 + 3 ^ 40 * 157758 * 2
def baseEnd_157758 : Nat := 81005681092099004799491

theorem tailTrace_157758 : CollatzResearch.WordTrace tailWord_157758 prefixEnd_157758 81005681092099004799491 := by
  unfold tailWord_157758
  simp only [CollatzResearch.WordTrace]
  refine ⟨719238370309647970809241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3835937974984789177649285 719238370309647970809241)
  ·
    refine ⟨539428777732235978106931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 719238370309647970809241 539428777732235978106931)
    ·
      refine ⟨809143166598353967160397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 539428777732235978106931 809143166598353967160397)
      ·
        refine ⟨303428687474382737685149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 809143166598353967160397 303428687474382737685149)
        ·
          refine ⟨113785757802893526631931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303428687474382737685149 113785757802893526631931)
          ·
            refine ⟨170678636704340289947897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113785757802893526631931 170678636704340289947897)
            ·
              refine ⟨128008977528255217460923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170678636704340289947897 128008977528255217460923)
              ·
                refine ⟨192013466292382826191385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128008977528255217460923 192013466292382826191385)
                ·
                  refine ⟨144010099719287119643539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192013466292382826191385 144010099719287119643539)
                  ·
                    refine ⟨216015149578930679465309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 144010099719287119643539 216015149578930679465309)
                    ·
                      refine ⟨81005681092099004799491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 216015149578930679465309 81005681092099004799491)
                      ·
                        rfl

theorem cell23_157758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_157758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157758 prefixEnd_157758 := by exact prefixLift 157758
  have htrace : WordTrace (prefixWord ++ tailWord_157758) baseStart_157758 baseEnd_157758 := by
    simpa [prefixWord, tailWord_157758, baseEnd_157758] using wordTrace_append hprefix tailTrace_157758
  have hstable : (prefixWord ++ tailWord_157758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157758).length < 2 ^ (prefixWord ++ tailWord_157758).sum := by decide
  have hdescent : baseEnd_157758 < baseStart_157758 := by decide
  rcases family_descends (prefixWord ++ tailWord_157758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157783 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 2, 5]
def baseStart_157783 : Nat := 118140960795 + 157783 * 2 ^ 59
def prefixEnd_157783 : Nat := 4983230072969 + 3 ^ 40 * 157783 * 2
def baseEnd_157783 : Nat := 27006172702820468995625

theorem tailTrace_157783 : CollatzResearch.WordTrace tailWord_157783 prefixEnd_157783 27006172702820468995625 := by
  unfold tailWord_157783
  simp only [CollatzResearch.WordTrace]
  refine ⟨5754818787386613036134003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3836545858257742024089335 5754818787386613036134003)
  ·
    refine ⟨8632228181079919554201005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5754818787386613036134003 8632228181079919554201005)
    ·
      refine ⟨3237085567904969832825377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8632228181079919554201005 3237085567904969832825377)
      ·
        refine ⟨2427814175928727374619033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3237085567904969832825377 2427814175928727374619033)
        ·
          refine ⟨1820860631946545530964275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2427814175928727374619033 1820860631946545530964275)
          ·
            refine ⟨2731290947919818296446413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820860631946545530964275 2731290947919818296446413)
            ·
              refine ⟨1024234105469931861167405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2731290947919818296446413 1024234105469931861167405)
              ·
                refine ⟨384087789551224447937777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1024234105469931861167405 384087789551224447937777)
                ·
                  refine ⟨288065842163418335953333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384087789551224447937777 288065842163418335953333)
                  ·
                    refine ⟨27006172702820468995625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 288065842163418335953333 27006172702820468995625)
                    ·
                      rfl

theorem cell23_157783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_157783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157783 prefixEnd_157783 := by exact prefixLift 157783
  have htrace : WordTrace (prefixWord ++ tailWord_157783) baseStart_157783 baseEnd_157783 := by
    simpa [prefixWord, tailWord_157783, baseEnd_157783] using wordTrace_append hprefix tailTrace_157783
  have hstable : (prefixWord ++ tailWord_157783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157783).length < 2 ^ (prefixWord ++ tailWord_157783).sum := by decide
  have hdescent : baseEnd_157783 < baseStart_157783 := by decide
  rcases family_descends (prefixWord ++ tailWord_157783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157820 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 1, 6, 2]
def baseStart_157820 : Nat := 118140960795 + 157820 * 2 ^ 59
def prefixEnd_157820 : Nat := 4983230072969 + 3 ^ 40 * 157820 * 2
def baseEnd_157820 : Nat := 81037516892677762224205

theorem tailTrace_157820 : CollatzResearch.WordTrace tailWord_157820 prefixEnd_157820 81037516892677762224205 := by
  unfold tailWord_157820
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878084144126284177615457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3837445525501712236820609 2878084144126284177615457)
  ·
    refine ⟨2158563108094713133211593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2878084144126284177615457 2158563108094713133211593)
    ·
      refine ⟨1618922331071034849908695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2158563108094713133211593 1618922331071034849908695)
      ·
        refine ⟨2428383496606552274863043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1618922331071034849908695 2428383496606552274863043)
        ·
          refine ⟨3642575244909828412294565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428383496606552274863043 3642575244909828412294565)
          ·
            refine ⟨682982858420592827305231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3642575244909828412294565 682982858420592827305231)
            ·
              refine ⟨1024474287630889240957847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682982858420592827305231 1024474287630889240957847)
              ·
                refine ⟨1536711431446333861436771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024474287630889240957847 1536711431446333861436771)
                ·
                  refine ⟨2305067147169500792155157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536711431446333861436771 2305067147169500792155157)
                  ·
                    refine ⟨108050022523570349632273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2305067147169500792155157 108050022523570349632273)
                    ·
                      refine ⟨81037516892677762224205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 108050022523570349632273 81037516892677762224205)
                      ·
                        rfl

theorem cell23_157820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_157820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157820 prefixEnd_157820 := by exact prefixLift 157820
  have htrace : WordTrace (prefixWord ++ tailWord_157820) baseStart_157820 baseEnd_157820 := by
    simpa [prefixWord, tailWord_157820, baseEnd_157820] using wordTrace_append hprefix tailTrace_157820
  have hstable : (prefixWord ++ tailWord_157820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157820).length < 2 ^ (prefixWord ++ tailWord_157820).sum := by decide
  have hdescent : baseEnd_157820 < baseStart_157820 := by decide
  rcases family_descends (prefixWord ++ tailWord_157820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157860 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 8]
def baseStart_157860 : Nat := 118140960795 + 157860 * 2 ^ 59
def prefixEnd_157860 : Nat := 4983230072969 + 3 ^ 40 * 157860 * 2
def baseEnd_157860 : Nat := 9006450679873067302669

theorem tailTrace_157860 : CollatzResearch.WordTrace tailWord_157860 prefixEnd_157860 9006450679873067302669 := by
  unfold tailWord_157860
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878813604053827593343517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3838418138738436791124689 2878813604053827593343517)
  ·
    refine ⟨1079555101520185347503819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2878813604053827593343517 1079555101520185347503819)
    ·
      refine ⟨1619332652280278021255729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1079555101520185347503819 1619332652280278021255729)
      ·
        refine ⟨1214499489210208515941797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1619332652280278021255729 1214499489210208515941797)
        ·
          refine ⟨227718654226914096739087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1214499489210208515941797 227718654226914096739087)
          ·
            refine ⟨341577981340371145108631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227718654226914096739087 341577981340371145108631)
            ·
              refine ⟨512366972010556717662947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341577981340371145108631 512366972010556717662947)
              ·
                refine ⟨768550458015835076494421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512366972010556717662947 768550458015835076494421)
                ·
                  refine ⟨9006450679873067302669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 768550458015835076494421 9006450679873067302669)
                  ·
                    rfl

theorem cell23_157860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_157860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157860 prefixEnd_157860 := by exact prefixLift 157860
  have htrace : WordTrace (prefixWord ++ tailWord_157860) baseStart_157860 baseEnd_157860 := by
    simpa [prefixWord, tailWord_157860, baseEnd_157860] using wordTrace_append hprefix tailTrace_157860
  have hstable : (prefixWord ++ tailWord_157860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157860).length < 2 ^ (prefixWord ++ tailWord_157860).sum := by decide
  have hdescent : baseEnd_157860 < baseStart_157860 := by decide
  rcases family_descends (prefixWord ++ tailWord_157860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157880 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 3, 5, 2]
def baseStart_157880 : Nat := 118140960795 + 157880 * 2 ^ 59
def prefixEnd_157880 : Nat := 4983230072969 + 3 ^ 40 * 157880 * 2
def baseEnd_157880 : Nat := 81068325731947527473929

theorem tailTrace_157880 : CollatzResearch.WordTrace tailWord_157880 prefixEnd_157880 81068325731947527473929 := by
  unfold tailWord_157880
  simp only [CollatzResearch.WordTrace]
  refine ⟨2879178334017599301207547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3838904445356799068276729 2879178334017599301207547)
  ·
    refine ⟨4318767501026398951811321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2879178334017599301207547 4318767501026398951811321)
    ·
      refine ⟨3239075625769799213858491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4318767501026398951811321 3239075625769799213858491)
      ·
        refine ⟨4858613438654698820787737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3239075625769799213858491 4858613438654698820787737)
        ·
          refine ⟨3643960078991024115590803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4858613438654698820787737 3643960078991024115590803)
          ·
            refine ⟨5465940118486536173386205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3643960078991024115590803 5465940118486536173386205)
            ·
              refine ⟨2049727544432451065019827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5465940118486536173386205 2049727544432451065019827)
              ·
                refine ⟨3074591316648676597529741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049727544432451065019827 3074591316648676597529741)
                ·
                  refine ⟨1152971743743253724073653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3074591316648676597529741 1152971743743253724073653)
                  ·
                    refine ⟨108091100975930036631905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1152971743743253724073653 108091100975930036631905)
                    ·
                      refine ⟨81068325731947527473929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 108091100975930036631905 81068325731947527473929)
                      ·
                        rfl

theorem cell23_157880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 5, 2].length) (baseStart_157880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157880 prefixEnd_157880 := by exact prefixLift 157880
  have htrace : WordTrace (prefixWord ++ tailWord_157880) baseStart_157880 baseEnd_157880 := by
    simpa [prefixWord, tailWord_157880, baseEnd_157880] using wordTrace_append hprefix tailTrace_157880
  have hstable : (prefixWord ++ tailWord_157880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157880).length < 2 ^ (prefixWord ++ tailWord_157880).sum := by decide
  have hdescent : baseEnd_157880 < baseStart_157880 := by decide
  rcases family_descends (prefixWord ++ tailWord_157880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157903 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 3, 6]
def baseStart_157903 : Nat := 118140960795 + 157903 * 2 ^ 59
def prefixEnd_157903 : Nat := 4983230072969 + 3 ^ 40 * 157903 * 2
def baseEnd_157903 : Nat := 27026711929000312495441

theorem tailTrace_157903 : CollatzResearch.WordTrace tailWord_157903 prefixEnd_157903 27026711929000312495441 := by
  unfold tailWord_157903
  simp only [CollatzResearch.WordTrace]
  refine ⟨5759195546951873530502363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3839463697967915687001575 5759195546951873530502363)
  ·
    refine ⟨8638793320427810295753545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5759195546951873530502363 8638793320427810295753545)
    ·
      refine ⟨6479094990320857721815159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8638793320427810295753545 6479094990320857721815159)
      ·
        refine ⟨9718642485481286582722739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6479094990320857721815159 9718642485481286582722739)
        ·
          refine ⟨14577963728221929874084109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9718642485481286582722739 14577963728221929874084109)
          ·
            refine ⟨5466736398083223702781541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14577963728221929874084109 5466736398083223702781541)
            ·
              refine ⟨1025013074640604444271539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5466736398083223702781541 1025013074640604444271539)
              ·
                refine ⟨1537519611960906666407309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025013074640604444271539 1537519611960906666407309)
                ·
                  refine ⟨576569854485339999902741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1537519611960906666407309 576569854485339999902741)
                  ·
                    refine ⟨27026711929000312495441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 576569854485339999902741 27026711929000312495441)
                    ·
                      rfl

theorem cell23_157903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_157903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157903 prefixEnd_157903 := by exact prefixLift 157903
  have htrace : WordTrace (prefixWord ++ tailWord_157903) baseStart_157903 baseEnd_157903 := by
    simpa [prefixWord, tailWord_157903, baseEnd_157903] using wordTrace_append hprefix tailTrace_157903
  have hstable : (prefixWord ++ tailWord_157903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157903).length < 2 ^ (prefixWord ++ tailWord_157903).sum := by decide
  have hdescent : baseEnd_157903 < baseStart_157903 := by decide
  rcases family_descends (prefixWord ++ tailWord_157903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157920 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 4, 4]
def baseStart_157920 : Nat := 118140960795 + 157920 * 2 ^ 59
def prefixEnd_157920 : Nat := 4983230072969 + 3 ^ 40 * 157920 * 2
def baseEnd_157920 : Nat := 27029621652709123657915

theorem tailTrace_157920 : CollatzResearch.WordTrace tailWord_157920 prefixEnd_157920 27029621652709123657915 := by
  unfold tailWord_157920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2879907793945142716935607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3839877058593523622580809 2879907793945142716935607)
  ·
    refine ⟨4319861690917714075403411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2879907793945142716935607 4319861690917714075403411)
    ·
      refine ⟨6479792536376571113105117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4319861690917714075403411 6479792536376571113105117)
      ·
        refine ⟨2429922201141214167414419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6479792536376571113105117 2429922201141214167414419)
        ·
          refine ⟨3644883301711821251121629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429922201141214167414419 3644883301711821251121629)
          ·
            refine ⟨1366831238141932969170611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3644883301711821251121629 1366831238141932969170611)
            ·
              refine ⟨2050246857212899453755917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366831238141932969170611 2050246857212899453755917)
              ·
                refine ⟨768842571454837295158469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2050246857212899453755917 768842571454837295158469)
                ·
                  refine ⟨144157982147781992842213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768842571454837295158469 144157982147781992842213)
                  ·
                    refine ⟨27029621652709123657915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144157982147781992842213 27029621652709123657915)
                    ·
                      rfl

theorem cell23_157920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4, 4].length) (baseStart_157920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157920 prefixEnd_157920 := by exact prefixLift 157920
  have htrace : WordTrace (prefixWord ++ tailWord_157920) baseStart_157920 baseEnd_157920 := by
    simpa [prefixWord, tailWord_157920, baseEnd_157920] using wordTrace_append hprefix tailTrace_157920
  have hstable : (prefixWord ++ tailWord_157920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157920).length < 2 ^ (prefixWord ++ tailWord_157920).sum := by decide
  have hdescent : baseEnd_157920 < baseStart_157920 := by decide
  rcases family_descends (prefixWord ++ tailWord_157920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157921 : List Nat := [1, 2, 3, 1, 3, 1, 5, 2, 1, 1, 3]
def baseStart_157921 : Nat := 118140960795 + 157921 * 2 ^ 59
def prefixEnd_157921 : Nat := 4983230072969 + 3 ^ 40 * 157921 * 2
def baseEnd_157921 : Nat := 81089378438781867061241

theorem tailTrace_157921 : CollatzResearch.WordTrace tailWord_157921 prefixEnd_157921 81089378438781867061241 := by
  unfold tailWord_157921
  simp only [CollatzResearch.WordTrace]
  refine ⟨5759852060886662604657617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3839901373924441736438411 5759852060886662604657617)
  ·
    refine ⟨4319889045664996953493213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5759852060886662604657617 4319889045664996953493213)
    ·
      refine ⟨1619958392124373857559955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4319889045664996953493213 1619958392124373857559955)
      ·
        refine ⟨2429937588186560786339933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619958392124373857559955 2429937588186560786339933)
        ·
          refine ⟨911226595569960294877475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2429937588186560786339933 911226595569960294877475)
          ·
            refine ⟨1366839893354940442316213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911226595569960294877475 1366839893354940442316213)
            ·
              refine ⟨128141240002025666467145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1366839893354940442316213 128141240002025666467145)
              ·
                refine ⟨96105930001519249850359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128141240002025666467145 96105930001519249850359)
                ·
                  refine ⟨144158895002278874775539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96105930001519249850359 144158895002278874775539)
                  ·
                    refine ⟨216238342503418312163309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 144158895002278874775539 216238342503418312163309)
                    ·
                      refine ⟨81089378438781867061241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 216238342503418312163309 81089378438781867061241)
                      ·
                        rfl

theorem cell23_157921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_157921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157921 prefixEnd_157921 := by exact prefixLift 157921
  have htrace : WordTrace (prefixWord ++ tailWord_157921) baseStart_157921 baseEnd_157921 := by
    simpa [prefixWord, tailWord_157921, baseEnd_157921] using wordTrace_append hprefix tailTrace_157921
  have hstable : (prefixWord ++ tailWord_157921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157921).length < 2 ^ (prefixWord ++ tailWord_157921).sum := by decide
  have hdescent : baseEnd_157921 < baseStart_157921 := by decide
  rcases family_descends (prefixWord ++ tailWord_157921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157930 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_157930 : Nat := 118140960795 + 157930 * 2 ^ 59
def prefixEnd_157930 : Nat := 4983230072969 + 3 ^ 40 * 157930 * 2
def baseEnd_157930 : Nat := 81093999764672331848699

theorem tailTrace_157930 : CollatzResearch.WordTrace tailWord_157930 prefixEnd_157930 81093999764672331848699 := by
  unfold tailWord_157930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440045079463514285433811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3840120211902704761156829 1440045079463514285433811)
  ·
    refine ⟨2160067619195271428150717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1440045079463514285433811 2160067619195271428150717)
    ·
      refine ⟨810025357198226785556519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2160067619195271428150717 810025357198226785556519)
      ·
        refine ⟨1215038035797340178334779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810025357198226785556519 1215038035797340178334779)
        ·
          refine ⟨1822557053696010267502169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215038035797340178334779 1822557053696010267502169)
          ·
            refine ⟨1366917790272007700626627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1822557053696010267502169 1366917790272007700626627)
            ·
              refine ⟨2050376685408011550939941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366917790272007700626627 2050376685408011550939941)
              ·
                refine ⟨384445628514002165801239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2050376685408011550939941 384445628514002165801239)
                ·
                  refine ⟨576668442771003248701859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384445628514002165801239 576668442771003248701859)
                  ·
                    refine ⟨865002664156504873052789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 576668442771003248701859 865002664156504873052789)
                    ·
                      refine ⟨81093999764672331848699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 865002664156504873052789 81093999764672331848699)
                      ·
                        rfl

theorem cell23_157930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_157930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157930 prefixEnd_157930 := by exact prefixLift 157930
  have htrace : WordTrace (prefixWord ++ tailWord_157930) baseStart_157930 baseEnd_157930 := by
    simpa [prefixWord, tailWord_157930, baseEnd_157930] using wordTrace_append hprefix tailTrace_157930
  have hstable : (prefixWord ++ tailWord_157930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157930).length < 2 ^ (prefixWord ++ tailWord_157930).sum := by decide
  have hdescent : baseEnd_157930 < baseStart_157930 := by decide
  rcases family_descends (prefixWord ++ tailWord_157930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157950 : List Nat := [4, 2, 2, 1, 1, 1, 1, 11]
def baseStart_157950 : Nat := 118140960795 + 157950 * 2 ^ 59
def prefixEnd_157950 : Nat := 4983230072969 + 3 ^ 40 * 157950 * 2
def baseEnd_157950 : Nat := 3003861828806009392541

theorem tailTrace_157950 : CollatzResearch.WordTrace tailWord_157950 prefixEnd_157950 3003861828806009392541 := by
  unfold tailWord_157950
  simp only [CollatzResearch.WordTrace]
  refine ⟨720113722222700069682913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3840606518521067038308869 720113722222700069682913)
  ·
    refine ⟨540085291667025052262185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 720113722222700069682913 540085291667025052262185)
    ·
      refine ⟨405063968750268789196639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 540085291667025052262185 405063968750268789196639)
      ·
        refine ⟨607595953125403183794959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405063968750268789196639 607595953125403183794959)
        ·
          refine ⟨911393929688104775692439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607595953125403183794959 911393929688104775692439)
          ·
            refine ⟨1367090894532157163538659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911393929688104775692439 1367090894532157163538659)
            ·
              refine ⟨2050636341798235745307989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367090894532157163538659 2050636341798235745307989)
              ·
                refine ⟨3003861828806009392541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 2050636341798235745307989 3003861828806009392541)
                ·
                  rfl

theorem cell23_157950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_157950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157950 prefixEnd_157950 := by exact prefixLift 157950
  have htrace : WordTrace (prefixWord ++ tailWord_157950) baseStart_157950 baseEnd_157950 := by
    simpa [prefixWord, tailWord_157950, baseEnd_157950] using wordTrace_append hprefix tailTrace_157950
  have hstable : (prefixWord ++ tailWord_157950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157950).length < 2 ^ (prefixWord ++ tailWord_157950).sum := by decide
  have hdescent : baseEnd_157950 < baseStart_157950 := by decide
  rcases family_descends (prefixWord ++ tailWord_157950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157964 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 1, 2, 3]
def baseStart_157964 : Nat := 118140960795 + 157964 * 2 ^ 59
def prefixEnd_157964 : Nat := 4983230072969 + 3 ^ 40 * 157964 * 2
def baseEnd_157964 : Nat := 81111458106925198823543

theorem tailTrace_157964 : CollatzResearch.WordTrace tailWord_157964 prefixEnd_157964 81111458106925198823543 := by
  unfold tailWord_157964
  simp only [CollatzResearch.WordTrace]
  refine ⟨2880710199865440474236473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3840946933153920632315297 2880710199865440474236473)
  ·
    refine ⟨2160532649899080355677355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2880710199865440474236473 2160532649899080355677355)
    ·
      refine ⟨3240798974848620533516033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2160532649899080355677355 3240798974848620533516033)
      ·
        refine ⟨2430599231136465400137025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3240798974848620533516033 2430599231136465400137025)
        ·
          refine ⟨1822949423352349050102769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2430599231136465400137025 1822949423352349050102769)
          ·
            refine ⟨1367212067514261787577077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1822949423352349050102769 1367212067514261787577077)
            ·
              refine ⟨128176131329462042585351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1367212067514261787577077 128176131329462042585351)
              ·
                refine ⟨192264196994193063878027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128176131329462042585351 192264196994193063878027)
                ·
                  refine ⟨288396295491289595817041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192264196994193063878027 288396295491289595817041)
                  ·
                    refine ⟨216297221618467196862781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 288396295491289595817041 216297221618467196862781)
                    ·
                      refine ⟨81111458106925198823543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 216297221618467196862781 81111458106925198823543)
                      ·
                        rfl

theorem cell23_157964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_157964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157964 prefixEnd_157964 := by exact prefixLift 157964
  have htrace : WordTrace (prefixWord ++ tailWord_157964) baseStart_157964 baseEnd_157964 := by
    simpa [prefixWord, tailWord_157964, baseEnd_157964] using wordTrace_append hprefix tailTrace_157964
  have hstable : (prefixWord ++ tailWord_157964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157964).length < 2 ^ (prefixWord ++ tailWord_157964).sum := by decide
  have hdescent : baseEnd_157964 < baseStart_157964 := by decide
  rcases family_descends (prefixWord ++ tailWord_157964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157978 : List Nat := [3, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2]
def baseStart_157978 : Nat := 118140960795 + 157978 * 2 ^ 59
def prefixEnd_157978 : Nat := 4983230072969 + 3 ^ 40 * 157978 * 2
def baseEnd_157978 : Nat := 81118646836088144048479

theorem tailTrace_157978 : CollatzResearch.WordTrace tailWord_157978 prefixEnd_157978 81118646836088144048479 := by
  unfold tailWord_157978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440482755420040334870647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3841287347786774226321725 1440482755420040334870647)
  ·
    refine ⟨2160724133130060502305971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1440482755420040334870647 2160724133130060502305971)
    ·
      refine ⟨3241086199695090753458957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2160724133130060502305971 3241086199695090753458957)
      ·
        refine ⟨1215407324885659032547109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3241086199695090753458957 1215407324885659032547109)
        ·
          refine ⟨227888873416061068602583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1215407324885659032547109 227888873416061068602583)
          ·
            refine ⟨341833310124091602903875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227888873416061068602583 341833310124091602903875)
            ·
              refine ⟨512749965186137404355813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341833310124091602903875 512749965186137404355813)
              ·
                refine ⟨96140618472400763316715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 512749965186137404355813 96140618472400763316715)
                ·
                  refine ⟨144210927708601144975073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96140618472400763316715 144210927708601144975073)
                  ·
                    refine ⟨108158195781450858731305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 144210927708601144975073 108158195781450858731305)
                    ·
                      refine ⟨81118646836088144048479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 108158195781450858731305 81118646836088144048479)
                      ·
                        rfl

theorem cell23_157978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_157978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157978 prefixEnd_157978 := by exact prefixLift 157978
  have htrace : WordTrace (prefixWord ++ tailWord_157978) baseStart_157978 baseEnd_157978 := by
    simpa [prefixWord, tailWord_157978, baseEnd_157978] using wordTrace_append hprefix tailTrace_157978
  have hstable : (prefixWord ++ tailWord_157978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157978).length < 2 ^ (prefixWord ++ tailWord_157978).sum := by decide
  have hdescent : baseEnd_157978 < baseStart_157978 := by decide
  rcases family_descends (prefixWord ++ tailWord_157978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157987 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 5, 3, 2]
def baseStart_157987 : Nat := 118140960795 + 157987 * 2 ^ 59
def prefixEnd_157987 : Nat := 4983230072969 + 3 ^ 40 * 157987 * 2
def baseEnd_157987 : Nat := 81123268161978608835937

theorem tailTrace_157987 : CollatzResearch.WordTrace tailWord_157987 prefixEnd_157987 81123268161978608835937 := by
  unfold tailWord_157987
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762259278647555876560215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3841506185765037251040143 5762259278647555876560215)
  ·
    refine ⟨8643388917971333814840323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5762259278647555876560215 8643388917971333814840323)
    ·
      refine ⟨12965083376957000722260485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8643388917971333814840323 12965083376957000722260485)
      ·
        refine ⟨2430953133179437635423841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12965083376957000722260485 2430953133179437635423841)
        ·
          refine ⟨1823214849884578226567881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2430953133179437635423841 1823214849884578226567881)
          ·
            refine ⟨1367411137413433669925911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1823214849884578226567881 1367411137413433669925911)
            ·
              refine ⟨2051116706120150504888867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367411137413433669925911 2051116706120150504888867)
              ·
                refine ⟨3076675059180225757333301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051116706120150504888867 3076675059180225757333301)
                ·
                  refine ⟨288438286798146164749997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3076675059180225757333301 288438286798146164749997)
                  ·
                    refine ⟨108164357549304811781249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 288438286798146164749997 108164357549304811781249)
                    ·
                      refine ⟨81123268161978608835937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 108164357549304811781249 81123268161978608835937)
                      ·
                        rfl

theorem cell23_157987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_157987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_157987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_157987 prefixEnd_157987 := by exact prefixLift 157987
  have htrace : WordTrace (prefixWord ++ tailWord_157987) baseStart_157987 baseEnd_157987 := by
    simpa [prefixWord, tailWord_157987, baseEnd_157987] using wordTrace_append hprefix tailTrace_157987
  have hstable : (prefixWord ++ tailWord_157987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157987).length < 2 ^ (prefixWord ++ tailWord_157987).sum := by decide
  have hdescent : baseEnd_157987 < baseStart_157987 := by decide
  rcases family_descends (prefixWord ++ tailWord_157987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158087 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 2, 5]
def baseStart_158087 : Nat := 118140960795 + 158087 * 2 ^ 59
def prefixEnd_158087 : Nat := 4983230072969 + 3 ^ 40 * 158087 * 2
def baseEnd_158087 : Nat := 27058205409142739195159

theorem tailTrace_158087 : CollatzResearch.WordTrace tailWord_158087 prefixEnd_158087 27058205409142739195159 := by
  unfold tailWord_158087
  simp only [CollatzResearch.WordTrace]
  refine ⟨5765906578285272955200515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3843937718856848636800343 5765906578285272955200515)
  ·
    refine ⟨8648859867427909432800773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5765906578285272955200515 8648859867427909432800773)
    ·
      refine ⟨1621661225142733018650145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8648859867427909432800773 1621661225142733018650145)
      ·
        refine ⟨1216245918857049763987609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1621661225142733018650145 1216245918857049763987609)
        ·
          refine ⟨912184439142787322990707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1216245918857049763987609 912184439142787322990707)
          ·
            refine ⟨1368276658714180984486061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912184439142787322990707 1368276658714180984486061)
            ·
              refine ⟨513103747017817869182273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1368276658714180984486061 513103747017817869182273)
              ·
                refine ⟨384827810263363401886705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513103747017817869182273 384827810263363401886705)
                ·
                  refine ⟨288620857697522551415029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384827810263363401886705 288620857697522551415029)
                  ·
                    refine ⟨27058205409142739195159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 288620857697522551415029 27058205409142739195159)
                    ·
                      rfl

theorem cell23_158087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_158087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158087 prefixEnd_158087 := by exact prefixLift 158087
  have htrace : WordTrace (prefixWord ++ tailWord_158087) baseStart_158087 baseEnd_158087 := by
    simpa [prefixWord, tailWord_158087, baseEnd_158087] using wordTrace_append hprefix tailTrace_158087
  have hstable : (prefixWord ++ tailWord_158087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158087).length < 2 ^ (prefixWord ++ tailWord_158087).sum := by decide
  have hdescent : baseEnd_158087 < baseStart_158087 := by decide
  rcases family_descends (prefixWord ++ tailWord_158087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158117 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 5, 4]
def baseStart_158117 : Nat := 118140960795 + 158117 * 2 ^ 59
def prefixEnd_158117 : Nat := 4983230072969 + 3 ^ 40 * 158117 * 2
def baseEnd_158117 : Nat := 27063340215687700070113

theorem tailTrace_158117 : CollatzResearch.WordTrace tailWord_158117 prefixEnd_158117 27063340215687700070113 := by
  unfold tailWord_158117
  simp only [CollatzResearch.WordTrace]
  refine ⟨5767000768176588078792605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3844667178784392052528403 5767000768176588078792605)
  ·
    refine ⟨2162625288066220529547227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5767000768176588078792605 2162625288066220529547227)
    ·
      refine ⟨3243937932099330794320841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2162625288066220529547227 3243937932099330794320841)
      ·
        refine ⟨2432953449074498095740631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3243937932099330794320841 2432953449074498095740631)
        ·
          refine ⟨3649430173611747143610947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432953449074498095740631 3649430173611747143610947)
          ·
            refine ⟨5474145260417620715416421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3649430173611747143610947 5474145260417620715416421)
            ·
              refine ⟨1026402236328303884140579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5474145260417620715416421 1026402236328303884140579)
              ·
                refine ⟨1539603354492455826210869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026402236328303884140579 1539603354492455826210869)
                ·
                  refine ⟨144337814483667733707269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1539603354492455826210869 144337814483667733707269)
                  ·
                    refine ⟨27063340215687700070113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144337814483667733707269 27063340215687700070113)
                    ·
                      rfl

theorem cell23_158117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_158117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158117 prefixEnd_158117 := by exact prefixLift 158117
  have htrace : WordTrace (prefixWord ++ tailWord_158117) baseStart_158117 baseEnd_158117 := by
    simpa [prefixWord, tailWord_158117, baseEnd_158117] using wordTrace_append hprefix tailTrace_158117
  have hstable : (prefixWord ++ tailWord_158117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158117).length < 2 ^ (prefixWord ++ tailWord_158117).sum := by decide
  have hdescent : baseEnd_158117 < baseStart_158117 := by decide
  rcases family_descends (prefixWord ++ tailWord_158117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158151 : List Nat := [1, 1, 4, 1, 1, 5, 1, 4, 1, 4]
def baseStart_158151 : Nat := 118140960795 + 158151 * 2 ^ 59
def prefixEnd_158151 : Nat := 4983230072969 + 3 ^ 40 * 158151 * 2
def baseEnd_158151 : Nat := 27069159663105322395061

theorem tailTrace_158151 : CollatzResearch.WordTrace tailWord_158151 prefixEnd_158151 27069159663105322395061 := by
  unfold tailWord_158151
  simp only [CollatzResearch.WordTrace]
  refine ⟨5768240850053411885530307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3845493900035607923686871 5768240850053411885530307)
  ·
    refine ⟨8652361275080117828295461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5768240850053411885530307 8652361275080117828295461)
    ·
      refine ⟨1622317739077522092805399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8652361275080117828295461 1622317739077522092805399)
      ·
        refine ⟨2433476608616283139208099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622317739077522092805399 2433476608616283139208099)
        ·
          refine ⟨3650214912924424708812149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2433476608616283139208099 3650214912924424708812149)
          ·
            refine ⟨342207648086664816451139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3650214912924424708812149 342207648086664816451139)
            ·
              refine ⟨513311472129997224676709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342207648086664816451139 513311472129997224676709)
              ·
                refine ⟨96245901024374479626883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513311472129997224676709 96245901024374479626883)
                ·
                  refine ⟨144368851536561719440325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96245901024374479626883 144368851536561719440325)
                  ·
                    refine ⟨27069159663105322395061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144368851536561719440325 27069159663105322395061)
                    ·
                      rfl

theorem cell23_158151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_158151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158151 prefixEnd_158151 := by exact prefixLift 158151
  have htrace : WordTrace (prefixWord ++ tailWord_158151) baseStart_158151 baseEnd_158151 := by
    simpa [prefixWord, tailWord_158151, baseEnd_158151] using wordTrace_append hprefix tailTrace_158151
  have hstable : (prefixWord ++ tailWord_158151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158151).length < 2 ^ (prefixWord ++ tailWord_158151).sum := by decide
  have hdescent : baseEnd_158151 < baseStart_158151 := by decide
  rcases family_descends (prefixWord ++ tailWord_158151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158160 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 1, 11]
def baseStart_158160 : Nat := 118140960795 + 158160 * 2 ^ 59
def prefixEnd_158160 : Nat := 4983230072969 + 3 ^ 40 * 158160 * 2
def baseEnd_158160 : Nat := 27070700105068810657547

theorem tailTrace_158160 : CollatzResearch.WordTrace tailWord_158160 prefixEnd_158160 27070700105068810657547 := by
  unfold tailWord_158160
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884284553510403211303967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3845712738013870948405289 2884284553510403211303967)
  ·
    refine ⟨4326426830265604816955951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2884284553510403211303967 4326426830265604816955951)
    ·
      refine ⟨6489640245398407225433927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4326426830265604816955951 6489640245398407225433927)
      ·
        refine ⟨9734460368097610838150891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6489640245398407225433927 9734460368097610838150891)
        ·
          refine ⟨14601690552146416257226337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9734460368097610838150891 14601690552146416257226337)
          ·
            refine ⟨10951267914109812192919753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14601690552146416257226337 10951267914109812192919753)
            ·
              refine ⟨8213450935582359144689815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10951267914109812192919753 8213450935582359144689815)
              ·
                refine ⟨12320176403373538717034723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8213450935582359144689815 12320176403373538717034723)
                ·
                  refine ⟨18480264605060308075552085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12320176403373538717034723 18480264605060308075552085)
                  ·
                    refine ⟨27070700105068810657547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 18480264605060308075552085 27070700105068810657547)
                    ·
                      rfl

theorem cell23_158160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_158160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158160 prefixEnd_158160 := by exact prefixLift 158160
  have htrace : WordTrace (prefixWord ++ tailWord_158160) baseStart_158160 baseEnd_158160 := by
    simpa [prefixWord, tailWord_158160, baseEnd_158160] using wordTrace_append hprefix tailTrace_158160
  have hstable : (prefixWord ++ tailWord_158160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158160).length < 2 ^ (prefixWord ++ tailWord_158160).sum := by decide
  have hdescent : baseEnd_158160 < baseStart_158160 := by decide
  rcases family_descends (prefixWord ++ tailWord_158160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158164 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 6]
def baseStart_158164 : Nat := 118140960795 + 158164 * 2 ^ 59
def prefixEnd_158164 : Nat := 4983230072969 + 3 ^ 40 * 158164 * 2
def baseEnd_158164 : Nat := 9023794915313824035847

theorem tailTrace_158164 : CollatzResearch.WordTrace tailWord_158164 prefixEnd_158164 9023794915313824035847 := by
  unfold tailWord_158164
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884357499503157552876773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3845809999337543403835697 2884357499503157552876773)
  ·
    refine ⟨540817031156842041164395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2884357499503157552876773 540817031156842041164395)
    ·
      refine ⟨811225546735263061746593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540817031156842041164395 811225546735263061746593)
      ·
        refine ⟨608419160051447296309945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 811225546735263061746593 608419160051447296309945)
        ·
          refine ⟨456314370038585472232459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608419160051447296309945 456314370038585472232459)
          ·
            refine ⟨684471555057878208348689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456314370038585472232459 684471555057878208348689)
            ·
              refine ⟨513353666293408656261517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684471555057878208348689 513353666293408656261517)
              ·
                refine ⟨192507624860028246098069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 513353666293408656261517 192507624860028246098069)
                ·
                  refine ⟨9023794915313824035847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 192507624860028246098069 9023794915313824035847)
                  ·
                    rfl

theorem cell23_158164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_158164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158164 prefixEnd_158164 := by exact prefixLift 158164
  have htrace : WordTrace (prefixWord ++ tailWord_158164) baseStart_158164 baseEnd_158164 := by
    simpa [prefixWord, tailWord_158164, baseEnd_158164] using wordTrace_append hprefix tailTrace_158164
  have hstable : (prefixWord ++ tailWord_158164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158164).length < 2 ^ (prefixWord ++ tailWord_158164).sum := by decide
  have hdescent : baseEnd_158164 < baseStart_158164 := by decide
  rcases family_descends (prefixWord ++ tailWord_158164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158177 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 3, 5]
def baseStart_158177 : Nat := 118140960795 + 158177 * 2 ^ 59
def prefixEnd_158177 : Nat := 4983230072969 + 3 ^ 40 * 158177 * 2
def baseEnd_158177 : Nat := 27073609828777621820021

theorem tailTrace_158177 : CollatzResearch.WordTrace tailWord_158177 prefixEnd_158177 27073609828777621820021 := by
  unfold tailWord_158177
  simp only [CollatzResearch.WordTrace]
  refine ⟨5769189147959218325976785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3846126098639478883984523 5769189147959218325976785)
  ·
    refine ⟨4326891860969413744482589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5769189147959218325976785 4326891860969413744482589)
    ·
      refine ⟨1622584447863530154180971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4326891860969413744482589 1622584447863530154180971)
      ·
        refine ⟨2433876671795295231271457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622584447863530154180971 2433876671795295231271457)
        ·
          refine ⟨1825407503846471423453593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2433876671795295231271457 1825407503846471423453593)
          ·
            refine ⟨1369055627884853567590195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1825407503846471423453593 1369055627884853567590195)
            ·
              refine ⟨2053583441827280351385293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369055627884853567590195 2053583441827280351385293)
              ·
                refine ⟨770093790685230131769485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053583441827280351385293 770093790685230131769485)
                ·
                  refine ⟨288785171506961299413557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770093790685230131769485 288785171506961299413557)
                  ·
                    refine ⟨27073609828777621820021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 288785171506961299413557 27073609828777621820021)
                    ·
                      rfl

theorem cell23_158177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_158177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158177 prefixEnd_158177 := by exact prefixLift 158177
  have htrace : WordTrace (prefixWord ++ tailWord_158177) baseStart_158177 baseEnd_158177 := by
    simpa [prefixWord, tailWord_158177, baseEnd_158177] using wordTrace_append hprefix tailTrace_158177
  have hstable : (prefixWord ++ tailWord_158177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158177).length < 2 ^ (prefixWord ++ tailWord_158177).sum := by decide
  have hdescent : baseEnd_158177 < baseStart_158177 := by decide
  rcases family_descends (prefixWord ++ tailWord_158177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158178 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_158178 : Nat := 118140960795 + 158178 * 2 ^ 59
def prefixEnd_158178 : Nat := 4983230072969 + 3 ^ 40 * 158178 * 2
def baseEnd_158178 : Nat := 81221342966987361547559

theorem tailTrace_158178 : CollatzResearch.WordTrace tailWord_158178 prefixEnd_158178 81221342966987361547559 := by
  unfold tailWord_158178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1442306405238898874190797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3846150413970396997842125 1442306405238898874190797)
  ·
    refine ⟨540864901964587077821549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1442306405238898874190797 540864901964587077821549)
    ·
      refine ⟨202824338236720154183081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 540864901964587077821549 202824338236720154183081)
      ·
        refine ⟨152118253677540115637311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202824338236720154183081 152118253677540115637311)
        ·
          refine ⟨228177380516310173455967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152118253677540115637311 228177380516310173455967)
          ·
            refine ⟨342266070774465260183951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228177380516310173455967 342266070774465260183951)
            ·
              refine ⟨513399106161697890275927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342266070774465260183951 513399106161697890275927)
              ·
                refine ⟨770098659242546835413891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513399106161697890275927 770098659242546835413891)
                ·
                  refine ⟨1155147988863820253120837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770098659242546835413891 1155147988863820253120837)
                  ·
                    refine ⟨216590247911966297460157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1155147988863820253120837 216590247911966297460157)
                    ·
                      refine ⟨81221342966987361547559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 216590247911966297460157 81221342966987361547559)
                      ·
                        rfl

theorem cell23_158178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_158178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158178 prefixEnd_158178 := by exact prefixLift 158178
  have htrace : WordTrace (prefixWord ++ tailWord_158178) baseStart_158178 baseEnd_158178 := by
    simpa [prefixWord, tailWord_158178, baseEnd_158178] using wordTrace_append hprefix tailTrace_158178
  have hstable : (prefixWord ++ tailWord_158178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158178).length < 2 ^ (prefixWord ++ tailWord_158178).sum := by decide
  have hdescent : baseEnd_158178 < baseStart_158178 := by decide
  rcases family_descends (prefixWord ++ tailWord_158178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158217 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 2, 6, 3]
def baseStart_158217 : Nat := 118140960795 + 158217 * 2 ^ 59
def prefixEnd_158217 : Nat := 4983230072969 + 3 ^ 40 * 158217 * 2
def baseEnd_158217 : Nat := 81241368712512708959879

theorem tailTrace_158217 : CollatzResearch.WordTrace tailWord_158217 prefixEnd_158217 81241368712512708959879 := by
  unfold tailWord_158217
  simp only [CollatzResearch.WordTrace]
  refine ⟨5770648067814305157432905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3847098711876203438288603 5770648067814305157432905)
  ·
    refine ⟨4327986050860728868074679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5770648067814305157432905 4327986050860728868074679)
    ·
      refine ⟨6491979076291093302112019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4327986050860728868074679 6491979076291093302112019)
      ·
        refine ⟨9737968614436639953168029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6491979076291093302112019 9737968614436639953168029)
        ·
          refine ⟨3651738230413739982438011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9737968614436639953168029 3651738230413739982438011)
          ·
            refine ⟨5477607345620609973657017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651738230413739982438011 5477607345620609973657017)
            ·
              refine ⟨4108205509215457480242763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5477607345620609973657017 4108205509215457480242763)
              ·
                refine ⟨6162308263823186220364145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4108205509215457480242763 6162308263823186220364145)
                ·
                  refine ⟨4621731197867389665273109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6162308263823186220364145 4621731197867389665273109)
                  ·
                    refine ⟨216643649900033890559677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4621731197867389665273109 216643649900033890559677)
                    ·
                      refine ⟨81241368712512708959879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 216643649900033890559677 81241368712512708959879)
                      ·
                        rfl

theorem cell23_158217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6, 3].length) (baseStart_158217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158217 prefixEnd_158217 := by exact prefixLift 158217
  have htrace : WordTrace (prefixWord ++ tailWord_158217) baseStart_158217 baseEnd_158217 := by
    simpa [prefixWord, tailWord_158217, baseEnd_158217] using wordTrace_append hprefix tailTrace_158217
  have hstable : (prefixWord ++ tailWord_158217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158217).length < 2 ^ (prefixWord ++ tailWord_158217).sum := by decide
  have hdescent : baseEnd_158217 < baseStart_158217 := by decide
  rcases family_descends (prefixWord ++ tailWord_158217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158227 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 6]
def baseStart_158227 : Nat := 118140960795 + 158227 * 2 ^ 59
def prefixEnd_158227 : Nat := 4983230072969 + 3 ^ 40 * 158227 * 2
def baseEnd_158227 : Nat := 81246503519057669834833

theorem tailTrace_158227 : CollatzResearch.WordTrace tailWord_158227 prefixEnd_158227 81246503519057669834833 := by
  unfold tailWord_158227
  simp only [CollatzResearch.WordTrace]
  refine ⟨5771012797778076865296935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3847341865185384576864623 5771012797778076865296935)
  ·
    refine ⟨8656519196667115297945403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5771012797778076865296935 8656519196667115297945403)
    ·
      refine ⟨12984778795000672946918105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8656519196667115297945403 12984778795000672946918105)
      ·
        refine ⟨9738584096250504710188579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12984778795000672946918105 9738584096250504710188579)
        ·
          refine ⟨14607876144375757065282869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9738584096250504710188579 14607876144375757065282869)
          ·
            refine ⟨1369488388535227224870269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14607876144375757065282869 1369488388535227224870269)
            ·
              refine ⟨513558145700710209326351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1369488388535227224870269 513558145700710209326351)
              ·
                refine ⟨770337218551065313989527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513558145700710209326351 770337218551065313989527)
                ·
                  refine ⟨1155505827826597970984291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770337218551065313989527 1155505827826597970984291)
                  ·
                    refine ⟨1733258741739896956476437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1155505827826597970984291 1733258741739896956476437)
                    ·
                      refine ⟨81246503519057669834833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1733258741739896956476437 81246503519057669834833)
                      ·
                        rfl

theorem cell23_158227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_158227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158227 prefixEnd_158227 := by exact prefixLift 158227
  have htrace : WordTrace (prefixWord ++ tailWord_158227) baseStart_158227 baseEnd_158227 := by
    simpa [prefixWord, tailWord_158227, baseEnd_158227] using wordTrace_append hprefix tailTrace_158227
  have hstable : (prefixWord ++ tailWord_158227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158227).length < 2 ^ (prefixWord ++ tailWord_158227).sum := by decide
  have hdescent : baseEnd_158227 < baseStart_158227 := by decide
  rcases family_descends (prefixWord ++ tailWord_158227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158228 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_158228 : Nat := 118140960795 + 158228 * 2 ^ 59
def prefixEnd_158228 : Nat := 4983230072969 + 3 ^ 40 * 158228 * 2
def baseEnd_158228 : Nat := 27082338999904055307443

theorem tailTrace_158228 : CollatzResearch.WordTrace tailWord_158228 prefixEnd_158228 27082338999904055307443 := by
  unfold tailWord_158228
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885524635387227018041669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3847366180516302690722225 2885524635387227018041669)
  ·
    refine ⟨541035869135105065882813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2885524635387227018041669 541035869135105065882813)
    ·
      refine ⟨202888450925664399706055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 541035869135105065882813 202888450925664399706055)
      ·
        refine ⟨304332676388496599559083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202888450925664399706055 304332676388496599559083)
        ·
          refine ⟨456499014582744899338625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304332676388496599559083 456499014582744899338625)
          ·
            refine ⟨342374260937058674503969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456499014582744899338625 342374260937058674503969)
            ·
              refine ⟨256780695702794005877977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342374260937058674503969 256780695702794005877977)
              ·
                refine ⟨192585521777095504408483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256780695702794005877977 192585521777095504408483)
                ·
                  refine ⟨288878282665643256612725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192585521777095504408483 288878282665643256612725)
                  ·
                    refine ⟨27082338999904055307443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 288878282665643256612725 27082338999904055307443)
                    ·
                      rfl

theorem cell23_158228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_158228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158228 prefixEnd_158228 := by exact prefixLift 158228
  have htrace : WordTrace (prefixWord ++ tailWord_158228) baseStart_158228 baseEnd_158228 := by
    simpa [prefixWord, tailWord_158228, baseEnd_158228] using wordTrace_append hprefix tailTrace_158228
  have hstable : (prefixWord ++ tailWord_158228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158228).length < 2 ^ (prefixWord ++ tailWord_158228).sum := by decide
  have hdescent : baseEnd_158228 < baseStart_158228 := by decide
  rcases family_descends (prefixWord ++ tailWord_158228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158234 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3]
def baseStart_158234 : Nat := 118140960795 + 158234 * 2 ^ 59
def prefixEnd_158234 : Nat := 4983230072969 + 3 ^ 40 * 158234 * 2
def baseEnd_158234 : Nat := 81250097883639142447301

theorem tailTrace_158234 : CollatzResearch.WordTrace tailWord_158234 prefixEnd_158234 81250097883639142447301 := by
  unfold tailWord_158234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1442817027188179265200439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3847512072501811373867837 1442817027188179265200439)
  ·
    refine ⟨2164225540782268897800659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1442817027188179265200439 2164225540782268897800659)
    ·
      refine ⟨3246338311173403346700989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2164225540782268897800659 3246338311173403346700989)
      ·
        refine ⟨1217376866690026255012871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3246338311173403346700989 1217376866690026255012871)
        ·
          refine ⟨1826065300035039382519307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217376866690026255012871 1826065300035039382519307)
          ·
            refine ⟨2739097950052559073778961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826065300035039382519307 2739097950052559073778961)
            ·
              refine ⟨2054323462539419305334221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2739097950052559073778961 2054323462539419305334221)
              ·
                refine ⟨770371298452282239500333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2054323462539419305334221 770371298452282239500333)
                ·
                  refine ⟨288889236919605839812625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770371298452282239500333 288889236919605839812625)
                  ·
                    refine ⟨216666927689704379859469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 288889236919605839812625 216666927689704379859469)
                    ·
                      refine ⟨81250097883639142447301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 216666927689704379859469 81250097883639142447301)
                      ·
                        rfl

theorem cell23_158234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_158234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158234 prefixEnd_158234 := by exact prefixLift 158234
  have htrace : WordTrace (prefixWord ++ tailWord_158234) baseStart_158234 baseEnd_158234 := by
    simpa [prefixWord, tailWord_158234, baseEnd_158234] using wordTrace_append hprefix tailTrace_158234
  have hstable : (prefixWord ++ tailWord_158234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158234).length < 2 ^ (prefixWord ++ tailWord_158234).sum := by decide
  have hdescent : baseEnd_158234 < baseStart_158234 := by decide
  rcases family_descends (prefixWord ++ tailWord_158234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158285 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_158285 : Nat := 118140960795 + 158285 * 2 ^ 59
def prefixEnd_158285 : Nat := 4983230072969 + 3 ^ 40 * 158285 * 2
def baseEnd_158285 : Nat := 81276285397018442909567

theorem tailTrace_158285 : CollatzResearch.WordTrace tailWord_158285 prefixEnd_158285 81276285397018442909567 := by
  unfold tailWord_158285
  simp only [CollatzResearch.WordTrace]
  refine ⟨5773128231567952770908309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3848752154378635180605539 5773128231567952770908309)
  ·
    refine ⟨270615385854747786136327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5773128231567952770908309 270615385854747786136327)
    ·
      refine ⟨405923078782121679204491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270615385854747786136327 405923078782121679204491)
      ·
        refine ⟨608884618173182518806737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405923078782121679204491 608884618173182518806737)
        ·
          refine ⟨456663463629886889105053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608884618173182518806737 456663463629886889105053)
          ·
            refine ⟨171248798861207583414395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 456663463629886889105053 171248798861207583414395)
            ·
              refine ⟨256873198291811375121593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171248798861207583414395 256873198291811375121593)
              ·
                refine ⟨192654898718858531341195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256873198291811375121593 192654898718858531341195)
                ·
                  refine ⟨288982348078287797011793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192654898718858531341195 288982348078287797011793)
                  ·
                    refine ⟨216736761058715847758845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 288982348078287797011793 216736761058715847758845)
                    ·
                      refine ⟨81276285397018442909567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 216736761058715847758845 81276285397018442909567)
                      ·
                        rfl

theorem cell23_158285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_158285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158285 prefixEnd_158285 := by exact prefixLift 158285
  have htrace : WordTrace (prefixWord ++ tailWord_158285) baseStart_158285 baseEnd_158285 := by
    simpa [prefixWord, tailWord_158285, baseEnd_158285] using wordTrace_append hprefix tailTrace_158285
  have hstable : (prefixWord ++ tailWord_158285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158285).length < 2 ^ (prefixWord ++ tailWord_158285).sum := by decide
  have hdescent : baseEnd_158285 < baseStart_158285 := by decide
  rcases family_descends (prefixWord ++ tailWord_158285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158297 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 6, 6]
def baseStart_158297 : Nat := 118140960795 + 158297 * 2 ^ 59
def prefixEnd_158297 : Nat := 4983230072969 + 3 ^ 40 * 158297 * 2
def baseEnd_158297 : Nat := 27094149054957465319837

theorem tailTrace_158297 : CollatzResearch.WordTrace tailWord_158297 prefixEnd_158297 27094149054957465319837 := by
  unfold tailWord_158297
  simp only [CollatzResearch.WordTrace]
  refine ⟨5773565907524478820345145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3849043938349652546896763 5773565907524478820345145)
  ·
    refine ⟨4330174430643359115258859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5773565907524478820345145 4330174430643359115258859)
    ·
      refine ⟨6495261645965038672888289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4330174430643359115258859 6495261645965038672888289)
      ·
        refine ⟨4871446234473779004666217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6495261645965038672888289 4871446234473779004666217)
        ·
          refine ⟨3653584675855334253499663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4871446234473779004666217 3653584675855334253499663)
          ·
            refine ⟨5480377013783001380249495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653584675855334253499663 5480377013783001380249495)
            ·
              refine ⟨8220565520674502070374243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5480377013783001380249495 8220565520674502070374243)
              ·
                refine ⟨12330848281011753105561365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8220565520674502070374243 12330848281011753105561365)
                ·
                  refine ⟨578008513172425926823189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12330848281011753105561365 578008513172425926823189)
                  ·
                    refine ⟨27094149054957465319837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 578008513172425926823189 27094149054957465319837)
                    ·
                      rfl

theorem cell23_158297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_158297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158297 prefixEnd_158297 := by exact prefixLift 158297
  have htrace : WordTrace (prefixWord ++ tailWord_158297) baseStart_158297 baseEnd_158297 := by
    simpa [prefixWord, tailWord_158297, baseEnd_158297] using wordTrace_append hprefix tailTrace_158297
  have hstable : (prefixWord ++ tailWord_158297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158297).length < 2 ^ (prefixWord ++ tailWord_158297).sum := by decide
  have hdescent : baseEnd_158297 < baseStart_158297 := by decide
  rcases family_descends (prefixWord ++ tailWord_158297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158302 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_158302 : Nat := 118140960795 + 158302 * 2 ^ 59
def prefixEnd_158302 : Nat := 4983230072969 + 3 ^ 40 * 158302 * 2
def baseEnd_158302 : Nat := 81285014568144876396989

theorem tailTrace_158302 : CollatzResearch.WordTrace tailWord_158302 prefixEnd_158302 81285014568144876396989 := by
  unfold tailWord_158302
  simp only [CollatzResearch.WordTrace]
  refine ⟨721718534063295584284645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3849165515004243116184773 721718534063295584284645)
  ·
    refine ⟨135322225136867922053371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 721718534063295584284645 135322225136867922053371)
    ·
      refine ⟨202983337705301883080057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135322225136867922053371 202983337705301883080057)
      ·
        refine ⟨152237503278976412310043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202983337705301883080057 152237503278976412310043)
        ·
          refine ⟨228356254918464618465065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152237503278976412310043 228356254918464618465065)
          ·
            refine ⟨171267191188848463848799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228356254918464618465065 171267191188848463848799)
            ·
              refine ⟨256900786783272695773199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171267191188848463848799 256900786783272695773199)
              ·
                refine ⟨385351180174909043659799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256900786783272695773199 385351180174909043659799)
                ·
                  refine ⟨578026770262363565489699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385351180174909043659799 578026770262363565489699)
                  ·
                    refine ⟨867040155393545348234549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 578026770262363565489699 867040155393545348234549)
                    ·
                      refine ⟨81285014568144876396989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 867040155393545348234549 81285014568144876396989)
                      ·
                        rfl

theorem cell23_158302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_158302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158302 prefixEnd_158302 := by exact prefixLift 158302
  have htrace : WordTrace (prefixWord ++ tailWord_158302) baseStart_158302 baseEnd_158302 := by
    simpa [prefixWord, tailWord_158302, baseEnd_158302] using wordTrace_append hprefix tailTrace_158302
  have hstable : (prefixWord ++ tailWord_158302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158302).length < 2 ^ (prefixWord ++ tailWord_158302).sum := by decide
  have hdescent : baseEnd_158302 < baseStart_158302 := by decide
  rcases family_descends (prefixWord ++ tailWord_158302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158314 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_158314 : Nat := 118140960795 + 158314 * 2 ^ 59
def prefixEnd_158314 : Nat := 4983230072969 + 3 ^ 40 * 158314 * 2
def baseEnd_158314 : Nat := 27097058778666276482311

theorem tailTrace_158314 : CollatzResearch.WordTrace tailWord_158314 prefixEnd_158314 27097058778666276482311 := by
  unfold tailWord_158314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1443546487115722680928499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3849457298975260482475997 1443546487115722680928499)
  ·
    refine ⟨2165319730673584021392749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1443546487115722680928499 2165319730673584021392749)
    ·
      refine ⟨811994899002594008022281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2165319730673584021392749 811994899002594008022281)
      ·
        refine ⟨608996174251945506016711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 811994899002594008022281 608996174251945506016711)
        ·
          refine ⟨913494261377918259025067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608996174251945506016711 913494261377918259025067)
          ·
            refine ⟨1370241392066877388537601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913494261377918259025067 1370241392066877388537601)
            ·
              refine ⟨1027681044050158041403201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370241392066877388537601 1027681044050158041403201)
              ·
                refine ⟨770760783037618531052401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1027681044050158041403201 770760783037618531052401)
                ·
                  refine ⟨578070587278213898289301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 770760783037618531052401 578070587278213898289301)
                  ·
                    refine ⟨27097058778666276482311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 578070587278213898289301 27097058778666276482311)
                    ·
                      rfl

theorem cell23_158314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_158314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158314 prefixEnd_158314 := by exact prefixLift 158314
  have htrace : WordTrace (prefixWord ++ tailWord_158314) baseStart_158314 baseEnd_158314 := by
    simpa [prefixWord, tailWord_158314, baseEnd_158314] using wordTrace_append hprefix tailTrace_158314
  have hstable : (prefixWord ++ tailWord_158314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158314).length < 2 ^ (prefixWord ++ tailWord_158314).sum := by decide
  have hdescent : baseEnd_158314 < baseStart_158314 := by decide
  rcases family_descends (prefixWord ++ tailWord_158314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158361 : List Nat := [1, 2, 1, 2, 1, 2, 6, 3, 5]
def baseStart_158361 : Nat := 118140960795 + 158361 * 2 ^ 59
def prefixEnd_158361 : Nat := 4983230072969 + 3 ^ 40 * 158361 * 2
def baseEnd_158361 : Nat := 9035034436306682839913

theorem tailTrace_158361 : CollatzResearch.WordTrace tailWord_158361 prefixEnd_158361 9035034436306682839913 := by
  unfold tailWord_158361
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775900179292617750674937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3850600119528411833783291 5775900179292617750674937)
  ·
    refine ⟨4331925134469463313006203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5775900179292617750674937 4331925134469463313006203)
    ·
      refine ⟨6497887701704194969509305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4331925134469463313006203 6497887701704194969509305)
      ·
        refine ⟨4873415776278146227131979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6497887701704194969509305 4873415776278146227131979)
        ·
          refine ⟨7310123664417219340697969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873415776278146227131979 7310123664417219340697969)
          ·
            refine ⟨5482592748312914505523477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7310123664417219340697969 5482592748312914505523477)
            ·
              refine ⟨256996535077167867446413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5482592748312914505523477 256996535077167867446413)
              ·
                refine ⟨96373700653937950292405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256996535077167867446413 96373700653937950292405)
                ·
                  refine ⟨9035034436306682839913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96373700653937950292405 9035034436306682839913)
                  ·
                    rfl

theorem cell23_158361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 5].length) (baseStart_158361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158361 prefixEnd_158361 := by exact prefixLift 158361
  have htrace : WordTrace (prefixWord ++ tailWord_158361) baseStart_158361 baseEnd_158361 := by
    simpa [prefixWord, tailWord_158361, baseEnd_158361] using wordTrace_append hprefix tailTrace_158361
  have hstable : (prefixWord ++ tailWord_158361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158361).length < 2 ^ (prefixWord ++ tailWord_158361).sum := by decide
  have hdescent : baseEnd_158361 < baseStart_158361 := by decide
  rcases family_descends (prefixWord ++ tailWord_158361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158394 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_158394 : Nat := 118140960795 + 158394 * 2 ^ 59
def prefixEnd_158394 : Nat := 4983230072969 + 3 ^ 40 * 158394 * 2
def baseEnd_158394 : Nat := 81332254788358516446565

theorem tailTrace_158394 : CollatzResearch.WordTrace tailWord_158394 prefixEnd_158394 81332254788358516446565 := by
  unfold tailWord_158394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444275947043266096656559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3851402525448709591084157 1444275947043266096656559)
  ·
    refine ⟨2166413920564899144984839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1444275947043266096656559 2166413920564899144984839)
    ·
      refine ⟨3249620880847348717477259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166413920564899144984839 3249620880847348717477259)
      ·
        refine ⟨4874431321271023076215889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3249620880847348717477259 4874431321271023076215889)
        ·
          refine ⟨3655823490953267307161917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4874431321271023076215889 3655823490953267307161917)
          ·
            refine ⟨1370933809107475240185719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3655823490953267307161917 1370933809107475240185719)
            ·
              refine ⟨2056400713661212860278579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370933809107475240185719 2056400713661212860278579)
              ·
                refine ⟨3084601070491819290417869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056400713661212860278579 3084601070491819290417869)
                ·
                  refine ⟨1156725401434432233906701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3084601070491819290417869 1156725401434432233906701)
                  ·
                    refine ⟨433772025537912087715013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156725401434432233906701 433772025537912087715013)
                    ·
                      refine ⟨81332254788358516446565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 433772025537912087715013 81332254788358516446565)
                      ·
                        rfl

theorem cell23_158394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_158394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158394 prefixEnd_158394 := by exact prefixLift 158394
  have htrace : WordTrace (prefixWord ++ tailWord_158394) baseStart_158394 baseEnd_158394 := by
    simpa [prefixWord, tailWord_158394, baseEnd_158394] using wordTrace_append hprefix tailTrace_158394
  have hstable : (prefixWord ++ tailWord_158394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158394).length < 2 ^ (prefixWord ++ tailWord_158394).sum := by decide
  have hdescent : baseEnd_158394 < baseStart_158394 := by decide
  rcases family_descends (prefixWord ++ tailWord_158394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158428 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_158428 : Nat := 118140960795 + 158428 * 2 ^ 59
def prefixEnd_158428 : Nat := 4983230072969 + 3 ^ 40 * 158428 * 2
def baseEnd_158428 : Nat := 81349713130611383421409

theorem tailTrace_158428 : CollatzResearch.WordTrace tailWord_158428 prefixEnd_158428 81349713130611383421409 := by
  unfold tailWord_158428
  simp only [CollatzResearch.WordTrace]
  refine ⟨2889171935024944096681969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3852229246699925462242625 2889171935024944096681969)
  ·
    refine ⟨2166878951268708072511477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2889171935024944096681969 2166878951268708072511477)
    ·
      refine ⟨203144901681441381797951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2166878951268708072511477 203144901681441381797951)
      ·
        refine ⟨304717352522162072696927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203144901681441381797951 304717352522162072696927)
        ·
          refine ⟨457076028783243109045391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304717352522162072696927 457076028783243109045391)
          ·
            refine ⟨685614043174864663568087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457076028783243109045391 685614043174864663568087)
            ·
              refine ⟨1028421064762296995352131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685614043174864663568087 1028421064762296995352131)
              ·
                refine ⟨1542631597143445493028197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028421064762296995352131 1542631597143445493028197)
                ·
                  refine ⟨289243424464396029942787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542631597143445493028197 289243424464396029942787)
                  ·
                    refine ⟨433865136696594044914181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 289243424464396029942787 433865136696594044914181)
                    ·
                      refine ⟨81349713130611383421409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 433865136696594044914181 81349713130611383421409)
                      ·
                        rfl

theorem cell23_158428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_158428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158428 prefixEnd_158428 := by exact prefixLift 158428
  have htrace : WordTrace (prefixWord ++ tailWord_158428) baseStart_158428 baseEnd_158428 := by
    simpa [prefixWord, tailWord_158428, baseEnd_158428] using wordTrace_append hprefix tailTrace_158428
  have hstable : (prefixWord ++ tailWord_158428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158428).length < 2 ^ (prefixWord ++ tailWord_158428).sum := by decide
  have hdescent : baseEnd_158428 < baseStart_158428 := by decide
  rcases family_descends (prefixWord ++ tailWord_158428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158431 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 3]
def baseStart_158431 : Nat := 118140960795 + 158431 * 2 ^ 59
def prefixEnd_158431 : Nat := 4983230072969 + 3 ^ 40 * 158431 * 2
def baseEnd_158431 : Nat := 81351253572574871683895

theorem tailTrace_158431 : CollatzResearch.WordTrace tailWord_158431 prefixEnd_158431 81351253572574871683895 := by
  unfold tailWord_158431
  simp only [CollatzResearch.WordTrace]
  refine ⟨5778453289039019705723147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3852302192692679803815431 5778453289039019705723147)
  ·
    refine ⟨8667679933558529558584721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5778453289039019705723147 8667679933558529558584721)
    ·
      refine ⟨6500759950168897168938541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8667679933558529558584721 6500759950168897168938541)
      ·
        refine ⟨2437784981313336438351953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6500759950168897168938541 2437784981313336438351953)
        ·
          refine ⟨1828338735985002328763965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2437784981313336438351953 1828338735985002328763965)
          ·
            refine ⟨685627025994375873286487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1828338735985002328763965 685627025994375873286487)
            ·
              refine ⟨1028440538991563809929731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685627025994375873286487 1028440538991563809929731)
              ·
                refine ⟨1542660808487345714894597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028440538991563809929731 1542660808487345714894597)
                ·
                  refine ⟨289248901591377321542737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542660808487345714894597 289248901591377321542737)
                  ·
                    refine ⟨216936676193532991157053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 289248901591377321542737 216936676193532991157053)
                    ·
                      refine ⟨81351253572574871683895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 216936676193532991157053 81351253572574871683895)
                      ·
                        rfl

theorem cell23_158431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_158431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158431 prefixEnd_158431 := by exact prefixLift 158431
  have htrace : WordTrace (prefixWord ++ tailWord_158431) baseStart_158431 baseEnd_158431 := by
    simpa [prefixWord, tailWord_158431, baseEnd_158431] using wordTrace_append hprefix tailTrace_158431
  have hstable : (prefixWord ++ tailWord_158431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158431).length < 2 ^ (prefixWord ++ tailWord_158431).sum := by decide
  have hdescent : baseEnd_158431 < baseStart_158431 := by decide
  rcases family_descends (prefixWord ++ tailWord_158431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158481 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 1, 5]
def baseStart_158481 : Nat := 118140960795 + 158481 * 2 ^ 59
def prefixEnd_158481 : Nat := 4983230072969 + 3 ^ 40 * 158481 * 2
def baseEnd_158481 : Nat := 27125642535099892019555

theorem tailTrace_158481 : CollatzResearch.WordTrace tailWord_158481 prefixEnd_158481 27125642535099892019555 := by
  unfold tailWord_158481
  simp only [CollatzResearch.WordTrace]
  refine ⟨5780276938857878245043297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3853517959238585496695531 5780276938857878245043297)
  ·
    refine ⟨4335207704143408683782473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5780276938857878245043297 4335207704143408683782473)
    ·
      refine ⟨3251405778107556512836855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4335207704143408683782473 3251405778107556512836855)
      ·
        refine ⟨4877108667161334769255283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3251405778107556512836855 4877108667161334769255283)
        ·
          refine ⟨7315663000742002153882925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4877108667161334769255283 7315663000742002153882925)
          ·
            refine ⟨2743373625278250807706097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7315663000742002153882925 2743373625278250807706097)
            ·
              refine ⟨2057530218958688105779573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2743373625278250807706097 2057530218958688105779573)
              ·
                refine ⟨192893458027377009916835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2057530218958688105779573 192893458027377009916835)
                ·
                  refine ⟨289340187041065514875253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192893458027377009916835 289340187041065514875253)
                  ·
                    refine ⟨27125642535099892019555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 289340187041065514875253 27125642535099892019555)
                    ·
                      rfl

theorem cell23_158481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_158481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158481 prefixEnd_158481 := by exact prefixLift 158481
  have htrace : WordTrace (prefixWord ++ tailWord_158481) baseStart_158481 baseEnd_158481 := by
    simpa [prefixWord, tailWord_158481, baseEnd_158481] using wordTrace_append hprefix tailTrace_158481
  have hstable : (prefixWord ++ tailWord_158481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158481).length < 2 ^ (prefixWord ++ tailWord_158481).sum := by decide
  have hdescent : baseEnd_158481 < baseStart_158481 := by decide
  rcases family_descends (prefixWord ++ tailWord_158481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158501 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_158501 : Nat := 118140960795 + 158501 * 2 ^ 59
def prefixEnd_158501 : Nat := 4983230072969 + 3 ^ 40 * 158501 * 2
def baseEnd_158501 : Nat := 81387197218389597808573

theorem tailTrace_158501 : CollatzResearch.WordTrace tailWord_158501 prefixEnd_158501 81387197218389597808573 := by
  unfold tailWord_158501
  simp only [CollatzResearch.WordTrace]
  refine ⟨5781006398785421660771357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3854004265856947773847571 5781006398785421660771357)
  ·
    refine ⟨2167877399544533122789259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5781006398785421660771357 2167877399544533122789259)
    ·
      refine ⟨3251816099316799684183889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2167877399544533122789259 3251816099316799684183889)
      ·
        refine ⟨2438862074487599763137917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3251816099316799684183889 2438862074487599763137917)
        ·
          refine ⟨914573277932849911176719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2438862074487599763137917 914573277932849911176719)
          ·
            refine ⟨1371859916899274866765079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914573277932849911176719 1371859916899274866765079)
            ·
              refine ⟨2057789875348912300147619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371859916899274866765079 2057789875348912300147619)
              ·
                refine ⟨3086684813023368450221429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057789875348912300147619 3086684813023368450221429)
                ·
                  refine ⟨289376701220940792208259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3086684813023368450221429 289376701220940792208259)
                  ·
                    refine ⟨434065051831411188312389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 289376701220940792208259 434065051831411188312389)
                    ·
                      refine ⟨81387197218389597808573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 434065051831411188312389 81387197218389597808573)
                      ·
                        rfl

theorem cell23_158501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_158501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158501 prefixEnd_158501 := by exact prefixLift 158501
  have htrace : WordTrace (prefixWord ++ tailWord_158501) baseStart_158501 baseEnd_158501 := by
    simpa [prefixWord, tailWord_158501, baseEnd_158501] using wordTrace_append hprefix tailTrace_158501
  have hstable : (prefixWord ++ tailWord_158501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158501).length < 2 ^ (prefixWord ++ tailWord_158501).sum := by decide
  have hdescent : baseEnd_158501 < baseStart_158501 := by decide
  rcases family_descends (prefixWord ++ tailWord_158501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158522 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2]
def baseStart_158522 : Nat := 118140960795 + 158522 * 2 ^ 59
def prefixEnd_158522 : Nat := 4983230072969 + 3 ^ 40 * 158522 * 2
def baseEnd_158522 : Nat := 81397980312134015645977

theorem tailTrace_158522 : CollatzResearch.WordTrace tailWord_158522 prefixEnd_158522 81397980312134015645977 := by
  unfold tailWord_158522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1445443082927335561821455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3854514887806228164857213 1445443082927335561821455)
  ·
    refine ⟨2168164624391003342732183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1445443082927335561821455 2168164624391003342732183)
    ·
      refine ⟨3252246936586505014098275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2168164624391003342732183 3252246936586505014098275)
      ·
        refine ⟨4878370404879757521147413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252246936586505014098275 4878370404879757521147413)
        ·
          refine ⟨228673612728738633803785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4878370404879757521147413 228673612728738633803785)
          ·
            refine ⟨171505209546553975352839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228673612728738633803785 171505209546553975352839)
            ·
              refine ⟨257257814319830963029259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171505209546553975352839 257257814319830963029259)
              ·
                refine ⟨385886721479746444543889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257257814319830963029259 385886721479746444543889)
                ·
                  refine ⟨289415041109809833407917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385886721479746444543889 289415041109809833407917)
                  ·
                    refine ⟨108530640416178687527969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 289415041109809833407917 108530640416178687527969)
                    ·
                      refine ⟨81397980312134015645977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 108530640416178687527969 81397980312134015645977)
                      ·
                        rfl

theorem cell23_158522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2].length) (baseStart_158522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158522 prefixEnd_158522 := by exact prefixLift 158522
  have htrace : WordTrace (prefixWord ++ tailWord_158522) baseStart_158522 baseEnd_158522 := by
    simpa [prefixWord, tailWord_158522, baseEnd_158522] using wordTrace_append hprefix tailTrace_158522
  have hstable : (prefixWord ++ tailWord_158522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158522).length < 2 ^ (prefixWord ++ tailWord_158522).sum := by decide
  have hdescent : baseEnd_158522 < baseStart_158522 := by decide
  rcases family_descends (prefixWord ++ tailWord_158522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158531 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 4]
def baseStart_158531 : Nat := 118140960795 + 158531 * 2 ^ 59
def prefixEnd_158531 : Nat := 4983230072969 + 3 ^ 40 * 158531 * 2
def baseEnd_158531 : Nat := 81402601638024480433435

theorem tailTrace_158531 : CollatzResearch.WordTrace tailWord_158531 prefixEnd_158531 81402601638024480433435 := by
  unfold tailWord_158531
  simp only [CollatzResearch.WordTrace]
  refine ⟨5782100588676736784363447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3854733725784491189575631 5782100588676736784363447)
  ·
    refine ⟨8673150883015105176545171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5782100588676736784363447 8673150883015105176545171)
    ·
      refine ⟨13009726324522657764817757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8673150883015105176545171 13009726324522657764817757)
      ·
        refine ⟨4878647371695996661806659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13009726324522657764817757 4878647371695996661806659)
        ·
          refine ⟨7317971057543994992709989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878647371695996661806659 7317971057543994992709989)
          ·
            refine ⟨1372119573289499061133123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7317971057543994992709989 1372119573289499061133123)
            ·
              refine ⟨2058179359934248591699685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372119573289499061133123 2058179359934248591699685)
              ·
                refine ⟨385908629987671610943691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2058179359934248591699685 385908629987671610943691)
                ·
                  refine ⟨578862944981507416415537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385908629987671610943691 578862944981507416415537)
                  ·
                    refine ⟨434147208736130562311653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 578862944981507416415537 434147208736130562311653)
                    ·
                      refine ⟨81402601638024480433435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 434147208736130562311653 81402601638024480433435)
                      ·
                        rfl

theorem cell23_158531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_158531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158531 prefixEnd_158531 := by exact prefixLift 158531
  have htrace : WordTrace (prefixWord ++ tailWord_158531) baseStart_158531 baseEnd_158531 := by
    simpa [prefixWord, tailWord_158531, baseEnd_158531] using wordTrace_append hprefix tailTrace_158531
  have hstable : (prefixWord ++ tailWord_158531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158531).length < 2 ^ (prefixWord ++ tailWord_158531).sum := by decide
  have hdescent : baseEnd_158531 < baseStart_158531 := by decide
  rcases family_descends (prefixWord ++ tailWord_158531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158532 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_158532 : Nat := 118140960795 + 158532 * 2 ^ 59
def prefixEnd_158532 : Nat := 4983230072969 + 3 ^ 40 * 158532 * 2
def baseEnd_158532 : Nat := 27134371706226325506977

theorem tailTrace_158532 : CollatzResearch.WordTrace tailWord_158532 prefixEnd_158532 27134371706226325506977 := by
  unfold tailWord_158532
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891068530836556977574925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3854758041115409303433233 2891068530836556977574925)
  ·
    refine ⟨1084150699063708866590597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2891068530836556977574925 1084150699063708866590597)
    ·
      refine ⟨203278256074445412485737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1084150699063708866590597 203278256074445412485737)
      ·
        refine ⟨152458692055834059364303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203278256074445412485737 152458692055834059364303)
        ·
          refine ⟨228688038083751089046455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152458692055834059364303 228688038083751089046455)
          ·
            refine ⟨343032057125626633569683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228688038083751089046455 343032057125626633569683)
            ·
              refine ⟨514548085688439950354525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343032057125626633569683 514548085688439950354525)
              ·
                refine ⟨192955532133164981382947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 514548085688439950354525 192955532133164981382947)
                ·
                  refine ⟨289433298199747472074421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192955532133164981382947 289433298199747472074421)
                  ·
                    refine ⟨27134371706226325506977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 289433298199747472074421 27134371706226325506977)
                    ·
                      rfl

theorem cell23_158532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_158532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158532 prefixEnd_158532 := by exact prefixLift 158532
  have htrace : WordTrace (prefixWord ++ tailWord_158532) baseStart_158532 baseEnd_158532 := by
    simpa [prefixWord, tailWord_158532, baseEnd_158532] using wordTrace_append hprefix tailTrace_158532
  have hstable : (prefixWord ++ tailWord_158532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158532).length < 2 ^ (prefixWord ++ tailWord_158532).sum := by decide
  have hdescent : baseEnd_158532 < baseStart_158532 := by decide
  rcases family_descends (prefixWord ++ tailWord_158532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158562 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_158562 : Nat := 118140960795 + 158562 * 2 ^ 59
def prefixEnd_158562 : Nat := 4983230072969 + 3 ^ 40 * 158562 * 2
def baseEnd_158562 : Nat := 27139506512771286381931

theorem tailTrace_158562 : CollatzResearch.WordTrace tailWord_158562 prefixEnd_158562 27139506512771286381931 := by
  unfold tailWord_158562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1445807812891107269685485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3855487501042952719161293 1445807812891107269685485)
  ·
    refine ⟨542177929834165226132057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1445807812891107269685485 542177929834165226132057)
    ·
      refine ⟨406633447375623919599043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 542177929834165226132057 406633447375623919599043)
      ·
        refine ⟨609950171063435879398565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406633447375623919599043 609950171063435879398565)
        ·
          refine ⟨114365657074394227387231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 609950171063435879398565 114365657074394227387231)
          ·
            refine ⟨171548485611591341080847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114365657074394227387231 171548485611591341080847)
            ·
              refine ⟨257322728417387011621271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171548485611591341080847 257322728417387011621271)
              ·
                refine ⟨385984092626080517431907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257322728417387011621271 385984092626080517431907)
                ·
                  refine ⟨578976138939120776147861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385984092626080517431907 578976138939120776147861)
                  ·
                    refine ⟨27139506512771286381931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 578976138939120776147861 27139506512771286381931)
                    ·
                      rfl

theorem cell23_158562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_158562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158562 prefixEnd_158562 := by exact prefixLift 158562
  have htrace : WordTrace (prefixWord ++ tailWord_158562) baseStart_158562 baseEnd_158562 := by
    simpa [prefixWord, tailWord_158562, baseEnd_158562] using wordTrace_append hprefix tailTrace_158562
  have hstable : (prefixWord ++ tailWord_158562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158562).length < 2 ^ (prefixWord ++ tailWord_158562).sum := by decide
  have hdescent : baseEnd_158562 < baseStart_158562 := by decide
  rcases family_descends (prefixWord ++ tailWord_158562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158595 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 1, 3, 2]
def baseStart_158595 : Nat := 118140960795 + 158595 * 2 ^ 59
def prefixEnd_158595 : Nat := 4983230072969 + 3 ^ 40 * 158595 * 2
def baseEnd_158595 : Nat := 81435464399912230033141

theorem tailTrace_158595 : CollatzResearch.WordTrace tailWord_158595 prefixEnd_158595 81435464399912230033141 := by
  unfold tailWord_158595
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784434860444875714693239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3856289906963250476462159 5784434860444875714693239)
  ·
    refine ⟨8676652290667313572039859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5784434860444875714693239 8676652290667313572039859)
    ·
      refine ⟨13014978436000970358059789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8676652290667313572039859 13014978436000970358059789)
      ·
        refine ⟨4880616913500363884272421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13014978436000970358059789 4880616913500363884272421)
        ·
          refine ⟨915115671281318228301079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4880616913500363884272421 915115671281318228301079)
          ·
            refine ⟨1372673506921977342451619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915115671281318228301079 1372673506921977342451619)
            ·
              refine ⟨2059010260382966013677429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372673506921977342451619 2059010260382966013677429)
              ·
                refine ⟨193032211910903063782259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2059010260382966013677429 193032211910903063782259)
                ·
                  refine ⟨289548317866354595673389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193032211910903063782259 289548317866354595673389)
                  ·
                    refine ⟨108580619199882973377521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 289548317866354595673389 108580619199882973377521)
                    ·
                      refine ⟨81435464399912230033141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 108580619199882973377521 81435464399912230033141)
                      ·
                        rfl

theorem cell23_158595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 3, 2].length) (baseStart_158595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158595 prefixEnd_158595 := by exact prefixLift 158595
  have htrace : WordTrace (prefixWord ++ tailWord_158595) baseStart_158595 baseEnd_158595 := by
    simpa [prefixWord, tailWord_158595, baseEnd_158595] using wordTrace_append hprefix tailTrace_158595
  have hstable : (prefixWord ++ tailWord_158595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158595).length < 2 ^ (prefixWord ++ tailWord_158595).sum := by decide
  have hdescent : baseEnd_158595 < baseStart_158595 := by decide
  rcases family_descends (prefixWord ++ tailWord_158595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158669 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_158669 : Nat := 118140960795 + 158669 * 2 ^ 59
def prefixEnd_158669 : Nat := 4983230072969 + 3 ^ 40 * 158669 * 2
def baseEnd_158669 : Nat := 27157820656114980169267

theorem tailTrace_158669 : CollatzResearch.WordTrace tailWord_158669 prefixEnd_158669 27157820656114980169267 := by
  unfold tailWord_158669
  simp only [CollatzResearch.WordTrace]
  refine ⟨5787133862176786352887061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3858089241451190901924707 5787133862176786352887061)
  ·
    refine ⟨271271899789536860291581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5787133862176786352887061 271271899789536860291581)
    ·
      refine ⟨101726962421076322609343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271271899789536860291581 101726962421076322609343)
      ·
        refine ⟨152590443631614483914015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101726962421076322609343 152590443631614483914015)
        ·
          refine ⟨228885665447421725871023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152590443631614483914015 228885665447421725871023)
          ·
            refine ⟨343328498171132588806535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228885665447421725871023 343328498171132588806535)
            ·
              refine ⟨514992747256698883209803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343328498171132588806535 514992747256698883209803)
              ·
                refine ⟨772489120885048324814705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514992747256698883209803 772489120885048324814705)
                ·
                  refine ⟨579366840663786243611029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 772489120885048324814705 579366840663786243611029)
                  ·
                    refine ⟨27157820656114980169267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 579366840663786243611029 27157820656114980169267)
                    ·
                      rfl

theorem cell23_158669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_158669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158669 prefixEnd_158669 := by exact prefixLift 158669
  have htrace : WordTrace (prefixWord ++ tailWord_158669) baseStart_158669 baseEnd_158669 := by
    simpa [prefixWord, tailWord_158669, baseEnd_158669] using wordTrace_append hprefix tailTrace_158669
  have hstable : (prefixWord ++ tailWord_158669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158669).length < 2 ^ (prefixWord ++ tailWord_158669).sum := by decide
  have hdescent : baseEnd_158669 < baseStart_158669 := by decide
  rcases family_descends (prefixWord ++ tailWord_158669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158695 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 2, 5]
def baseStart_158695 : Nat := 118140960795 + 158695 * 2 ^ 59
def prefixEnd_158695 : Nat := 4983230072969 + 3 ^ 40 * 158695 * 2
def baseEnd_158695 : Nat := 27162270821787279594227

theorem tailTrace_158695 : CollatzResearch.WordTrace tailWord_158695 prefixEnd_158695 27162270821787279594227 := by
  unfold tailWord_158695
  simp only [CollatzResearch.WordTrace]
  refine ⟨5788082160082592793333539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3858721440055061862222359 5788082160082592793333539)
  ·
    refine ⟨8682123240123889190000309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5788082160082592793333539 8682123240123889190000309)
    ·
      refine ⟨813949053761614611562529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8682123240123889190000309 813949053761614611562529)
      ·
        refine ⟨610461790321210958671897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 813949053761614611562529 610461790321210958671897)
        ·
          refine ⟨457846342740908219003923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 610461790321210958671897 457846342740908219003923)
          ·
            refine ⟨686769514111362328505885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457846342740908219003923 686769514111362328505885)
            ·
              refine ⟨257538567791760873189707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 686769514111362328505885 257538567791760873189707)
              ·
                refine ⟨386307851687641309784561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257538567791760873189707 386307851687641309784561)
                ·
                  refine ⟨289730888765730982338421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386307851687641309784561 289730888765730982338421)
                  ·
                    refine ⟨27162270821787279594227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 289730888765730982338421 27162270821787279594227)
                    ·
                      rfl

theorem cell23_158695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_158695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158695 prefixEnd_158695 := by exact prefixLift 158695
  have htrace : WordTrace (prefixWord ++ tailWord_158695) baseStart_158695 baseEnd_158695 := by
    simpa [prefixWord, tailWord_158695, baseEnd_158695] using wordTrace_append hprefix tailTrace_158695
  have hstable : (prefixWord ++ tailWord_158695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158695).length < 2 ^ (prefixWord ++ tailWord_158695).sum := by decide
  have hdescent : baseEnd_158695 < baseStart_158695 := by decide
  rcases family_descends (prefixWord ++ tailWord_158695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158725 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 3, 4]
def baseStart_158725 : Nat := 118140960795 + 158725 * 2 ^ 59
def prefixEnd_158725 : Nat := 4983230072969 + 3 ^ 40 * 158725 * 2
def baseEnd_158725 : Nat := 27167405628332240469181

theorem tailTrace_158725 : CollatzResearch.WordTrace tailWord_158725 prefixEnd_158725 27167405628332240469181 := by
  unfold tailWord_158725
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789176349973907916925629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3859450899982605277950419 5789176349973907916925629)
  ·
    refine ⟨2170941131240215468847111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5789176349973907916925629 2170941131240215468847111)
    ·
      refine ⟨3256411696860323203270667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2170941131240215468847111 3256411696860323203270667)
      ·
        refine ⟨4884617545290484804906001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3256411696860323203270667 4884617545290484804906001)
        ·
          refine ⟨3663463158967863603679501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4884617545290484804906001 3663463158967863603679501)
          ·
            refine ⟨1373798684612948851379813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3663463158967863603679501 1373798684612948851379813)
            ·
              refine ⟨257587253364927909633715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1373798684612948851379813 257587253364927909633715)
              ·
                refine ⟨386380880047391864450573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257587253364927909633715 386380880047391864450573)
                ·
                  refine ⟨144892830017771949168965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386380880047391864450573 144892830017771949168965)
                  ·
                    refine ⟨27167405628332240469181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144892830017771949168965 27167405628332240469181)
                    ·
                      rfl

theorem cell23_158725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_158725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158725 prefixEnd_158725 := by exact prefixLift 158725
  have htrace : WordTrace (prefixWord ++ tailWord_158725) baseStart_158725 baseEnd_158725 := by
    simpa [prefixWord, tailWord_158725, baseEnd_158725] using wordTrace_append hprefix tailTrace_158725
  have hstable : (prefixWord ++ tailWord_158725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158725).length < 2 ^ (prefixWord ++ tailWord_158725).sum := by decide
  have hdescent : baseEnd_158725 < baseStart_158725 := by decide
  rcases family_descends (prefixWord ++ tailWord_158725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158802 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_158802 : Nat := 118140960795 + 158802 * 2 ^ 59
def prefixEnd_158802 : Nat := 4983230072969 + 3 ^ 40 * 158802 * 2
def baseEnd_158802 : Nat := 27180584965130973381563

theorem tailTrace_158802 : CollatzResearch.WordTrace tailWord_158802 prefixEnd_158802 27180584965130973381563 := by
  unfold tailWord_158802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1447996192673737516869665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3861323180463300044985773 1447996192673737516869665)
  ·
    refine ⟨1085997144505303137652249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1447996192673737516869665 1085997144505303137652249)
    ·
      refine ⟨814497858378977353239187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1085997144505303137652249 814497858378977353239187)
      ·
        refine ⟨1221746787568466029858781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814497858378977353239187 1221746787568466029858781)
        ·
          refine ⟨458155045338174761197043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1221746787568466029858781 458155045338174761197043)
          ·
            refine ⟨687232568007262141795565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458155045338174761197043 687232568007262141795565)
            ·
              refine ⟨257712213002723303173337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 687232568007262141795565 257712213002723303173337)
              ·
                refine ⟨193284159752042477380003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257712213002723303173337 193284159752042477380003)
                ·
                  refine ⟨289926239628063716070005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193284159752042477380003 289926239628063716070005)
                  ·
                    refine ⟨27180584965130973381563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 289926239628063716070005 27180584965130973381563)
                    ·
                      rfl

theorem cell23_158802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_158802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158802 prefixEnd_158802 := by exact prefixLift 158802
  have htrace : WordTrace (prefixWord ++ tailWord_158802) baseStart_158802 baseEnd_158802 := by
    simpa [prefixWord, tailWord_158802, baseEnd_158802] using wordTrace_append hprefix tailTrace_158802
  have hstable : (prefixWord ++ tailWord_158802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158802).length < 2 ^ (prefixWord ++ tailWord_158802).sum := by decide
  have hdescent : baseEnd_158802 < baseStart_158802 := by decide
  rcases family_descends (prefixWord ++ tailWord_158802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158805 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_158805 : Nat := 118140960795 + 158805 * 2 ^ 59
def prefixEnd_158805 : Nat := 4983230072969 + 3 ^ 40 * 158805 * 2
def baseEnd_158805 : Nat := 81543295337356408407175

theorem tailTrace_158805 : CollatzResearch.WordTrace tailWord_158805 prefixEnd_158805 81543295337356408407175 := by
  unfold tailWord_158805
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792094189684081579837869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3861396126456054386558579 5792094189684081579837869)
  ·
    refine ⟨2172035321131530592439201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5792094189684081579837869 2172035321131530592439201)
    ·
      refine ⟨1629026490848647944329401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2172035321131530592439201 1629026490848647944329401)
      ·
        refine ⟨1221769868136485958247051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1629026490848647944329401 1221769868136485958247051)
        ·
          refine ⟨1832654802204728937370577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221769868136485958247051 1832654802204728937370577)
          ·
            refine ⟨1374491101653546703027933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1832654802204728937370577 1374491101653546703027933)
            ·
              refine ⟨515434163120080013635475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1374491101653546703027933 515434163120080013635475)
              ·
                refine ⟨773151244680120020453213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515434163120080013635475 773151244680120020453213)
                ·
                  refine ⟨289931716755045007669955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773151244680120020453213 289931716755045007669955)
                  ·
                    refine ⟨434897575132567511504933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 289931716755045007669955 434897575132567511504933)
                    ·
                      refine ⟨81543295337356408407175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 434897575132567511504933 81543295337356408407175)
                      ·
                        rfl

theorem cell23_158805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_158805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158805 prefixEnd_158805 := by exact prefixLift 158805
  have htrace : WordTrace (prefixWord ++ tailWord_158805) baseStart_158805 baseEnd_158805 := by
    simpa [prefixWord, tailWord_158805, baseEnd_158805] using wordTrace_append hprefix tailTrace_158805
  have hstable : (prefixWord ++ tailWord_158805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158805).length < 2 ^ (prefixWord ++ tailWord_158805).sum := by decide
  have hdescent : baseEnd_158805 < baseStart_158805 := by decide
  rcases family_descends (prefixWord ++ tailWord_158805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158825 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 5]
def baseStart_158825 : Nat := 118140960795 + 158825 * 2 ^ 59
def prefixEnd_158825 : Nat := 4983230072969 + 3 ^ 40 * 158825 * 2
def baseEnd_158825 : Nat := 81553564950446330157083

theorem tailTrace_158825 : CollatzResearch.WordTrace tailWord_158825 prefixEnd_158825 81553564950446330157083 := by
  unfold tailWord_158825
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792823649611624995565929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3861882433074416663710619 5792823649611624995565929)
  ·
    refine ⟨4344617737208718746674447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5792823649611624995565929 4344617737208718746674447)
    ·
      refine ⟨6516926605813078120011671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4344617737208718746674447 6516926605813078120011671)
      ·
        refine ⟨9775389908719617180017507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6516926605813078120011671 9775389908719617180017507)
        ·
          refine ⟨14663084863079425770026261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9775389908719617180017507 14663084863079425770026261)
          ·
            refine ⟨687332102956848082969981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14663084863079425770026261 687332102956848082969981)
            ·
              refine ⟨257749538608818031113743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 687332102956848082969981 257749538608818031113743)
              ·
                refine ⟨386624307913227046670615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257749538608818031113743 386624307913227046670615)
                ·
                  refine ⟨579936461869840570005923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386624307913227046670615 579936461869840570005923)
                  ·
                    refine ⟨869904692804760855008885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579936461869840570005923 869904692804760855008885)
                    ·
                      refine ⟨81553564950446330157083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 869904692804760855008885 81553564950446330157083)
                      ·
                        rfl

theorem cell23_158825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 5].length) (baseStart_158825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158825 prefixEnd_158825 := by exact prefixLift 158825
  have htrace : WordTrace (prefixWord ++ tailWord_158825) baseStart_158825 baseEnd_158825 := by
    simpa [prefixWord, tailWord_158825, baseEnd_158825] using wordTrace_append hprefix tailTrace_158825
  have hstable : (prefixWord ++ tailWord_158825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158825).length < 2 ^ (prefixWord ++ tailWord_158825).sum := by decide
  have hdescent : baseEnd_158825 < baseStart_158825 := by decide
  rcases family_descends (prefixWord ++ tailWord_158825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158832 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 2, 4]
def baseStart_158832 : Nat := 118140960795 + 158832 * 2 ^ 59
def prefixEnd_158832 : Nat := 4983230072969 + 3 ^ 40 * 158832 * 2
def baseEnd_158832 : Nat := 27185719771675934256517

theorem tailTrace_158832 : CollatzResearch.WordTrace tailWord_158832 prefixEnd_158832 27185719771675934256517 := by
  unfold tailWord_158832
  simp only [CollatzResearch.WordTrace]
  refine ⟨2896539480293132595535375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3862052640390843460713833 2896539480293132595535375)
  ·
    refine ⟨4344809220439698893303063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2896539480293132595535375 4344809220439698893303063)
    ·
      refine ⟨6517213830659548339954595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4344809220439698893303063 6517213830659548339954595)
      ·
        refine ⟨9775820745989322509931893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6517213830659548339954595 9775820745989322509931893)
        ·
          refine ⟨916483194936498985306115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9775820745989322509931893 916483194936498985306115)
          ·
            refine ⟨1374724792404748477959173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916483194936498985306115 1374724792404748477959173)
            ·
              refine ⟨257760898575890339617345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1374724792404748477959173 257760898575890339617345)
              ·
                refine ⟨193320673931917754713009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257760898575890339617345 193320673931917754713009)
                ·
                  refine ⟨144990505448938316034757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193320673931917754713009 144990505448938316034757)
                  ·
                    refine ⟨27185719771675934256517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144990505448938316034757 27185719771675934256517)
                    ·
                      rfl

theorem cell23_158832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2, 4].length) (baseStart_158832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158832 prefixEnd_158832 := by exact prefixLift 158832
  have htrace : WordTrace (prefixWord ++ tailWord_158832) baseStart_158832 baseEnd_158832 := by
    simpa [prefixWord, tailWord_158832, baseEnd_158832] using wordTrace_append hprefix tailTrace_158832
  have hstable : (prefixWord ++ tailWord_158832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158832).length < 2 ^ (prefixWord ++ tailWord_158832).sum := by decide
  have hdescent : baseEnd_158832 < baseStart_158832 := by decide
  rcases family_descends (prefixWord ++ tailWord_158832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158848 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_158848 : Nat := 118140960795 + 158848 * 2 ^ 59
def prefixEnd_158848 : Nat := 4983230072969 + 3 ^ 40 * 158848 * 2
def baseEnd_158848 : Nat := 81565375005499740169477

theorem tailTrace_158848 : CollatzResearch.WordTrace tailWord_158848 prefixEnd_158848 81565375005499740169477 := by
  unfold tailWord_158848
  simp only [CollatzResearch.WordTrace]
  refine ⟨2896831264264149961826599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3862441685685533282435465 2896831264264149961826599)
  ·
    refine ⟨4345246896396224942739899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2896831264264149961826599 4345246896396224942739899)
    ·
      refine ⟨6517870344594337414109849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4345246896396224942739899 6517870344594337414109849)
      ·
        refine ⟨4888402758445753060582387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6517870344594337414109849 4888402758445753060582387)
        ·
          refine ⟨7332604137668629590873581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4888402758445753060582387 7332604137668629590873581)
          ·
            refine ⟨2749726551625736096577593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7332604137668629590873581 2749726551625736096577593)
            ·
              refine ⟨2062294913719302072433195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2749726551625736096577593 2062294913719302072433195)
              ·
                refine ⟨3093442370578953108649793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062294913719302072433195 3093442370578953108649793)
                ·
                  refine ⟨2320081777934214831487345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3093442370578953108649793 2320081777934214831487345)
                  ·
                    refine ⟨1740061333450661123615509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2320081777934214831487345 1740061333450661123615509)
                    ·
                      refine ⟨81565375005499740169477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1740061333450661123615509 81565375005499740169477)
                      ·
                        rfl

theorem cell23_158848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_158848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158848 prefixEnd_158848 := by exact prefixLift 158848
  have htrace : WordTrace (prefixWord ++ tailWord_158848) baseStart_158848 baseEnd_158848 := by
    simpa [prefixWord, tailWord_158848, baseEnd_158848] using wordTrace_append hprefix tailTrace_158848
  have hstable : (prefixWord ++ tailWord_158848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158848).length < 2 ^ (prefixWord ++ tailWord_158848).sum := by decide
  have hdescent : baseEnd_158848 < baseStart_158848 := by decide
  rcases family_descends (prefixWord ++ tailWord_158848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158852 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_158852 : Nat := 118140960795 + 158852 * 2 ^ 59
def prefixEnd_158852 : Nat := 4983230072969 + 3 ^ 40 * 158852 * 2
def baseEnd_158852 : Nat := 81567428928117724519459

theorem tailTrace_158852 : CollatzResearch.WordTrace tailWord_158852 prefixEnd_158852 81567428928117724519459 := by
  unfold tailWord_158852
  simp only [CollatzResearch.WordTrace]
  refine ⟨2896904210256904303399405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3862538947009205737865873 2896904210256904303399405)
  ·
    refine ⟨1086339078846339113774777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2896904210256904303399405 1086339078846339113774777)
    ·
      refine ⟨814754309134754335331083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1086339078846339113774777 814754309134754335331083)
      ·
        refine ⟨1222131463702131502996625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814754309134754335331083 1222131463702131502996625)
        ·
          refine ⟨916598597776598627247469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1222131463702131502996625 916598597776598627247469)
          ·
            refine ⟨343724474166224485217801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 916598597776598627247469 343724474166224485217801)
            ·
              refine ⟨257793355624668363913351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343724474166224485217801 257793355624668363913351)
              ·
                refine ⟨386690033437002545870027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257793355624668363913351 386690033437002545870027)
                ·
                  refine ⟨580035050155503818805041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386690033437002545870027 580035050155503818805041)
                  ·
                    refine ⟨435026287616627864103781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 580035050155503818805041 435026287616627864103781)
                    ·
                      refine ⟨81567428928117724519459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 435026287616627864103781 81567428928117724519459)
                      ·
                        rfl

theorem cell23_158852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_158852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158852 prefixEnd_158852 := by exact prefixLift 158852
  have htrace : WordTrace (prefixWord ++ tailWord_158852) baseStart_158852 baseEnd_158852 := by
    simpa [prefixWord, tailWord_158852, baseEnd_158852] using wordTrace_append hprefix tailTrace_158852
  have hstable : (prefixWord ++ tailWord_158852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158852).length < 2 ^ (prefixWord ++ tailWord_158852).sum := by decide
  have hdescent : baseEnd_158852 < baseStart_158852 := by decide
  rcases family_descends (prefixWord ++ tailWord_158852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158856 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 3, 2, 2]
def baseStart_158856 : Nat := 118140960795 + 158856 * 2 ^ 59
def prefixEnd_158856 : Nat := 4983230072969 + 3 ^ 40 * 158856 * 2
def baseEnd_158856 : Nat := 81569482850735708869441

theorem tailTrace_158856 : CollatzResearch.WordTrace tailWord_158856 prefixEnd_158856 81569482850735708869441 := by
  unfold tailWord_158856
  simp only [CollatzResearch.WordTrace]
  refine ⟨2896977156249658644972211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3862636208332878193296281 2896977156249658644972211)
  ·
    refine ⟨4345465734374487967458317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2896977156249658644972211 4345465734374487967458317)
    ·
      refine ⟨1629549650390432987796869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4345465734374487967458317 1629549650390432987796869)
      ·
        refine ⟨305540559448206185211913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1629549650390432987796869 305540559448206185211913)
        ·
          refine ⟨229155419586154638908935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305540559448206185211913 229155419586154638908935)
          ·
            refine ⟨343733129379231958363403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229155419586154638908935 343733129379231958363403)
            ·
              refine ⟨515599694068847937545105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343733129379231958363403 515599694068847937545105)
              ·
                refine ⟨386699770551635953158829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515599694068847937545105 386699770551635953158829)
                ·
                  refine ⟨145012413956863482434561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386699770551635953158829 145012413956863482434561)
                  ·
                    refine ⟨108759310467647611825921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 145012413956863482434561 108759310467647611825921)
                    ·
                      refine ⟨81569482850735708869441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 108759310467647611825921 81569482850735708869441)
                      ·
                        rfl

theorem cell23_158856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_158856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158856 prefixEnd_158856 := by exact prefixLift 158856
  have htrace : WordTrace (prefixWord ++ tailWord_158856) baseStart_158856 baseEnd_158856 := by
    simpa [prefixWord, tailWord_158856, baseEnd_158856] using wordTrace_append hprefix tailTrace_158856
  have hstable : (prefixWord ++ tailWord_158856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158856).length < 2 ^ (prefixWord ++ tailWord_158856).sum := by decide
  have hdescent : baseEnd_158856 < baseStart_158856 := by decide
  rcases family_descends (prefixWord ++ tailWord_158856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158862 : List Nat := [4, 1, 1, 3, 2, 2, 3, 7]
def baseStart_158862 : Nat := 118140960795 + 158862 * 2 ^ 59
def prefixEnd_158862 : Nat := 4983230072969 + 3 ^ 40 * 158862 * 2
def baseEnd_158862 : Nat := 3021206064246766125719

theorem tailTrace_158862 : CollatzResearch.WordTrace tailWord_158862 prefixEnd_158862 3021206064246766125719 := by
  unfold tailWord_158862
  simp only [CollatzResearch.WordTrace]
  refine ⟨724271643809697539332855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3862782100318386876441893 724271643809697539332855)
  ·
    refine ⟨1086407465714546308999283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 724271643809697539332855 1086407465714546308999283)
    ·
      refine ⟨1629611198571819463498925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086407465714546308999283 1629611198571819463498925)
      ·
        refine ⟨611104199464432298812097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1629611198571819463498925 611104199464432298812097)
        ·
          refine ⟨458328149598324224109073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611104199464432298812097 458328149598324224109073)
          ·
            refine ⟨343746112198743168081805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458328149598324224109073 343746112198743168081805)
            ·
              refine ⟨128904792074528688030677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 343746112198743168081805 128904792074528688030677)
              ·
                refine ⟨3021206064246766125719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 128904792074528688030677 3021206064246766125719)
                ·
                  rfl

theorem cell23_158862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_158862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158862 prefixEnd_158862 := by exact prefixLift 158862
  have htrace : WordTrace (prefixWord ++ tailWord_158862) baseStart_158862 baseEnd_158862 := by
    simpa [prefixWord, tailWord_158862, baseEnd_158862] using wordTrace_append hprefix tailTrace_158862
  have hstable : (prefixWord ++ tailWord_158862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158862).length < 2 ^ (prefixWord ++ tailWord_158862).sum := by decide
  have hdescent : baseEnd_158862 < baseStart_158862 := by decide
  rcases family_descends (prefixWord ++ tailWord_158862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158872 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 1, 3, 3]
def baseStart_158872 : Nat := 118140960795 + 158872 * 2 ^ 59
def prefixEnd_158872 : Nat := 4983230072969 + 3 ^ 40 * 158872 * 2
def baseEnd_158872 : Nat := 81577698541207646269367

theorem tailTrace_158872 : CollatzResearch.WordTrace tailWord_158872 prefixEnd_158872 81577698541207646269367 := by
  unfold tailWord_158872
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897268940220676011263435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3863025253627568015017913 2897268940220676011263435)
  ·
    refine ⟨4345903410331014016895153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2897268940220676011263435 4345903410331014016895153)
    ·
      refine ⟨3259427557748260512671365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4345903410331014016895153 3259427557748260512671365)
      ·
        refine ⟨611142667077798846125881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3259427557748260512671365 611142667077798846125881)
        ·
          refine ⟨458357000308349134594411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611142667077798846125881 458357000308349134594411)
          ·
            refine ⟨687535500462523701891617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458357000308349134594411 687535500462523701891617)
            ·
              refine ⟨515651625346892776418713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687535500462523701891617 515651625346892776418713)
              ·
                refine ⟨386738719010169582314035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515651625346892776418713 386738719010169582314035)
                ·
                  refine ⟨580108078515254373471053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386738719010169582314035 580108078515254373471053)
                  ·
                    refine ⟨217540529443220390051645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 580108078515254373471053 217540529443220390051645)
                    ·
                      refine ⟨81577698541207646269367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 217540529443220390051645 81577698541207646269367)
                      ·
                        rfl

theorem cell23_158872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_158872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158872 prefixEnd_158872 := by exact prefixLift 158872
  have htrace : WordTrace (prefixWord ++ tailWord_158872) baseStart_158872 baseEnd_158872 := by
    simpa [prefixWord, tailWord_158872, baseEnd_158872] using wordTrace_append hprefix tailTrace_158872
  have hstable : (prefixWord ++ tailWord_158872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158872).length < 2 ^ (prefixWord ++ tailWord_158872).sum := by decide
  have hdescent : baseEnd_158872 < baseStart_158872 := by decide
  rcases family_descends (prefixWord ++ tailWord_158872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158876 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_158876 : Nat := 118140960795 + 158876 * 2 ^ 59
def prefixEnd_158876 : Nat := 4983230072969 + 3 ^ 40 * 158876 * 2
def baseEnd_158876 : Nat := 81579752463825630619349

theorem tailTrace_158876 : CollatzResearch.WordTrace tailWord_158876 prefixEnd_158876 81579752463825630619349 := by
  unfold tailWord_158876
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897341886213430352836241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3863122514951240470448321 2897341886213430352836241)
  ·
    refine ⟨2173006414660072764627181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2897341886213430352836241 2173006414660072764627181)
    ·
      refine ⟨814877405497527286735193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2173006414660072764627181 814877405497527286735193)
      ·
        refine ⟨611158054123145465051395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 814877405497527286735193 611158054123145465051395)
        ·
          refine ⟨916737081184718197577093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611158054123145465051395 916737081184718197577093)
          ·
            refine ⟨171888202722134662045705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 916737081184718197577093 171888202722134662045705)
            ·
              refine ⟨128916152041600996534279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171888202722134662045705 128916152041600996534279)
              ·
                refine ⟨193374228062401494801419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128916152041600996534279 193374228062401494801419)
                ·
                  refine ⟨290061342093602242202129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193374228062401494801419 290061342093602242202129)
                  ·
                    refine ⟨217546006570201681651597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 290061342093602242202129 217546006570201681651597)
                    ·
                      refine ⟨81579752463825630619349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 217546006570201681651597 81579752463825630619349)
                      ·
                        rfl

theorem cell23_158876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_158876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158876 prefixEnd_158876 := by exact prefixLift 158876
  have htrace : WordTrace (prefixWord ++ tailWord_158876) baseStart_158876 baseEnd_158876 := by
    simpa [prefixWord, tailWord_158876, baseEnd_158876] using wordTrace_append hprefix tailTrace_158876
  have hstable : (prefixWord ++ tailWord_158876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158876).length < 2 ^ (prefixWord ++ tailWord_158876).sum := by decide
  have hdescent : baseEnd_158876 < baseStart_158876 := by decide
  rcases family_descends (prefixWord ++ tailWord_158876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158905 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 2, 6]
def baseStart_158905 : Nat := 118140960795 + 158905 * 2 ^ 59
def prefixEnd_158905 : Nat := 4983230072969 + 3 ^ 40 * 158905 * 2
def baseEnd_158905 : Nat := 27198214467602005718905

theorem tailTrace_158905 : CollatzResearch.WordTrace tailWord_158905 prefixEnd_158905 27198214467602005718905 := by
  unfold tailWord_158905
  simp only [CollatzResearch.WordTrace]
  refine ⟨5795741489321798658478169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3863827659547865772318779 5795741489321798658478169)
  ·
    refine ⟨4346806116991348993858627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5795741489321798658478169 4346806116991348993858627)
    ·
      refine ⟨6520209175487023490787941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4346806116991348993858627 6520209175487023490787941)
      ·
        refine ⟨1222539220403816904522739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6520209175487023490787941 1222539220403816904522739)
        ·
          refine ⟨1833808830605725356784109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222539220403816904522739 1833808830605725356784109)
          ·
            refine ⟨687678311477147008794041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1833808830605725356784109 687678311477147008794041)
            ·
              refine ⟨515758733607860256595531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687678311477147008794041 515758733607860256595531)
              ·
                refine ⟨773638100411790384893297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515758733607860256595531 773638100411790384893297)
                ·
                  refine ⟨580228575308842788669973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 773638100411790384893297 580228575308842788669973)
                  ·
                    refine ⟨27198214467602005718905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 580228575308842788669973 27198214467602005718905)
                    ·
                      rfl

theorem cell23_158905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_158905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158905 prefixEnd_158905 := by exact prefixLift 158905
  have htrace : WordTrace (prefixWord ++ tailWord_158905) baseStart_158905 baseEnd_158905 := by
    simpa [prefixWord, tailWord_158905, baseEnd_158905] using wordTrace_append hprefix tailTrace_158905
  have hstable : (prefixWord ++ tailWord_158905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158905).length < 2 ^ (prefixWord ++ tailWord_158905).sum := by decide
  have hdescent : baseEnd_158905 < baseStart_158905 := by decide
  rcases family_descends (prefixWord ++ tailWord_158905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158963 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 2, 2, 2]
def baseStart_158963 : Nat := 118140960795 + 158963 * 2 ^ 59
def prefixEnd_158963 : Nat := 4983230072969 + 3 ^ 40 * 158963 * 2
def baseEnd_158963 : Nat := 81624425280766790231449

theorem tailTrace_158963 : CollatzResearch.WordTrace tailWord_158963 prefixEnd_158963 81624425280766790231449 := by
  unfold tailWord_158963
  simp only [CollatzResearch.WordTrace]
  refine ⟨5797856923111674564089543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3865237948741116376059695 5797856923111674564089543)
  ·
    refine ⟨8696785384667511846134315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5797856923111674564089543 8696785384667511846134315)
    ·
      refine ⟨13045178077001267769201473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8696785384667511846134315 13045178077001267769201473)
      ·
        refine ⟨9783883557750950826901105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13045178077001267769201473 9783883557750950826901105)
        ·
          refine ⟨7337912668313213120175829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9783883557750950826901105 7337912668313213120175829)
          ·
            refine ⟨171982328163590932504121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7337912668313213120175829 171982328163590932504121)
            ·
              refine ⟨128986746122693199378091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171982328163590932504121 128986746122693199378091)
              ·
                refine ⟨193480119184039799067137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128986746122693199378091 193480119184039799067137)
                ·
                  refine ⟨145110089388029849300353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193480119184039799067137 145110089388029849300353)
                  ·
                    refine ⟨108832567041022386975265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 145110089388029849300353 108832567041022386975265)
                    ·
                      refine ⟨81624425280766790231449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 108832567041022386975265 81624425280766790231449)
                      ·
                        rfl

theorem cell23_158963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 2, 2, 2].length) (baseStart_158963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_158963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_158963 prefixEnd_158963 := by exact prefixLift 158963
  have htrace : WordTrace (prefixWord ++ tailWord_158963) baseStart_158963 baseEnd_158963 := by
    simpa [prefixWord, tailWord_158963, baseEnd_158963] using wordTrace_append hprefix tailTrace_158963
  have hstable : (prefixWord ++ tailWord_158963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158963).length < 2 ^ (prefixWord ++ tailWord_158963).sum := by decide
  have hdescent : baseEnd_158963 < baseStart_158963 := by decide
  rcases family_descends (prefixWord ++ tailWord_158963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159029 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 3, 4]
def baseStart_159029 : Nat := 118140960795 + 159029 * 2 ^ 59
def prefixEnd_159029 : Nat := 4983230072969 + 3 ^ 40 * 159029 * 2
def baseEnd_159029 : Nat := 27219438334654510668715

theorem tailTrace_159029 : CollatzResearch.WordTrace tailWord_159029 prefixEnd_159029 27219438334654510668715 := by
  unfold tailWord_159029
  simp only [CollatzResearch.WordTrace]
  refine ⟨5800264140872567835992141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3866842760581711890661427 5800264140872567835992141)
  ·
    refine ⟨2175099052827212938497053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5800264140872567835992141 2175099052827212938497053)
    ·
      refine ⟨815662144810204851936395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2175099052827212938497053 815662144810204851936395)
      ·
        refine ⟨1223493217215307277904593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815662144810204851936395 1223493217215307277904593)
        ·
          refine ⟨917619912911480458428445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1223493217215307277904593 917619912911480458428445)
          ·
            refine ⟨344107467341805171910667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 917619912911480458428445 344107467341805171910667)
            ·
              refine ⟨516161201012707757866001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344107467341805171910667 516161201012707757866001)
              ·
                refine ⟨387120900759530818399501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516161201012707757866001 387120900759530818399501)
                ·
                  refine ⟨145170337784824056899813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387120900759530818399501 145170337784824056899813)
                  ·
                    refine ⟨27219438334654510668715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 145170337784824056899813 27219438334654510668715)
                    ·
                      rfl

theorem cell23_159029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_159029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159029 prefixEnd_159029 := by exact prefixLift 159029
  have htrace : WordTrace (prefixWord ++ tailWord_159029) baseStart_159029 baseEnd_159029 := by
    simpa [prefixWord, tailWord_159029, baseEnd_159029] using wordTrace_append hprefix tailTrace_159029
  have hstable : (prefixWord ++ tailWord_159029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159029).length < 2 ^ (prefixWord ++ tailWord_159029).sum := by decide
  have hdescent : baseEnd_159029 < baseStart_159029 := by decide
  rcases family_descends (prefixWord ++ tailWord_159029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159039 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 3]
def baseStart_159039 : Nat := 118140960795 + 159039 * 2 ^ 59
def prefixEnd_159039 : Nat := 4983230072969 + 3 ^ 40 * 159039 * 2
def baseEnd_159039 : Nat := 81663449810508492881099

theorem tailTrace_159039 : CollatzResearch.WordTrace tailWord_159039 prefixEnd_159039 81663449810508492881099 := by
  unfold tailWord_159039
  simp only [CollatzResearch.WordTrace]
  refine ⟨5800628870836339543856171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3867085913890893029237447 5800628870836339543856171)
  ·
    refine ⟨8700943306254509315784257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5800628870836339543856171 8700943306254509315784257)
    ·
      refine ⟨6525707479690881986838193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8700943306254509315784257 6525707479690881986838193)
      ·
        refine ⟨4894280609768161490128645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6525707479690881986838193 4894280609768161490128645)
        ·
          refine ⟨917677614331530279399121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4894280609768161490128645 917677614331530279399121)
          ·
            refine ⟨688258210748647709549341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 917677614331530279399121 688258210748647709549341)
            ·
              refine ⟨258096829030742891081003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 688258210748647709549341 258096829030742891081003)
              ·
                refine ⟨387145243546114336621505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258096829030742891081003 387145243546114336621505)
                ·
                  refine ⟨290358932659585752466129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387145243546114336621505 290358932659585752466129)
                  ·
                    refine ⟨217769199494689314349597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 290358932659585752466129 217769199494689314349597)
                    ·
                      refine ⟨81663449810508492881099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 217769199494689314349597 81663449810508492881099)
                      ·
                        rfl

theorem cell23_159039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_159039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159039 prefixEnd_159039 := by exact prefixLift 159039
  have htrace : WordTrace (prefixWord ++ tailWord_159039) baseStart_159039 baseEnd_159039 := by
    simpa [prefixWord, tailWord_159039, baseEnd_159039] using wordTrace_append hprefix tailTrace_159039
  have hstable : (prefixWord ++ tailWord_159039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159039).length < 2 ^ (prefixWord ++ tailWord_159039).sum := by decide
  have hdescent : baseEnd_159039 < baseStart_159039 := by decide
  rcases family_descends (prefixWord ++ tailWord_159039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159045 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_159045 : Nat := 118140960795 + 159045 * 2 ^ 59
def prefixEnd_159045 : Nat := 4983230072969 + 3 ^ 40 * 159045 * 2
def baseEnd_159045 : Nat := 81666530694435469406071

theorem tailTrace_159045 : CollatzResearch.WordTrace tailWord_159045 prefixEnd_159045 81666530694435469406071 := by
  unfold tailWord_159045
  simp only [CollatzResearch.WordTrace]
  refine ⟨5800847708814602568574589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3867231805876401712383059 5800847708814602568574589)
  ·
    refine ⟨2175317890805475963215471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5800847708814602568574589 2175317890805475963215471)
    ·
      refine ⟨3262976836208213944823207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2175317890805475963215471 3262976836208213944823207)
      ·
        refine ⟨4894465254312320917234811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262976836208213944823207 4894465254312320917234811)
        ·
          refine ⟨7341697881468481375852217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4894465254312320917234811 7341697881468481375852217)
          ·
            refine ⟨5506273411101361031889163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7341697881468481375852217 5506273411101361031889163)
            ·
              refine ⟨8259410116652041547833745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5506273411101361031889163 8259410116652041547833745)
              ·
                refine ⟨6194557587489031160875309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8259410116652041547833745 6194557587489031160875309)
                ·
                  refine ⟨2322959095308386685328241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6194557587489031160875309 2322959095308386685328241)
                  ·
                    refine ⟨1742219321481290013996181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2322959095308386685328241 1742219321481290013996181)
                    ·
                      refine ⟨81666530694435469406071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1742219321481290013996181 81666530694435469406071)
                      ·
                        rfl

theorem cell23_159045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_159045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159045 prefixEnd_159045 := by exact prefixLift 159045
  have htrace : WordTrace (prefixWord ++ tailWord_159045) baseStart_159045 baseEnd_159045 := by
    simpa [prefixWord, tailWord_159045, baseEnd_159045] using wordTrace_append hprefix tailTrace_159045
  have hstable : (prefixWord ++ tailWord_159045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159045).length < 2 ^ (prefixWord ++ tailWord_159045).sum := by decide
  have hdescent : baseEnd_159045 < baseStart_159045 := by decide
  rcases family_descends (prefixWord ++ tailWord_159045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159109 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 4]
def baseStart_159109 : Nat := 118140960795 + 159109 * 2 ^ 59
def prefixEnd_159109 : Nat := 4983230072969 + 3 ^ 40 * 159109 * 2
def baseEnd_159109 : Nat := 81699393456323219005777

theorem tailTrace_159109 : CollatzResearch.WordTrace tailWord_159109 prefixEnd_159109 81699393456323219005777 := by
  unfold tailWord_159109
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803181980582741498904381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3868787987055160999269587 5803181980582741498904381)
  ·
    refine ⟨2176193242718528062089143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5803181980582741498904381 2176193242718528062089143)
    ·
      refine ⟨3264289864077792093133715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176193242718528062089143 3264289864077792093133715)
      ·
        refine ⟨4896434796116688139700573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3264289864077792093133715 4896434796116688139700573)
        ·
          refine ⟨1836163048543758052387715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4896434796116688139700573 1836163048543758052387715)
          ·
            refine ⟨2754244572815637078581573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836163048543758052387715 2754244572815637078581573)
            ·
              refine ⟨516420857402931952234045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2754244572815637078581573 516420857402931952234045)
              ·
                refine ⟨193657821526099482087767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 516420857402931952234045 193657821526099482087767)
                ·
                  refine ⟨290486732289149223131651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193657821526099482087767 290486732289149223131651)
                  ·
                    refine ⟨435730098433723834697477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 290486732289149223131651 435730098433723834697477)
                    ·
                      refine ⟨81699393456323219005777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 435730098433723834697477 81699393456323219005777)
                      ·
                        rfl

theorem cell23_159109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_159109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159109 prefixEnd_159109 := by exact prefixLift 159109
  have htrace : WordTrace (prefixWord ++ tailWord_159109) baseStart_159109 baseEnd_159109 := by
    simpa [prefixWord, tailWord_159109, baseEnd_159109] using wordTrace_append hprefix tailTrace_159109
  have hstable : (prefixWord ++ tailWord_159109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159109).length < 2 ^ (prefixWord ++ tailWord_159109).sum := by decide
  have hdescent : baseEnd_159109 < baseStart_159109 := by decide
  rcases family_descends (prefixWord ++ tailWord_159109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159149 : List Nat := [1, 5, 2, 2, 1, 1, 2, 9]
def baseStart_159149 : Nat := 118140960795 + 159149 * 2 ^ 59
def prefixEnd_159149 : Nat := 4983230072969 + 3 ^ 40 * 159149 * 2
def baseEnd_159149 : Nat := 3026664173426039352059

theorem tailTrace_159149 : CollatzResearch.WordTrace tailWord_159149 prefixEnd_159149 3026664173426039352059 := by
  unfold tailWord_159149
  simp only [CollatzResearch.WordTrace]
  refine ⟨5804640900437828330360501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3869760600291885553573667 5804640900437828330360501)
  ·
    refine ⟨544185084416046405971297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5804640900437828330360501 544185084416046405971297)
    ·
      refine ⟨408138813312034804478473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 544185084416046405971297 408138813312034804478473)
      ·
        refine ⟨306104109984026103358855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408138813312034804478473 306104109984026103358855)
        ·
          refine ⟨459156164976039155038283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306104109984026103358855 459156164976039155038283)
          ·
            refine ⟨688734247464058732557425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459156164976039155038283 688734247464058732557425)
            ·
              refine ⟨516550685598044049418069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 688734247464058732557425 516550685598044049418069)
              ·
                refine ⟨3026664173426039352059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 516550685598044049418069 3026664173426039352059)
                ·
                  rfl

theorem cell23_159149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 9].length) (baseStart_159149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159149 prefixEnd_159149 := by exact prefixLift 159149
  have htrace : WordTrace (prefixWord ++ tailWord_159149) baseStart_159149 baseEnd_159149 := by
    simpa [prefixWord, tailWord_159149, baseEnd_159149] using wordTrace_append hprefix tailTrace_159149
  have hstable : (prefixWord ++ tailWord_159149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159149).length < 2 ^ (prefixWord ++ tailWord_159149).sum := by decide
  have hdescent : baseEnd_159149 < baseStart_159149 := by decide
  rcases family_descends (prefixWord ++ tailWord_159149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159159 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 3]
def baseStart_159159 : Nat := 118140960795 + 159159 * 2 ^ 59
def prefixEnd_159159 : Nat := 4983230072969 + 3 ^ 40 * 159159 * 2
def baseEnd_159159 : Nat := 81725067489048023380547

theorem tailTrace_159159 : CollatzResearch.WordTrace tailWord_159159 prefixEnd_159159 81725067489048023380547 := by
  unfold tailWord_159159
  simp only [CollatzResearch.WordTrace]
  refine ⟨5805005630401600038224531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3870003753601066692149687 5805005630401600038224531)
  ·
    refine ⟨8707508445602400057336797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5805005630401600038224531 8707508445602400057336797)
    ·
      refine ⟨3265315667100900021501299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8707508445602400057336797 3265315667100900021501299)
      ·
        refine ⟨4897973500651350032251949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3265315667100900021501299 4897973500651350032251949)
        ·
          refine ⟨1836740062744256262094481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4897973500651350032251949 1836740062744256262094481)
          ·
            refine ⟨1377555047058192196570861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1836740062744256262094481 1377555047058192196570861)
            ·
              refine ⟨516583142646822073714073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1377555047058192196570861 516583142646822073714073)
              ·
                refine ⟨387437356985116555285555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516583142646822073714073 387437356985116555285555)
                ·
                  refine ⟨581156035477674832928333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387437356985116555285555 581156035477674832928333)
                  ·
                    refine ⟨217933513304128062348125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581156035477674832928333 217933513304128062348125)
                    ·
                      refine ⟨81725067489048023380547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 217933513304128062348125 81725067489048023380547)
                      ·
                        rfl

theorem cell23_159159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_159159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159159 prefixEnd_159159 := by exact prefixLift 159159
  have htrace : WordTrace (prefixWord ++ tailWord_159159) baseStart_159159 baseEnd_159159 := by
    simpa [prefixWord, tailWord_159159, baseEnd_159159] using wordTrace_append hprefix tailTrace_159159
  have hstable : (prefixWord ++ tailWord_159159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159159).length < 2 ^ (prefixWord ++ tailWord_159159).sum := by decide
  have hdescent : baseEnd_159159 < baseStart_159159 := by decide
  rcases family_descends (prefixWord ++ tailWord_159159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159192 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 1, 8]
def baseStart_159192 : Nat := 118140960795 + 159192 * 2 ^ 59
def prefixEnd_159192 : Nat := 4983230072969 + 3 ^ 40 * 159192 * 2
def baseEnd_159192 : Nat := 27247337450215464755965

theorem tailTrace_159192 : CollatzResearch.WordTrace tailWord_159192 prefixEnd_159192 27247337450215464755965 := by
  unfold tailWord_159192
  simp only [CollatzResearch.WordTrace]
  refine ⟨2903104619641023337087915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3870806159521364449450553 2903104619641023337087915)
  ·
    refine ⟨4354656929461535005631873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2903104619641023337087915 4354656929461535005631873)
    ·
      refine ⟨3265992697096151254223905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4354656929461535005631873 3265992697096151254223905)
      ·
        refine ⟨2449494522822113440667929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3265992697096151254223905 2449494522822113440667929)
        ·
          refine ⟨1837120892116585080500947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2449494522822113440667929 1837120892116585080500947)
          ·
            refine ⟨2755681338174877620751421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837120892116585080500947 2755681338174877620751421)
            ·
              refine ⟨1033380501815579107781783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2755681338174877620751421 1033380501815579107781783)
              ·
                refine ⟨1550070752723368661672675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1033380501815579107781783 1550070752723368661672675)
                ·
                  refine ⟨2325106129085052992509013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550070752723368661672675 2325106129085052992509013)
                  ·
                    refine ⟨27247337450215464755965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2325106129085052992509013 27247337450215464755965)
                    ·
                      rfl

theorem cell23_159192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_159192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159192 prefixEnd_159192 := by exact prefixLift 159192
  have htrace : WordTrace (prefixWord ++ tailWord_159192) baseStart_159192 baseEnd_159192 := by
    simpa [prefixWord, tailWord_159192, baseEnd_159192] using wordTrace_append hprefix tailTrace_159192
  have hstable : (prefixWord ++ tailWord_159192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159192).length < 2 ^ (prefixWord ++ tailWord_159192).sum := by decide
  have hdescent : baseEnd_159192 < baseStart_159192 := by decide
  rcases family_descends (prefixWord ++ tailWord_159192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159216 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 1, 4, 2]
def baseStart_159216 : Nat := 118140960795 + 159216 * 2 ^ 59
def prefixEnd_159216 : Nat := 4983230072969 + 3 ^ 40 * 159216 * 2
def baseEnd_159216 : Nat := 81754335886354300367785

theorem tailTrace_159216 : CollatzResearch.WordTrace tailWord_159216 prefixEnd_159216 81754335886354300367785 := by
  unfold tailWord_159216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2903542295597549386524751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3871389727463399182033001 2903542295597549386524751)
  ·
    refine ⟨4355313443396324079787127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2903542295597549386524751 4355313443396324079787127)
    ·
      refine ⟨6532970165094486119680691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4355313443396324079787127 6532970165094486119680691)
      ·
        refine ⟨9799455247641729179521037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6532970165094486119680691 9799455247641729179521037)
        ·
          refine ⟨3674795717865648442320389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9799455247641729179521037 3674795717865648442320389)
          ·
            refine ⟨689024197099809082935073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3674795717865648442320389 689024197099809082935073)
            ·
              refine ⟨516768147824856812201305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689024197099809082935073 516768147824856812201305)
              ·
                refine ⟨387576110868642609150979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516768147824856812201305 387576110868642609150979)
                ·
                  refine ⟨581364166302963913726469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387576110868642609150979 581364166302963913726469)
                  ·
                    refine ⟨109005781181805733823713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 581364166302963913726469 109005781181805733823713)
                    ·
                      refine ⟨81754335886354300367785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 109005781181805733823713 81754335886354300367785)
                      ·
                        rfl

theorem cell23_159216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 4, 2].length) (baseStart_159216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159216 prefixEnd_159216 := by exact prefixLift 159216
  have htrace : WordTrace (prefixWord ++ tailWord_159216) baseStart_159216 baseEnd_159216 := by
    simpa [prefixWord, tailWord_159216, baseEnd_159216] using wordTrace_append hprefix tailTrace_159216
  have hstable : (prefixWord ++ tailWord_159216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159216).length < 2 ^ (prefixWord ++ tailWord_159216).sum := by decide
  have hdescent : baseEnd_159216 < baseStart_159216 := by decide
  rcases family_descends (prefixWord ++ tailWord_159216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159229 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_159229 : Nat := 118140960795 + 159229 * 2 ^ 59
def prefixEnd_159229 : Nat := 4983230072969 + 3 ^ 40 * 159229 * 2
def baseEnd_159229 : Nat := 81761011134862749505225

theorem tailTrace_159229 : CollatzResearch.WordTrace tailWord_159229 prefixEnd_159229 81761011134862749505225 := by
  unfold tailWord_159229
  simp only [CollatzResearch.WordTrace]
  refine ⟨5807558740148001993272741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3871705826765334662181827 5807558740148001993272741)
  ·
    refine ⟨1088917263777750373738639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5807558740148001993272741 1088917263777750373738639)
    ·
      refine ⟨1633375895666625560607959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1088917263777750373738639 1633375895666625560607959)
      ·
        refine ⟨2450063843499938340911939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1633375895666625560607959 2450063843499938340911939)
        ·
          refine ⟨3675095765249907511367909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2450063843499938340911939 3675095765249907511367909)
          ·
            refine ⟨689080455984357658381483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3675095765249907511367909 689080455984357658381483)
            ·
              refine ⟨1033620683976536487572225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689080455984357658381483 1033620683976536487572225)
              ·
                refine ⟨775215512982402365679169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1033620683976536487572225 775215512982402365679169)
                ·
                  refine ⟨581411634736801774259377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775215512982402365679169 581411634736801774259377)
                  ·
                    refine ⟨436058726052601330694533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 581411634736801774259377 436058726052601330694533)
                    ·
                      refine ⟨81761011134862749505225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 436058726052601330694533 81761011134862749505225)
                      ·
                        rfl

theorem cell23_159229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_159229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159229 prefixEnd_159229 := by exact prefixLift 159229
  have htrace : WordTrace (prefixWord ++ tailWord_159229) baseStart_159229 baseEnd_159229 := by
    simpa [prefixWord, tailWord_159229, baseEnd_159229] using wordTrace_append hprefix tailTrace_159229
  have hstable : (prefixWord ++ tailWord_159229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159229).length < 2 ^ (prefixWord ++ tailWord_159229).sum := by decide
  have hdescent : baseEnd_159229 < baseStart_159229 := by decide
  rcases family_descends (prefixWord ++ tailWord_159229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159239 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 7]
def baseStart_159239 : Nat := 118140960795 + 159239 * 2 ^ 59
def prefixEnd_159239 : Nat := 4983230072969 + 3 ^ 40 * 159239 * 2
def baseEnd_159239 : Nat := 9085127326823078931131

theorem tailTrace_159239 : CollatzResearch.WordTrace tailWord_159239 prefixEnd_159239 9085127326823078931131 := by
  unfold tailWord_159239
  simp only [CollatzResearch.WordTrace]
  refine ⟨5807923470111773701136771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3871948980074515800757847 5807923470111773701136771)
  ·
    refine ⟨8711885205167660551705157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5807923470111773701136771 8711885205167660551705157)
    ·
      refine ⟨1633478475968936353444717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8711885205167660551705157 1633478475968936353444717)
      ·
        refine ⟨612554428488351132541769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1633478475968936353444717 612554428488351132541769)
        ·
          refine ⟨459415821366263349406327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612554428488351132541769 459415821366263349406327)
          ·
            refine ⟨689123732049395024109491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459415821366263349406327 689123732049395024109491)
            ·
              refine ⟨1033685598074092536164237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689123732049395024109491 1033685598074092536164237)
              ·
                refine ⟨387632099277784701061589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1033685598074092536164237 387632099277784701061589)
                ·
                  refine ⟨9085127326823078931131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 387632099277784701061589 9085127326823078931131)
                  ·
                    rfl

theorem cell23_159239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 7].length) (baseStart_159239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159239 prefixEnd_159239 := by exact prefixLift 159239
  have htrace : WordTrace (prefixWord ++ tailWord_159239) baseStart_159239 baseEnd_159239 := by
    simpa [prefixWord, tailWord_159239, baseEnd_159239] using wordTrace_append hprefix tailTrace_159239
  have hstable : (prefixWord ++ tailWord_159239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159239).length < 2 ^ (prefixWord ++ tailWord_159239).sum := by decide
  have hdescent : baseEnd_159239 < baseStart_159239 := by decide
  rcases family_descends (prefixWord ++ tailWord_159239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159249 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 3]
def baseStart_159249 : Nat := 118140960795 + 159249 * 2 ^ 59
def prefixEnd_159249 : Nat := 4983230072969 + 3 ^ 40 * 159249 * 2
def baseEnd_159249 : Nat := 81771280747952671255133

theorem tailTrace_159249 : CollatzResearch.WordTrace tailWord_159249 prefixEnd_159249 81771280747952671255133 := by
  unfold tailWord_159249
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808288200075545409000801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3872192133383696939333867 5808288200075545409000801)
  ·
    refine ⟨4356216150056659056750601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5808288200075545409000801 4356216150056659056750601)
    ·
      refine ⟨3267162112542494292562951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4356216150056659056750601 3267162112542494292562951)
      ·
        refine ⟨4900743168813741438844427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3267162112542494292562951 4900743168813741438844427)
        ·
          refine ⟨7351114753220612158266641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4900743168813741438844427 7351114753220612158266641)
          ·
            refine ⟨5513336064915459118699981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7351114753220612158266641 5513336064915459118699981)
            ·
              refine ⟨2067501024343297169512493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5513336064915459118699981 2067501024343297169512493)
              ·
                refine ⟨775312884128736438567185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2067501024343297169512493 775312884128736438567185)
                ·
                  refine ⟨581484663096552328925389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775312884128736438567185 581484663096552328925389)
                  ·
                    refine ⟨218056748661207123347021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581484663096552328925389 218056748661207123347021)
                    ·
                      refine ⟨81771280747952671255133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 218056748661207123347021 81771280747952671255133)
                      ·
                        rfl

theorem cell23_159249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_159249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159249 prefixEnd_159249 := by exact prefixLift 159249
  have htrace : WordTrace (prefixWord ++ tailWord_159249) baseStart_159249 baseEnd_159249 := by
    simpa [prefixWord, tailWord_159249, baseEnd_159249] using wordTrace_append hprefix tailTrace_159249
  have hstable : (prefixWord ++ tailWord_159249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159249).length < 2 ^ (prefixWord ++ tailWord_159249).sum := by decide
  have hdescent : baseEnd_159249 < baseStart_159249 := by decide
  rcases family_descends (prefixWord ++ tailWord_159249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159269 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_159269 : Nat := 118140960795 + 159269 * 2 ^ 59
def prefixEnd_159269 : Nat := 4983230072969 + 3 ^ 40 * 159269 * 2
def baseEnd_159269 : Nat := 27260516787014197668347

theorem tailTrace_159269 : CollatzResearch.WordTrace tailWord_159269 prefixEnd_159269 27260516787014197668347 := by
  unfold tailWord_159269
  simp only [CollatzResearch.WordTrace]
  refine ⟨5809017660003088824728861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3872678440002059216485907 5809017660003088824728861)
  ·
    refine ⟨2178381622501158309273323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5809017660003088824728861 2178381622501158309273323)
    ·
      refine ⟨3267572433751737463909985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2178381622501158309273323 3267572433751737463909985)
      ·
        refine ⟨2450679325313803097932489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3267572433751737463909985 2450679325313803097932489)
        ·
          refine ⟨1838009493985352323449367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2450679325313803097932489 1838009493985352323449367)
          ·
            refine ⟨2757014240978028485174051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838009493985352323449367 2757014240978028485174051)
            ·
              refine ⟨4135521361467042727761077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2757014240978028485174051 4135521361467042727761077)
              ·
                refine ⟨387705127637535255727601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4135521361467042727761077 387705127637535255727601)
                ·
                  refine ⟨290778845728151441795701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387705127637535255727601 290778845728151441795701)
                  ·
                    refine ⟨27260516787014197668347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 290778845728151441795701 27260516787014197668347)
                    ·
                      rfl

theorem cell23_159269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_159269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159269 prefixEnd_159269 := by exact prefixLift 159269
  have htrace : WordTrace (prefixWord ++ tailWord_159269) baseStart_159269 baseEnd_159269 := by
    simpa [prefixWord, tailWord_159269, baseEnd_159269] using wordTrace_append hprefix tailTrace_159269
  have hstable : (prefixWord ++ tailWord_159269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159269).length < 2 ^ (prefixWord ++ tailWord_159269).sum := by decide
  have hdescent : baseEnd_159269 < baseStart_159269 := by decide
  rcases family_descends (prefixWord ++ tailWord_159269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159306 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2]
def baseStart_159306 : Nat := 118140960795 + 159306 * 2 ^ 59
def prefixEnd_159306 : Nat := 4983230072969 + 3 ^ 40 * 159306 * 2
def baseEnd_159306 : Nat := 81800549145258948242371

theorem tailTrace_159306 : CollatzResearch.WordTrace tailWord_159306 prefixEnd_159306 81800549145258948242371 := by
  unfold tailWord_159306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1452591790217261035956443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3873578107246029429217181 1452591790217261035956443)
  ·
    refine ⟨2178887685325891553934665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1452591790217261035956443 2178887685325891553934665)
    ·
      refine ⟨1634165763994418665450999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2178887685325891553934665 1634165763994418665450999)
      ·
        refine ⟨2451248645991627998176499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1634165763994418665450999 2451248645991627998176499)
        ·
          refine ⟨3676872968987441997264749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451248645991627998176499 3676872968987441997264749)
          ·
            refine ⟨1378827363370290748974281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3676872968987441997264749 1378827363370290748974281)
            ·
              refine ⟨1034120522527718061730711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1378827363370290748974281 1034120522527718061730711)
              ·
                refine ⟨1551180783791577092596067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034120522527718061730711 1551180783791577092596067)
                ·
                  refine ⟨2326771175687365638894101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1551180783791577092596067 2326771175687365638894101)
                  ·
                    refine ⟨109067398860345264323161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2326771175687365638894101 109067398860345264323161)
                    ·
                      refine ⟨81800549145258948242371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 109067398860345264323161 81800549145258948242371)
                      ·
                        rfl

theorem cell23_159306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_159306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159306 prefixEnd_159306 := by exact prefixLift 159306
  have htrace : WordTrace (prefixWord ++ tailWord_159306) baseStart_159306 baseEnd_159306 := by
    simpa [prefixWord, tailWord_159306, baseEnd_159306] using wordTrace_append hprefix tailTrace_159306
  have hstable : (prefixWord ++ tailWord_159306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159306).length < 2 ^ (prefixWord ++ tailWord_159306).sum := by decide
  have hdescent : baseEnd_159306 < baseStart_159306 := by decide
  rcases family_descends (prefixWord ++ tailWord_159306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159316 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_159316 : Nat := 118140960795 + 159316 * 2 ^ 59
def prefixEnd_159316 : Nat := 4983230072969 + 3 ^ 40 * 159316 * 2
def baseEnd_159316 : Nat := 27268561317267969705775

theorem tailTrace_159316 : CollatzResearch.WordTrace tailWord_159316 prefixEnd_159316 27268561317267969705775 := by
  unfold tailWord_159316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2905365945416407925844901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3873821260555210567793201 2905365945416407925844901)
  ·
    refine ⟨544756114765576486095919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2905365945416407925844901 544756114765576486095919)
    ·
      refine ⟨817134172148364729143879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544756114765576486095919 817134172148364729143879)
      ·
        refine ⟨1225701258222547093715819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 817134172148364729143879 1225701258222547093715819)
        ·
          refine ⟨1838551887333820640573729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225701258222547093715819 1838551887333820640573729)
          ·
            refine ⟨1378913915500365480430297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1838551887333820640573729 1378913915500365480430297)
            ·
              refine ⟨1034185436625274110322723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1378913915500365480430297 1034185436625274110322723)
              ·
                refine ⟨1551278154937911165484085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034185436625274110322723 1551278154937911165484085)
                ·
                  refine ⟨145432327025429171764133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1551278154937911165484085 145432327025429171764133)
                  ·
                    refine ⟨27268561317267969705775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 145432327025429171764133 27268561317267969705775)
                    ·
                      rfl

theorem cell23_159316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_159316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159316 prefixEnd_159316 := by exact prefixLift 159316
  have htrace : WordTrace (prefixWord ++ tailWord_159316) baseStart_159316 baseEnd_159316 := by
    simpa [prefixWord, tailWord_159316, baseEnd_159316] using wordTrace_append hprefix tailTrace_159316
  have hstable : (prefixWord ++ tailWord_159316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159316).length < 2 ^ (prefixWord ++ tailWord_159316).sum := by decide
  have hdescent : baseEnd_159316 < baseStart_159316 := by decide
  rcases family_descends (prefixWord ++ tailWord_159316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159339 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 3]
def baseStart_159339 : Nat := 118140960795 + 159339 * 2 ^ 59
def prefixEnd_159339 : Nat := 4983230072969 + 3 ^ 40 * 159339 * 2
def baseEnd_159339 : Nat := 81817494006857319129719

theorem tailTrace_159339 : CollatzResearch.WordTrace tailWord_159339 prefixEnd_159339 81817494006857319129719 := by
  unfold tailWord_159339
  simp only [CollatzResearch.WordTrace]
  refine ⟨5811570769749490779777071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3874380513166327186518047 5811570769749490779777071)
  ·
    refine ⟨8717356154624236169665607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5811570769749490779777071 8717356154624236169665607)
    ·
      refine ⟨13076034231936354254498411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8717356154624236169665607 13076034231936354254498411)
      ·
        refine ⟨19614051347904531381747617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13076034231936354254498411 19614051347904531381747617)
        ·
          refine ⟨14710538510928398536310713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19614051347904531381747617 14710538510928398536310713)
          ·
            refine ⟨11032903883196298902233035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14710538510928398536310713 11032903883196298902233035)
            ·
              refine ⟨16549355824794448353349553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11032903883196298902233035 16549355824794448353349553)
              ·
                refine ⟨12412016868595836265012165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16549355824794448353349553 12412016868595836265012165)
                ·
                  refine ⟨2327253162861719299689781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12412016868595836265012165 2327253162861719299689781)
                  ·
                    refine ⟨218179984018286184345917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2327253162861719299689781 218179984018286184345917)
                    ·
                      refine ⟨81817494006857319129719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 218179984018286184345917 81817494006857319129719)
                      ·
                        rfl

theorem cell23_159339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 3].length) (baseStart_159339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159339 prefixEnd_159339 := by exact prefixLift 159339
  have htrace : WordTrace (prefixWord ++ tailWord_159339) baseStart_159339 baseEnd_159339 := by
    simpa [prefixWord, tailWord_159339, baseEnd_159339] using wordTrace_append hprefix tailTrace_159339
  have hstable : (prefixWord ++ tailWord_159339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159339).length < 2 ^ (prefixWord ++ tailWord_159339).sum := by decide
  have hdescent : baseEnd_159339 < baseStart_159339 := by decide
  rcases family_descends (prefixWord ++ tailWord_159339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159346 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 6]
def baseStart_159346 : Nat := 118140960795 + 159346 * 2 ^ 59
def prefixEnd_159346 : Nat := 4983230072969 + 3 ^ 40 * 159346 * 2
def baseEnd_159346 : Nat := 9091232041270976860243

theorem tailTrace_159346 : CollatzResearch.WordTrace tailWord_159346 prefixEnd_159346 9091232041270976860243 := by
  unfold tailWord_159346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1452956520181032743820473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3874550720482753983521261 1452956520181032743820473)
  ·
    refine ⟨1089717390135774557865355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1452956520181032743820473 1089717390135774557865355)
    ·
      refine ⟨1634576085203661836798033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1089717390135774557865355 1634576085203661836798033)
      ·
        refine ⟨1225932063902746377598525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1634576085203661836798033 1225932063902746377598525)
        ·
          refine ⟨459724523963529891599447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1225932063902746377598525 459724523963529891599447)
          ·
            refine ⟨689586785945294837399171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459724523963529891599447 689586785945294837399171)
            ·
              refine ⟨1034380178917942256098757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689586785945294837399171 1034380178917942256098757)
              ·
                refine ⟨193946283547114173018517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1034380178917942256098757 193946283547114173018517)
                ·
                  refine ⟨9091232041270976860243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 193946283547114173018517 9091232041270976860243)
                  ·
                    rfl

theorem cell23_159346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_159346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159346 prefixEnd_159346 := by exact prefixLift 159346
  have htrace : WordTrace (prefixWord ++ tailWord_159346) baseStart_159346 baseEnd_159346 := by
    simpa [prefixWord, tailWord_159346, baseEnd_159346] using wordTrace_append hprefix tailTrace_159346
  have hstable : (prefixWord ++ tailWord_159346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159346).length < 2 ^ (prefixWord ++ tailWord_159346).sum := by decide
  have hdescent : baseEnd_159346 < baseStart_159346 := by decide
  rcases family_descends (prefixWord ++ tailWord_159346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159383 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 1, 5, 2]
def baseStart_159383 : Nat := 118140960795 + 159383 * 2 ^ 59
def prefixEnd_159383 : Nat := 4983230072969 + 3 ^ 40 * 159383 * 2
def baseEnd_159383 : Nat := 81840087155655146979517

theorem tailTrace_159383 : CollatzResearch.WordTrace tailWord_159383 prefixEnd_159383 81840087155655146979517 := by
  unfold tailWord_159383
  simp only [CollatzResearch.WordTrace]
  refine ⟨5813175581590086294378803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3875450387726724196252535 5813175581590086294378803)
  ·
    refine ⟨8719763372385129441568205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5813175581590086294378803 8719763372385129441568205)
    ·
      refine ⟨3269911264644423540588077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8719763372385129441568205 3269911264644423540588077)
      ·
        refine ⟨1226216724241658827720529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3269911264644423540588077 1226216724241658827720529)
        ·
          refine ⟨919662543181244120790397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1226216724241658827720529 919662543181244120790397)
          ·
            refine ⟨344873453692966545296399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 919662543181244120790397 344873453692966545296399)
            ·
              refine ⟨517310180539449817944599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344873453692966545296399 517310180539449817944599)
              ·
                refine ⟨775965270809174726916899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517310180539449817944599 775965270809174726916899)
                ·
                  refine ⟨1163947906213762090375349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775965270809174726916899 1163947906213762090375349)
                  ·
                    refine ⟨109120116207540195972689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1163947906213762090375349 109120116207540195972689)
                    ·
                      refine ⟨81840087155655146979517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 109120116207540195972689 81840087155655146979517)
                      ·
                        rfl

theorem cell23_159383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_159383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159383 prefixEnd_159383 := by exact prefixLift 159383
  have htrace : WordTrace (prefixWord ++ tailWord_159383) baseStart_159383 baseEnd_159383 := by
    simpa [prefixWord, tailWord_159383, baseEnd_159383] using wordTrace_append hprefix tailTrace_159383
  have hstable : (prefixWord ++ tailWord_159383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159383).length < 2 ^ (prefixWord ++ tailWord_159383).sum := by decide
  have hdescent : baseEnd_159383 < baseStart_159383 := by decide
  rcases family_descends (prefixWord ++ tailWord_159383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159393 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 1, 5]
def baseStart_159393 : Nat := 118140960795 + 159393 * 2 ^ 59
def prefixEnd_159393 : Nat := 4983230072969 + 3 ^ 40 * 159393 * 2
def baseEnd_159393 : Nat := 27281740654066702618157

theorem tailTrace_159393 : CollatzResearch.WordTrace tailWord_159393 prefixEnd_159393 27281740654066702618157 := by
  unfold tailWord_159393
  simp only [CollatzResearch.WordTrace]
  refine ⟨5813540311553858002242833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3875693541035905334828555 5813540311553858002242833)
  ·
    refine ⟨4360155233665393501682125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5813540311553858002242833 4360155233665393501682125)
    ·
      refine ⟨1635058212624522563130797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4360155233665393501682125 1635058212624522563130797)
      ·
        refine ⟨613146829734195961174049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1635058212624522563130797 613146829734195961174049)
        ·
          refine ⟨459860122300646970880537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 613146829734195961174049 459860122300646970880537)
          ·
            refine ⟨344895091725485228160403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459860122300646970880537 344895091725485228160403)
            ·
              refine ⟨517342637588227842240605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344895091725485228160403 517342637588227842240605)
              ·
                refine ⟨194003489095585440840227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 517342637588227842240605 194003489095585440840227)
                ·
                  refine ⟨291005233643378161260341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194003489095585440840227 291005233643378161260341)
                  ·
                    refine ⟨27281740654066702618157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 291005233643378161260341 27281740654066702618157)
                    ·
                      rfl

theorem cell23_159393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_159393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159393 prefixEnd_159393 := by exact prefixLift 159393
  have htrace : WordTrace (prefixWord ++ tailWord_159393) baseStart_159393 baseEnd_159393 := by
    simpa [prefixWord, tailWord_159393, baseEnd_159393] using wordTrace_append hprefix tailTrace_159393
  have hstable : (prefixWord ++ tailWord_159393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159393).length < 2 ^ (prefixWord ++ tailWord_159393).sum := by decide
  have hdescent : baseEnd_159393 < baseStart_159393 := by decide
  rcases family_descends (prefixWord ++ tailWord_159393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159416 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 5, 2, 3]
def baseStart_159416 : Nat := 118140960795 + 159416 * 2 ^ 59
def prefixEnd_159416 : Nat := 4983230072969 + 3 ^ 40 * 159416 * 2
def baseEnd_159416 : Nat := 81857032017253517866865

theorem tailTrace_159416 : CollatzResearch.WordTrace tailWord_159416 prefixEnd_159416 81857032017253517866865 := by
  unfold tailWord_159416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2907189595235266465165051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3876252793647021953553401 2907189595235266465165051)
  ·
    refine ⟨4360784392852899697747577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2907189595235266465165051 4360784392852899697747577)
    ·
      refine ⟨3270588294639674773310683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4360784392852899697747577 3270588294639674773310683)
      ·
        refine ⟨4905882441959512159966025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270588294639674773310683 4905882441959512159966025)
        ·
          refine ⟨3679411831469634119974519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4905882441959512159966025 3679411831469634119974519)
          ·
            refine ⟨5519117747204451179961779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3679411831469634119974519 5519117747204451179961779)
            ·
              refine ⟨8278676620806676769942669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519117747204451179961779 8278676620806676769942669)
              ·
                refine ⟨3104503732802503788728501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8278676620806676769942669 3104503732802503788728501)
                ·
                  refine ⟨291047224950234730193297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3104503732802503788728501 291047224950234730193297)
                  ·
                    refine ⟨218285418712676047644973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 291047224950234730193297 218285418712676047644973)
                    ·
                      refine ⟨81857032017253517866865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 218285418712676047644973 81857032017253517866865)
                      ·
                        rfl

theorem cell23_159416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_159416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159416 prefixEnd_159416 := by exact prefixLift 159416
  have htrace : WordTrace (prefixWord ++ tailWord_159416) baseStart_159416 baseEnd_159416 := by
    simpa [prefixWord, tailWord_159416, baseEnd_159416] using wordTrace_append hprefix tailTrace_159416
  have hstable : (prefixWord ++ tailWord_159416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159416).length < 2 ^ (prefixWord ++ tailWord_159416).sum := by decide
  have hdescent : baseEnd_159416 < baseStart_159416 := by decide
  rcases family_descends (prefixWord ++ tailWord_159416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159429 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_159429 : Nat := 118140960795 + 159429 * 2 ^ 59
def prefixEnd_159429 : Nat := 4983230072969 + 3 ^ 40 * 159429 * 2
def baseEnd_159429 : Nat := 81863707265761967004305

theorem tailTrace_159429 : CollatzResearch.WordTrace tailWord_159429 prefixEnd_159429 81863707265761967004305 := by
  unfold tailWord_159429
  simp only [CollatzResearch.WordTrace]
  refine ⟨5814853339423436150553341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3876568892948957433702227 5814853339423436150553341)
  ·
    refine ⟨2180570002283788556457503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5814853339423436150553341 2180570002283788556457503)
    ·
      refine ⟨3270855003425682834686255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2180570002283788556457503 3270855003425682834686255)
      ·
        refine ⟨4906282505138524252029383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270855003425682834686255 4906282505138524252029383)
        ·
          refine ⟨7359423757707786378044075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4906282505138524252029383 7359423757707786378044075)
          ·
            refine ⟨11039135636561679567066113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7359423757707786378044075 11039135636561679567066113)
            ·
              refine ⟨8279351727421259675299585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11039135636561679567066113 8279351727421259675299585)
              ·
                refine ⟨6209513795565944756474689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8279351727421259675299585 6209513795565944756474689)
                ·
                  refine ⟨4657135346674458567356017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6209513795565944756474689 4657135346674458567356017)
                  ·
                    refine ⟨3492851510005843925517013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4657135346674458567356017 3492851510005843925517013)
                    ·
                      refine ⟨81863707265761967004305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3492851510005843925517013 81863707265761967004305)
                      ·
                        rfl

theorem cell23_159429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_159429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159429 prefixEnd_159429 := by exact prefixLift 159429
  have htrace : WordTrace (prefixWord ++ tailWord_159429) baseStart_159429 baseEnd_159429 := by
    simpa [prefixWord, tailWord_159429, baseEnd_159429] using wordTrace_append hprefix tailTrace_159429
  have hstable : (prefixWord ++ tailWord_159429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159429).length < 2 ^ (prefixWord ++ tailWord_159429).sum := by decide
  have hdescent : baseEnd_159429 < baseStart_159429 := by decide
  rcases family_descends (prefixWord ++ tailWord_159429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159439 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_159439 : Nat := 118140960795 + 159439 * 2 ^ 59
def prefixEnd_159439 : Nat := 4983230072969 + 3 ^ 40 * 159439 * 2
def baseEnd_159439 : Nat := 81868842072306927879259

theorem tailTrace_159439 : CollatzResearch.WordTrace tailWord_159439 prefixEnd_159439 81868842072306927879259 := by
  unfold tailWord_159439
  simp only [CollatzResearch.WordTrace]
  refine ⟨5815218069387207858417371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3876812046258138572278247 5815218069387207858417371)
  ·
    refine ⟨8722827104080811787626057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5815218069387207858417371 8722827104080811787626057)
    ·
      refine ⟨6542120328060608840719543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8722827104080811787626057 6542120328060608840719543)
      ·
        refine ⟨9813180492090913261079315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6542120328060608840719543 9813180492090913261079315)
        ·
          refine ⟨14719770738136369891618973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9813180492090913261079315 14719770738136369891618973)
          ·
            refine ⟨5519914026801138709357115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14719770738136369891618973 5519914026801138709357115)
            ·
              refine ⟨8279871040201708064035673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519914026801138709357115 8279871040201708064035673)
              ·
                refine ⟨6209903280151281048026755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8279871040201708064035673 6209903280151281048026755)
                ·
                  refine ⟨9314854920226921572040133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6209903280151281048026755 9314854920226921572040133)
                  ·
                    refine ⟨1746535297542547794757525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9314854920226921572040133 1746535297542547794757525)
                    ·
                      refine ⟨81868842072306927879259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1746535297542547794757525 81868842072306927879259)
                      ·
                        rfl

theorem cell23_159439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_159439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159439 prefixEnd_159439 := by exact prefixLift 159439
  have htrace : WordTrace (prefixWord ++ tailWord_159439) baseStart_159439 baseEnd_159439 := by
    simpa [prefixWord, tailWord_159439, baseEnd_159439] using wordTrace_append hprefix tailTrace_159439
  have hstable : (prefixWord ++ tailWord_159439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159439).length < 2 ^ (prefixWord ++ tailWord_159439).sum := by decide
  have hdescent : baseEnd_159439 < baseStart_159439 := by decide
  rcases family_descends (prefixWord ++ tailWord_159439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159501 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_159501 : Nat := 118140960795 + 159501 * 2 ^ 59
def prefixEnd_159501 : Nat := 4983230072969 + 3 ^ 40 * 159501 * 2
def baseEnd_159501 : Nat := 81900677872885685303975

theorem tailTrace_159501 : CollatzResearch.WordTrace tailWord_159501 prefixEnd_159501 81900677872885685303975 := by
  unfold tailWord_159501
  simp only [CollatzResearch.WordTrace]
  refine ⟨5817479395162592447174357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3878319596775061631449571 5817479395162592447174357)
  ·
    refine ⟨136347173324123260480649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 5817479395162592447174357 136347173324123260480649)
    ·
      refine ⟨102260379993092445360487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136347173324123260480649 102260379993092445360487)
      ·
        refine ⟨153390569989638668040731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102260379993092445360487 153390569989638668040731)
        ·
          refine ⟨230085854984458002061097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153390569989638668040731 230085854984458002061097)
          ·
            refine ⟨172564391238343501545823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230085854984458002061097 172564391238343501545823)
            ·
              refine ⟨258846586857515252318735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172564391238343501545823 258846586857515252318735)
              ·
                refine ⟨388269880286272878478103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258846586857515252318735 388269880286272878478103)
                ·
                  refine ⟨582404820429409317717155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388269880286272878478103 582404820429409317717155)
                  ·
                    refine ⟨873607230644113976575733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 582404820429409317717155 873607230644113976575733)
                    ·
                      refine ⟨81900677872885685303975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 873607230644113976575733 81900677872885685303975)
                      ·
                        rfl

theorem cell23_159501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_159501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159501 prefixEnd_159501 := by exact prefixLift 159501
  have htrace : WordTrace (prefixWord ++ tailWord_159501) baseStart_159501 baseEnd_159501 := by
    simpa [prefixWord, tailWord_159501, baseEnd_159501] using wordTrace_append hprefix tailTrace_159501
  have hstable : (prefixWord ++ tailWord_159501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159501).length < 2 ^ (prefixWord ++ tailWord_159501).sum := by decide
  have hdescent : baseEnd_159501 < baseStart_159501 := by decide
  rcases family_descends (prefixWord ++ tailWord_159501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159537 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 2, 2, 2]
def baseStart_159537 : Nat := 118140960795 + 159537 * 2 ^ 59
def prefixEnd_159537 : Nat := 4983230072969 + 3 ^ 40 * 159537 * 2
def baseEnd_159537 : Nat := 81919163176447544453809

theorem tailTrace_159537 : CollatzResearch.WordTrace tailWord_159537 prefixEnd_159537 81919163176447544453809 := by
  unfold tailWord_159537
  simp only [CollatzResearch.WordTrace]
  refine ⟨5818792423032170595484865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3879194948688113730323243 5818792423032170595484865)
  ·
    refine ⟨4364094317274127946613649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5818792423032170595484865 4364094317274127946613649)
    ·
      refine ⟨3273070737955595959960237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4364094317274127946613649 3273070737955595959960237)
      ·
        refine ⟨1227401526733348484985089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3273070737955595959960237 1227401526733348484985089)
        ·
          refine ⟨920551145050011363738817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1227401526733348484985089 920551145050011363738817)
          ·
            refine ⟨690413358787508522804113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 920551145050011363738817 690413358787508522804113)
            ·
              refine ⟨517810019090631392103085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690413358787508522804113 517810019090631392103085)
              ·
                refine ⟨194178757158986772038657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 517810019090631392103085 194178757158986772038657)
                ·
                  refine ⟨145634067869240079028993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194178757158986772038657 145634067869240079028993)
                  ·
                    refine ⟨109225550901930059271745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 145634067869240079028993 109225550901930059271745)
                    ·
                      refine ⟨81919163176447544453809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 109225550901930059271745 81919163176447544453809)
                      ·
                        rfl

theorem cell23_159537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_159537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159537 prefixEnd_159537 := by exact prefixLift 159537
  have htrace : WordTrace (prefixWord ++ tailWord_159537) baseStart_159537 baseEnd_159537 := by
    simpa [prefixWord, tailWord_159537, baseEnd_159537] using wordTrace_append hprefix tailTrace_159537
  have hstable : (prefixWord ++ tailWord_159537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159537).length < 2 ^ (prefixWord ++ tailWord_159537).sum := by decide
  have hdescent : baseEnd_159537 < baseStart_159537 := by decide
  rcases family_descends (prefixWord ++ tailWord_159537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159558 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_159558 : Nat := 118140960795 + 159558 * 2 ^ 59
def prefixEnd_159558 : Nat := 4983230072969 + 3 ^ 40 * 159558 * 2
def baseEnd_159558 : Nat := 81929946270191962291213

theorem tailTrace_159558 : CollatzResearch.WordTrace tailWord_159558 prefixEnd_159558 81929946270191962291213 := by
  unfold tailWord_159558
  simp only [CollatzResearch.WordTrace]
  refine ⟨181861198623627849437479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3879705570637394121332885 181861198623627849437479)
  ·
    refine ⟨272791797935441774156219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181861198623627849437479 272791797935441774156219)
    ·
      refine ⟨409187696903162661234329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272791797935441774156219 409187696903162661234329)
      ·
        refine ⟨306890772677371995925747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409187696903162661234329 306890772677371995925747)
        ·
          refine ⟨460336159016057993888621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306890772677371995925747 460336159016057993888621)
          ·
            refine ⟨172626059631021747708233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 460336159016057993888621 172626059631021747708233)
            ·
              refine ⟨129469544723266310781175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172626059631021747708233 129469544723266310781175)
              ·
                refine ⟨194204317084899466171763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129469544723266310781175 194204317084899466171763)
                ·
                  refine ⟨291306475627349199257645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194204317084899466171763 291306475627349199257645)
                  ·
                    refine ⟨109239928360255949721617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291306475627349199257645 109239928360255949721617)
                    ·
                      refine ⟨81929946270191962291213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 109239928360255949721617 81929946270191962291213)
                      ·
                        rfl

theorem cell23_159558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_159558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159558 prefixEnd_159558 := by exact prefixLift 159558
  have htrace : WordTrace (prefixWord ++ tailWord_159558) baseStart_159558 baseEnd_159558 := by
    simpa [prefixWord, tailWord_159558, baseEnd_159558] using wordTrace_append hprefix tailTrace_159558
  have hstable : (prefixWord ++ tailWord_159558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159558).length < 2 ^ (prefixWord ++ tailWord_159558).sum := by decide
  have hdescent : baseEnd_159558 < baseStart_159558 := by decide
  rcases family_descends (prefixWord ++ tailWord_159558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159560 : List Nat := [2, 1, 3, 1, 1, 5, 2, 3, 5]
def baseStart_159560 : Nat := 118140960795 + 159560 * 2 ^ 59
def prefixEnd_159560 : Nat := 4983230072969 + 3 ^ 40 * 159560 * 2
def baseEnd_159560 : Nat := 9103441470166772718467

theorem tailTrace_159560 : CollatzResearch.WordTrace tailWord_159560 prefixEnd_159560 9103441470166772718467 := by
  unfold tailWord_159560
  simp only [CollatzResearch.WordTrace]
  refine ⟨2909815650974422761786067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3879754201299230349048089 2909815650974422761786067)
  ·
    refine ⟨4364723476461634142679101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2909815650974422761786067 4364723476461634142679101)
    ·
      refine ⟨1636771303673112803504663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4364723476461634142679101 1636771303673112803504663)
      ·
        refine ⟨2455156955509669205256995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1636771303673112803504663 2455156955509669205256995)
        ·
          refine ⟨3682735433264503807885493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455156955509669205256995 3682735433264503807885493)
          ·
            refine ⟨345256446868547231989265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3682735433264503807885493 345256446868547231989265)
            ·
              refine ⟨258942335151410423991949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345256446868547231989265 258942335151410423991949)
              ·
                refine ⟨97103375681778908996981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258942335151410423991949 97103375681778908996981)
                ·
                  refine ⟨9103441470166772718467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97103375681778908996981 9103441470166772718467)
                  ·
                    rfl

theorem cell23_159560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 5].length) (baseStart_159560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159560 prefixEnd_159560 := by exact prefixLift 159560
  have htrace : WordTrace (prefixWord ++ tailWord_159560) baseStart_159560 baseEnd_159560 := by
    simpa [prefixWord, tailWord_159560, baseEnd_159560] using wordTrace_append hprefix tailTrace_159560
  have hstable : (prefixWord ++ tailWord_159560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159560).length < 2 ^ (prefixWord ++ tailWord_159560).sum := by decide
  have hdescent : baseEnd_159560 < baseStart_159560 := by decide
  rcases family_descends (prefixWord ++ tailWord_159560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159616 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 10]
def baseStart_159616 : Nat := 118140960795 + 159616 * 2 ^ 59
def prefixEnd_159616 : Nat := 4983230072969 + 3 ^ 40 * 159616 * 2
def baseEnd_159616 : Nat := 9106636460905859485105

theorem tailTrace_159616 : CollatzResearch.WordTrace tailWord_159616 prefixEnd_159616 9106636460905859485105 := by
  unfold tailWord_159616
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910836894872983543805351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3881115859830644725073801 2910836894872983543805351)
  ·
    refine ⟨4366255342309475315708027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2910836894872983543805351 4366255342309475315708027)
    ·
      refine ⟨6549383013464212973562041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4366255342309475315708027 6549383013464212973562041)
      ·
        refine ⟨4912037260098159730171531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6549383013464212973562041 4912037260098159730171531)
        ·
          refine ⟨7368055890147239595257297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4912037260098159730171531 7368055890147239595257297)
          ·
            refine ⟨5526041917610429696442973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7368055890147239595257297 5526041917610429696442973)
            ·
              refine ⟨2072265719103911136166115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5526041917610429696442973 2072265719103911136166115)
              ·
                refine ⟨3108398578655866704249173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072265719103911136166115 3108398578655866704249173)
                ·
                  refine ⟨9106636460905859485105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 3108398578655866704249173 9106636460905859485105)
                  ·
                    rfl

theorem cell23_159616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 10].length) (baseStart_159616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159616 prefixEnd_159616 := by exact prefixLift 159616
  have htrace : WordTrace (prefixWord ++ tailWord_159616) baseStart_159616 baseEnd_159616 := by
    simpa [prefixWord, tailWord_159616, baseEnd_159616] using wordTrace_append hprefix tailTrace_159616
  have hstable : (prefixWord ++ tailWord_159616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159616).length < 2 ^ (prefixWord ++ tailWord_159616).sum := by decide
  have hdescent : baseEnd_159616 < baseStart_159616 := by decide
  rcases family_descends (prefixWord ++ tailWord_159616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159663 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 3, 5]
def baseStart_159663 : Nat := 118140960795 + 159663 * 2 ^ 59
def prefixEnd_159663 : Nat := 4983230072969 + 3 ^ 40 * 159663 * 2
def baseEnd_159663 : Nat := 27327953912971350492743

theorem tailTrace_159663 : CollatzResearch.WordTrace tailWord_159663 prefixEnd_159663 27327953912971350492743 := by
  unfold tailWord_159663
  simp only [CollatzResearch.WordTrace]
  refine ⟨5823388020575694114571643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3882258680383796076381095 5823388020575694114571643)
  ·
    refine ⟨8735082030863541171857465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5823388020575694114571643 8735082030863541171857465)
    ·
      refine ⟨6551311523147655878893099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8735082030863541171857465 6551311523147655878893099)
      ·
        refine ⟨9826967284721483818339649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6551311523147655878893099 9826967284721483818339649)
        ·
          refine ⟨7370225463541112863754737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9826967284721483818339649 7370225463541112863754737)
          ·
            refine ⟨5527669097655834647816053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7370225463541112863754737 5527669097655834647816053)
            ·
              refine ⟨518218977905234498232755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5527669097655834647816053 518218977905234498232755)
              ·
                refine ⟨777328466857851747349133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518218977905234498232755 777328466857851747349133)
                ·
                  refine ⟨291498175071694405255925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777328466857851747349133 291498175071694405255925)
                  ·
                    refine ⟨27327953912971350492743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 291498175071694405255925 27327953912971350492743)
                    ·
                      rfl

theorem cell23_159663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_159663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159663 prefixEnd_159663 := by exact prefixLift 159663
  have htrace : WordTrace (prefixWord ++ tailWord_159663) baseStart_159663 baseEnd_159663 := by
    simpa [prefixWord, tailWord_159663, baseEnd_159663] using wordTrace_append hprefix tailTrace_159663
  have hstable : (prefixWord ++ tailWord_159663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159663).length < 2 ^ (prefixWord ++ tailWord_159663).sum := by decide
  have hdescent : baseEnd_159663 < baseStart_159663 := by decide
  rcases family_descends (prefixWord ++ tailWord_159663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159683 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 4]
def baseStart_159683 : Nat := 118140960795 + 159683 * 2 ^ 59
def prefixEnd_159683 : Nat := 4983230072969 + 3 ^ 40 * 159683 * 2
def baseEnd_159683 : Nat := 81994131352003973228137

theorem tailTrace_159683 : CollatzResearch.WordTrace tailWord_159683 prefixEnd_159683 81994131352003973228137 := by
  unfold tailWord_159683
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824117480503237530299703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3882744987002158353533135 5824117480503237530299703)
  ·
    refine ⟨8736176220754856295449555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5824117480503237530299703 8736176220754856295449555)
    ·
      refine ⟨13104264331132284443174333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8736176220754856295449555 13104264331132284443174333)
      ·
        refine ⟨4914099124174606666190375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13104264331132284443174333 4914099124174606666190375)
        ·
          refine ⟨7371148686261909999285563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4914099124174606666190375 7371148686261909999285563)
          ·
            refine ⟨11056723029392864998928345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7371148686261909999285563 11056723029392864998928345)
            ·
              refine ⟨8292542272044648749196259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11056723029392864998928345 8292542272044648749196259)
              ·
                refine ⟨12438813408066973123794389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8292542272044648749196259 12438813408066973123794389)
                ·
                  refine ⟨291534689251569682588931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12438813408066973123794389 291534689251569682588931)
                  ·
                    refine ⟨437302033877354523883397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 291534689251569682588931 437302033877354523883397)
                    ·
                      refine ⟨81994131352003973228137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 437302033877354523883397 81994131352003973228137)
                      ·
                        rfl

theorem cell23_159683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_159683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159683 prefixEnd_159683 := by exact prefixLift 159683
  have htrace : WordTrace (prefixWord ++ tailWord_159683) baseStart_159683 baseEnd_159683 := by
    simpa [prefixWord, tailWord_159683, baseEnd_159683] using wordTrace_append hprefix tailTrace_159683
  have hstable : (prefixWord ++ tailWord_159683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159683).length < 2 ^ (prefixWord ++ tailWord_159683).sum := by decide
  have hdescent : baseEnd_159683 < baseStart_159683 := by decide
  rcases family_descends (prefixWord ++ tailWord_159683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159694 : List Nat := [4, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3]
def baseStart_159694 : Nat := 118140960795 + 159694 * 2 ^ 59
def prefixEnd_159694 : Nat := 4983230072969 + 3 ^ 40 * 159694 * 2
def baseEnd_159694 : Nat := 81999779639203430190587

theorem tailTrace_159694 : CollatzResearch.WordTrace tailWord_159694 prefixEnd_159694 81999779639203430190587 := by
  unfold tailWord_159694
  simp only [CollatzResearch.WordTrace]
  refine ⟨728064835432923301118767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3883012455642257605966757 728064835432923301118767)
  ·
    refine ⟨1092097253149384951678151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 728064835432923301118767 1092097253149384951678151)
    ·
      refine ⟨1638145879724077427517227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092097253149384951678151 1638145879724077427517227)
      ·
        refine ⟨2457218819586116141275841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638145879724077427517227 2457218819586116141275841)
        ·
          refine ⟨1842914114689587105956881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2457218819586116141275841 1842914114689587105956881)
          ·
            refine ⟨1382185586017190329467661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1842914114689587105956881 1382185586017190329467661)
            ·
              refine ⟨518319594756446373550373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1382185586017190329467661 518319594756446373550373)
              ·
                refine ⟨97184924016833695040695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 518319594756446373550373 97184924016833695040695)
                ·
                  refine ⟨145777386025250542561043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97184924016833695040695 145777386025250542561043)
                  ·
                    refine ⟨218666079037875813841565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 145777386025250542561043 218666079037875813841565)
                    ·
                      refine ⟨81999779639203430190587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 218666079037875813841565 81999779639203430190587)
                      ·
                        rfl

theorem cell23_159694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_159694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159694 prefixEnd_159694 := by exact prefixLift 159694
  have htrace : WordTrace (prefixWord ++ tailWord_159694) baseStart_159694 baseEnd_159694 := by
    simpa [prefixWord, tailWord_159694, baseEnd_159694] using wordTrace_append hprefix tailTrace_159694
  have hstable : (prefixWord ++ tailWord_159694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159694).length < 2 ^ (prefixWord ++ tailWord_159694).sum := by decide
  have hdescent : baseEnd_159694 < baseStart_159694 := by decide
  rcases family_descends (prefixWord ++ tailWord_159694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159700 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_159700 : Nat := 118140960795 + 159700 * 2 ^ 59
def prefixEnd_159700 : Nat := 4983230072969 + 3 ^ 40 * 159700 * 2
def baseEnd_159700 : Nat := 82002860523130406715559

theorem tailTrace_159700 : CollatzResearch.WordTrace tailWord_159700 prefixEnd_159700 82002860523130406715559 := by
  unfold tailWord_159700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2912368760720824716834277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3883158347627766289112369 2912368760720824716834277)
  ·
    refine ⟨546069142635154634406427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2912368760720824716834277 546069142635154634406427)
    ·
      refine ⟨819103713952731951609641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546069142635154634406427 819103713952731951609641)
      ·
        refine ⟨614327785464548963707231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 819103713952731951609641 614327785464548963707231)
        ·
          refine ⟨921491678196823445560847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614327785464548963707231 921491678196823445560847)
          ·
            refine ⟨1382237517295235168341271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921491678196823445560847 1382237517295235168341271)
            ·
              refine ⟨2073356275942852752511907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382237517295235168341271 2073356275942852752511907)
              ·
                refine ⟨3110034413914279128767861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073356275942852752511907 3110034413914279128767861)
                ·
                  refine ⟨291565726304463668321987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3110034413914279128767861 291565726304463668321987)
                  ·
                    refine ⟨437348589456695502482981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 291565726304463668321987 437348589456695502482981)
                    ·
                      refine ⟨82002860523130406715559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 437348589456695502482981 82002860523130406715559)
                      ·
                        rfl

theorem cell23_159700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_159700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159700 prefixEnd_159700 := by exact prefixLift 159700
  have htrace : WordTrace (prefixWord ++ tailWord_159700) baseStart_159700 baseEnd_159700 := by
    simpa [prefixWord, tailWord_159700, baseEnd_159700] using wordTrace_append hprefix tailTrace_159700
  have hstable : (prefixWord ++ tailWord_159700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159700).length < 2 ^ (prefixWord ++ tailWord_159700).sum := by decide
  have hdescent : baseEnd_159700 < baseStart_159700 := by decide
  rcases family_descends (prefixWord ++ tailWord_159700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159703 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_159703 : Nat := 118140960795 + 159703 * 2 ^ 59
def prefixEnd_159703 : Nat := 4983230072969 + 3 ^ 40 * 159703 * 2
def baseEnd_159703 : Nat := 82004400965093894978045

theorem tailTrace_159703 : CollatzResearch.WordTrace tailWord_159703 prefixEnd_159703 82004400965093894978045 := by
  unfold tailWord_159703
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824846940430780946027763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3883231293620520630685175 5824846940430780946027763)
  ·
    refine ⟨8737270410646171419041645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5824846940430780946027763 8737270410646171419041645)
    ·
      refine ⟨3276476403992314282140617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8737270410646171419041645 3276476403992314282140617)
      ·
        refine ⟨2457357302994235711605463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3276476403992314282140617 2457357302994235711605463)
        ·
          refine ⟨3686035954491353567408195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2457357302994235711605463 3686035954491353567408195)
          ·
            refine ⟨5529053931737030351112293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686035954491353567408195 5529053931737030351112293)
            ·
              refine ⟨1036697612200693190833555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5529053931737030351112293 1036697612200693190833555)
              ·
                refine ⟨1555046418301039786250333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036697612200693190833555 1555046418301039786250333)
                ·
                  refine ⟨583142406862889919843875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1555046418301039786250333 583142406862889919843875)
                  ·
                    refine ⟨874713610294334879765813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 583142406862889919843875 874713610294334879765813)
                    ·
                      refine ⟨82004400965093894978045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 874713610294334879765813 82004400965093894978045)
                      ·
                        rfl

theorem cell23_159703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_159703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159703 prefixEnd_159703 := by exact prefixLift 159703
  have htrace : WordTrace (prefixWord ++ tailWord_159703) baseStart_159703 baseEnd_159703 := by
    simpa [prefixWord, tailWord_159703, baseEnd_159703] using wordTrace_append hprefix tailTrace_159703
  have hstable : (prefixWord ++ tailWord_159703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159703).length < 2 ^ (prefixWord ++ tailWord_159703).sum := by decide
  have hdescent : baseEnd_159703 < baseStart_159703 := by decide
  rcases family_descends (prefixWord ++ tailWord_159703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159713 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_159713 : Nat := 118140960795 + 159713 * 2 ^ 59
def prefixEnd_159713 : Nat := 4983230072969 + 3 ^ 40 * 159713 * 2
def baseEnd_159713 : Nat := 82009535771638855852999

theorem tailTrace_159713 : CollatzResearch.WordTrace tailWord_159713 prefixEnd_159713 82009535771638855852999 := by
  unfold tailWord_159713
  simp only [CollatzResearch.WordTrace]
  refine ⟨5825211670394552653891793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3883474446929701769261195 5825211670394552653891793)
  ·
    refine ⟨4368908752795914490418845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5825211670394552653891793 4368908752795914490418845)
    ·
      refine ⟨1638340782298467933907067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4368908752795914490418845 1638340782298467933907067)
      ·
        refine ⟨2457511173447701900860601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638340782298467933907067 2457511173447701900860601)
        ·
          refine ⟨1843133380085776425645451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2457511173447701900860601 1843133380085776425645451)
          ·
            refine ⟨2764700070128664638468177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843133380085776425645451 2764700070128664638468177)
            ·
              refine ⟨2073525052596498478851133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2764700070128664638468177 2073525052596498478851133)
              ·
                refine ⟨777571894723686929569175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2073525052596498478851133 777571894723686929569175)
                ·
                  refine ⟨1166357842085530394353763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777571894723686929569175 1166357842085530394353763)
                  ·
                    refine ⟨1749536763128295591530645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1166357842085530394353763 1749536763128295591530645)
                    ·
                      refine ⟨82009535771638855852999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1749536763128295591530645 82009535771638855852999)
                      ·
                        rfl

theorem cell23_159713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_159713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159713 prefixEnd_159713 := by exact prefixLift 159713
  have htrace : WordTrace (prefixWord ++ tailWord_159713) baseStart_159713 baseEnd_159713 := by
    simpa [prefixWord, tailWord_159713, baseEnd_159713] using wordTrace_append hprefix tailTrace_159713
  have hstable : (prefixWord ++ tailWord_159713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159713).length < 2 ^ (prefixWord ++ tailWord_159713).sum := by decide
  have hdescent : baseEnd_159713 < baseStart_159713 := by decide
  rcases family_descends (prefixWord ++ tailWord_159713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159734 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_159734 : Nat := 118140960795 + 159734 * 2 ^ 59
def prefixEnd_159734 : Nat := 4983230072969 + 3 ^ 40 * 159734 * 2
def baseEnd_159734 : Nat := 82020318865383273690403

theorem tailTrace_159734 : CollatzResearch.WordTrace tailWord_159734 prefixEnd_159734 82020318865383273690403 := by
  unfold tailWord_159734
  simp only [CollatzResearch.WordTrace]
  refine ⟨364123600207404577525391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3883985068878982160270837 364123600207404577525391)
  ·
    refine ⟨546185400311106866288087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 364123600207404577525391 546185400311106866288087)
    ·
      refine ⟨819278100466660299432131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546185400311106866288087 819278100466660299432131)
      ·
        refine ⟨1228917150699990449148197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819278100466660299432131 1228917150699990449148197)
        ·
          refine ⟨230421965756248209215287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1228917150699990449148197 230421965756248209215287)
          ·
            refine ⟨345632948634372313822931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230421965756248209215287 345632948634372313822931)
            ·
              refine ⟨518449422951558470734397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345632948634372313822931 518449422951558470734397)
              ·
                refine ⟨194418533606834426525399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 518449422951558470734397 194418533606834426525399)
                ·
                  refine ⟨291627800410251639788099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194418533606834426525399 291627800410251639788099)
                  ·
                    refine ⟨437441700615377459682149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 291627800410251639788099 437441700615377459682149)
                    ·
                      refine ⟨82020318865383273690403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 437441700615377459682149 82020318865383273690403)
                      ·
                        rfl

theorem cell23_159734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_159734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159734 prefixEnd_159734 := by exact prefixLift 159734
  have htrace : WordTrace (prefixWord ++ tailWord_159734) baseStart_159734 baseEnd_159734 := by
    simpa [prefixWord, tailWord_159734, baseEnd_159734] using wordTrace_append hprefix tailTrace_159734
  have hstable : (prefixWord ++ tailWord_159734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159734).length < 2 ^ (prefixWord ++ tailWord_159734).sum := by decide
  have hdescent : baseEnd_159734 < baseStart_159734 := by decide
  rcases family_descends (prefixWord ++ tailWord_159734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159737 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 1, 2, 3]
def baseStart_159737 : Nat := 118140960795 + 159737 * 2 ^ 59
def prefixEnd_159737 : Nat := 4983230072969 + 3 ^ 40 * 159737 * 2
def baseEnd_159737 : Nat := 82021859307346761952889

theorem tailTrace_159737 : CollatzResearch.WordTrace tailWord_159737 prefixEnd_159737 82021859307346761952889 := by
  unfold tailWord_159737
  simp only [CollatzResearch.WordTrace]
  refine ⟨5826087022307604752765465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3884058014871736501843643 5826087022307604752765465)
  ·
    refine ⟨4369565266730703564574099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5826087022307604752765465 4369565266730703564574099)
    ·
      refine ⟨6554347900096055346861149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4369565266730703564574099 6554347900096055346861149)
      ·
        refine ⟨2457880462536020755072931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6554347900096055346861149 2457880462536020755072931)
        ·
          refine ⟨3686820693804031132609397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2457880462536020755072931 3686820693804031132609397)
          ·
            refine ⟨345639440044127918682131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3686820693804031132609397 345639440044127918682131)
            ·
              refine ⟨518459160066191878023197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345639440044127918682131 518459160066191878023197)
              ·
                refine ⟨194422185024821954258699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 518459160066191878023197 194422185024821954258699)
                ·
                  refine ⟨291633277537232931388049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194422185024821954258699 291633277537232931388049)
                  ·
                    refine ⟨218724958152924698541037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 291633277537232931388049 218724958152924698541037)
                    ·
                      refine ⟨82021859307346761952889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 218724958152924698541037 82021859307346761952889)
                      ·
                        rfl

theorem cell23_159737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_159737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159737 prefixEnd_159737 := by exact prefixLift 159737
  have htrace : WordTrace (prefixWord ++ tailWord_159737) baseStart_159737 baseEnd_159737 := by
    simpa [prefixWord, tailWord_159737, baseEnd_159737] using wordTrace_append hprefix tailTrace_159737
  have hstable : (prefixWord ++ tailWord_159737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159737).length < 2 ^ (prefixWord ++ tailWord_159737).sum := by decide
  have hdescent : baseEnd_159737 < baseStart_159737 := by decide
  rcases family_descends (prefixWord ++ tailWord_159737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159751 : List Nat := [1, 1, 4, 3, 1, 2, 2, 4, 1, 2, 2]
def baseStart_159751 : Nat := 118140960795 + 159751 * 2 ^ 59
def prefixEnd_159751 : Nat := 4983230072969 + 3 ^ 40 * 159751 * 2
def baseEnd_159751 : Nat := 82029048036509707177825

theorem tailTrace_159751 : CollatzResearch.WordTrace tailWord_159751 prefixEnd_159751 82029048036509707177825 := by
  unfold tailWord_159751
  simp only [CollatzResearch.WordTrace]
  refine ⟨5826597644256885143775107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3884398429504590095850071 5826597644256885143775107)
  ·
    refine ⟨8739896466385327715662661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5826597644256885143775107 8739896466385327715662661)
    ·
      refine ⟨1638730587447248946686749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8739896466385327715662661 1638730587447248946686749)
      ·
        refine ⟨614523970292718355007531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1638730587447248946686749 614523970292718355007531)
        ·
          refine ⟨921785955439077532511297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614523970292718355007531 921785955439077532511297)
          ·
            refine ⟨691339466579308149383473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 921785955439077532511297 691339466579308149383473)
            ·
              refine ⟨518504599934481112037605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 691339466579308149383473 518504599934481112037605)
              ·
                refine ⟨97219612487715208507051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 518504599934481112037605 97219612487715208507051)
                ·
                  refine ⟨145829418731572812760577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97219612487715208507051 145829418731572812760577)
                  ·
                    refine ⟨109372064048679609570433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 145829418731572812760577 109372064048679609570433)
                    ·
                      refine ⟨82029048036509707177825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 109372064048679609570433 82029048036509707177825)
                      ·
                        rfl

theorem cell23_159751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_159751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159751 prefixEnd_159751 := by exact prefixLift 159751
  have htrace : WordTrace (prefixWord ++ tailWord_159751) baseStart_159751 baseEnd_159751 := by
    simpa [prefixWord, tailWord_159751, baseEnd_159751] using wordTrace_append hprefix tailTrace_159751
  have hstable : (prefixWord ++ tailWord_159751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159751).length < 2 ^ (prefixWord ++ tailWord_159751).sum := by decide
  have hdescent : baseEnd_159751 < baseStart_159751 := by decide
  rcases family_descends (prefixWord ++ tailWord_159751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159764 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_159764 : Nat := 118140960795 + 159764 * 2 ^ 59
def prefixEnd_159764 : Nat := 4983230072969 + 3 ^ 40 * 159764 * 2
def baseEnd_159764 : Nat := 82035723285018156315265

theorem tailTrace_159764 : CollatzResearch.WordTrace tailWord_159764 prefixEnd_159764 82035723285018156315265 := by
  unfold tailWord_159764
  simp only [CollatzResearch.WordTrace]
  refine ⟨2913535896604894181999173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3884714528806525575998897 2913535896604894181999173)
  ·
    refine ⟨546287980613417659124845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2913535896604894181999173 546287980613417659124845)
    ·
      refine ⟨204857992730031622171817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 546287980613417659124845 204857992730031622171817)
      ·
        refine ⟨153643494547523716628863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204857992730031622171817 153643494547523716628863)
        ·
          refine ⟨230465241821285574943295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153643494547523716628863 230465241821285574943295)
          ·
            refine ⟨345697862731928362414943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230465241821285574943295 345697862731928362414943)
            ·
              refine ⟨518546794097892543622415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345697862731928362414943 518546794097892543622415)
              ·
                refine ⟨777820191146838815433623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518546794097892543622415 777820191146838815433623)
                ·
                  refine ⟨1166730286720258223150435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777820191146838815433623 1166730286720258223150435)
                  ·
                    refine ⟨1750095430080387334725653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1166730286720258223150435 1750095430080387334725653)
                    ·
                      refine ⟨82035723285018156315265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1750095430080387334725653 82035723285018156315265)
                      ·
                        rfl

theorem cell23_159764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_159764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159764 prefixEnd_159764 := by exact prefixLift 159764
  have htrace : WordTrace (prefixWord ++ tailWord_159764) baseStart_159764 baseEnd_159764 := by
    simpa [prefixWord, tailWord_159764, baseEnd_159764] using wordTrace_append hprefix tailTrace_159764
  have hstable : (prefixWord ++ tailWord_159764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159764).length < 2 ^ (prefixWord ++ tailWord_159764).sum := by decide
  have hdescent : baseEnd_159764 < baseStart_159764 := by decide
  rcases family_descends (prefixWord ++ tailWord_159764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159794 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2]
def baseStart_159794 : Nat := 118140960795 + 159794 * 2 ^ 59
def prefixEnd_159794 : Nat := 4983230072969 + 3 ^ 40 * 159794 * 2
def baseEnd_159794 : Nat := 82051127704653038940127

theorem tailTrace_159794 : CollatzResearch.WordTrace tailWord_159794 prefixEnd_159794 82051127704653038940127 := by
  unfold tailWord_159794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1457041495775275871897609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3885443988734068991726957 1457041495775275871897609)
  ·
    refine ⟨1092781121831456903923207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1457041495775275871897609 1092781121831456903923207)
    ·
      refine ⟨1639171682747185355884811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092781121831456903923207 1639171682747185355884811)
      ·
        refine ⟨2458757524120778033827217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1639171682747185355884811 2458757524120778033827217)
        ·
          refine ⟨1844068143090583525370413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2458757524120778033827217 1844068143090583525370413)
          ·
            refine ⟨691525553658968822013905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1844068143090583525370413 691525553658968822013905)
            ·
              refine ⟨518644165244226616510429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 691525553658968822013905 518644165244226616510429)
              ·
                refine ⟨194491561966584981191411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 518644165244226616510429 194491561966584981191411)
                ·
                  refine ⟨291737342949877471787117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194491561966584981191411 291737342949877471787117)
                  ·
                    refine ⟨109401503606204051920169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291737342949877471787117 109401503606204051920169)
                    ·
                      refine ⟨82051127704653038940127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 109401503606204051920169 82051127704653038940127)
                      ·
                        rfl

theorem cell23_159794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_159794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159794 prefixEnd_159794 := by exact prefixLift 159794
  have htrace : WordTrace (prefixWord ++ tailWord_159794) baseStart_159794 baseEnd_159794 := by
    simpa [prefixWord, tailWord_159794, baseEnd_159794] using wordTrace_append hprefix tailTrace_159794
  have hstable : (prefixWord ++ tailWord_159794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159794).length < 2 ^ (prefixWord ++ tailWord_159794).sum := by decide
  have hdescent : baseEnd_159794 < baseStart_159794 := by decide
  rcases family_descends (prefixWord ++ tailWord_159794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159820 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_159820 : Nat := 118140960795 + 159820 * 2 ^ 59
def prefixEnd_159820 : Nat := 4983230072969 + 3 ^ 40 * 159820 * 2
def baseEnd_159820 : Nat := 82064478201669937215007

theorem tailTrace_159820 : CollatzResearch.WordTrace tailWord_159820 prefixEnd_159820 82064478201669937215007 := by
  unfold tailWord_159820
  simp only [CollatzResearch.WordTrace]
  refine ⟨2914557140503454964018457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3886076187337939952024609 2914557140503454964018457)
  ·
    refine ⟨2185917855377591223013843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2914557140503454964018457 2185917855377591223013843)
    ·
      refine ⟨3278876783066386834520765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2185917855377591223013843 3278876783066386834520765)
      ·
        refine ⟨1229578793649895062945287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3278876783066386834520765 1229578793649895062945287)
        ·
          refine ⟨1844368190474842594417931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229578793649895062945287 1844368190474842594417931)
          ·
            refine ⟨2766552285712263891626897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844368190474842594417931 2766552285712263891626897)
            ·
              refine ⟨2074914214284197918720173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2766552285712263891626897 2074914214284197918720173)
              ·
                refine ⟨778092830356574219520065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2074914214284197918720173 778092830356574219520065)
                ·
                  refine ⟨583569622767430664640049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 778092830356574219520065 583569622767430664640049)
                  ·
                    refine ⟨437677217075572998480037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 583569622767430664640049 437677217075572998480037)
                    ·
                      refine ⟨82064478201669937215007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 437677217075572998480037 82064478201669937215007)
                      ·
                        rfl

theorem cell23_159820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_159820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159820 prefixEnd_159820 := by exact prefixLift 159820
  have htrace : WordTrace (prefixWord ++ tailWord_159820) baseStart_159820 baseEnd_159820 := by
    simpa [prefixWord, tailWord_159820, baseEnd_159820] using wordTrace_append hprefix tailTrace_159820
  have hstable : (prefixWord ++ tailWord_159820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159820).length < 2 ^ (prefixWord ++ tailWord_159820).sum := by decide
  have hdescent : baseEnd_159820 < baseStart_159820 := by decide
  rcases family_descends (prefixWord ++ tailWord_159820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159823 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_159823 : Nat := 118140960795 + 159823 * 2 ^ 59
def prefixEnd_159823 : Nat := 4983230072969 + 3 ^ 40 * 159823 * 2
def baseEnd_159823 : Nat := 82066018643633425477493

theorem tailTrace_159823 : CollatzResearch.WordTrace tailWord_159823 prefixEnd_159823 82066018643633425477493 := by
  unfold tailWord_159823
  simp only [CollatzResearch.WordTrace]
  refine ⟨5829223699996041440396123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3886149133330694293597415 5829223699996041440396123)
  ·
    refine ⟨8743835549994062160594185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5829223699996041440396123 8743835549994062160594185)
    ·
      refine ⟨6557876662495546620445639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8743835549994062160594185 6557876662495546620445639)
      ·
        refine ⟨9836814993743319930668459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6557876662495546620445639 9836814993743319930668459)
        ·
          refine ⟨14755222490614979896002689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9836814993743319930668459 14755222490614979896002689)
          ·
            refine ⟨11066416867961234922002017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14755222490614979896002689 11066416867961234922002017)
            ·
              refine ⟨8299812650970926191501513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11066416867961234922002017 8299812650970926191501513)
              ·
                refine ⟨6224859488228194643626135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8299812650970926191501513 6224859488228194643626135)
                ·
                  refine ⟨9337289232342291965439203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224859488228194643626135 9337289232342291965439203)
                  ·
                    refine ⟨14005933848513437948158805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9337289232342291965439203 14005933848513437948158805)
                    ·
                      refine ⟨82066018643633425477493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 14005933848513437948158805 82066018643633425477493)
                      ·
                        rfl

theorem cell23_159823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_159823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159823 prefixEnd_159823 := by exact prefixLift 159823
  have htrace : WordTrace (prefixWord ++ tailWord_159823) baseStart_159823 baseEnd_159823 := by
    simpa [prefixWord, tailWord_159823, baseEnd_159823] using wordTrace_append hprefix tailTrace_159823
  have hstable : (prefixWord ++ tailWord_159823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159823).length < 2 ^ (prefixWord ++ tailWord_159823).sum := by decide
  have hdescent : baseEnd_159823 < baseStart_159823 := by decide
  rcases family_descends (prefixWord ++ tailWord_159823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
