import V185TrunkScan23Chunk0933

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5527739 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 5, 3, 2]
def baseStart_5527739 : Nat := 118140960795 + 5527739 * 2 ^ 59
def prefixEnd_5527739 : Nat := 4983230072969 + 3 ^ 40 * 5527739 * 2
def baseEnd_5527739 : Nat := 2838387039603653429440897

theorem tailTrace_5527739 : CollatzResearch.WordTrace tailWord_5527739 prefixEnd_5527739 2838387039603653429440897 := by
  unfold tailWord_5527739
  simp only [CollatzResearch.WordTrace]
  refine ⟨201613204520953140505642271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134408803013968760337094847 201613204520953140505642271)
  ·
    refine ⟨302419806781429710758463407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201613204520953140505642271 302419806781429710758463407)
    ·
      refine ⟨453629710172144566137695111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302419806781429710758463407 453629710172144566137695111)
      ·
        refine ⟨680444565258216849206542667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453629710172144566137695111 680444565258216849206542667)
        ·
          refine ⟨1020666847887325273809814001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680444565258216849206542667 1020666847887325273809814001)
          ·
            refine ⟨765500135915493955357360501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1020666847887325273809814001 765500135915493955357360501)
            ·
              refine ⟨71765637742077558314752547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 765500135915493955357360501 71765637742077558314752547)
              ·
                refine ⟨107648456613116337472128821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71765637742077558314752547 107648456613116337472128821)
                ·
                  refine ⟨10092042807479656638012077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107648456613116337472128821 10092042807479656638012077)
                  ·
                    refine ⟨3784516052804871239254529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10092042807479656638012077 3784516052804871239254529)
                    ·
                      refine ⟨2838387039603653429440897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784516052804871239254529 2838387039603653429440897)
                      ·
                        rfl

theorem cell23_5527739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 3, 2].length) (baseStart_5527739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527739 prefixEnd_5527739 := by exact prefixLift 5527739
  have htrace : WordTrace (prefixWord ++ tailWord_5527739) baseStart_5527739 baseEnd_5527739 := by
    simpa [prefixWord, tailWord_5527739, baseEnd_5527739] using wordTrace_append hprefix tailTrace_5527739
  have hstable : (prefixWord ++ tailWord_5527739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527739).length < 2 ^ (prefixWord ++ tailWord_5527739).sum := by decide
  have hdescent : baseEnd_5527739 < baseStart_5527739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527752 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_5527752 : Nat := 118140960795 + 5527752 * 2 ^ 59
def prefixEnd_5527752 : Nat := 4983230072969 + 3 ^ 40 * 5527752 * 2
def baseEnd_5527752 : Nat := 2838393714852161878578337

theorem tailTrace_5527752 : CollatzResearch.WordTrace tailWord_5527752 prefixEnd_5527752 2838393714852161878578337 := by
  unfold tailWord_5527752
  simp only [CollatzResearch.WordTrace]
  refine ⟨100806839334953021862932755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134409119113270695817243673 100806839334953021862932755)
  ·
    refine ⟨151210259002429532794399133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100806839334953021862932755 151210259002429532794399133)
    ·
      refine ⟨56703847125911074797899675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151210259002429532794399133 56703847125911074797899675)
      ·
        refine ⟨85055770688866612196849513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56703847125911074797899675 85055770688866612196849513)
        ·
          refine ⟨63791828016649959147637135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85055770688866612196849513 63791828016649959147637135)
          ·
            refine ⟨95687742024974938721455703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63791828016649959147637135 95687742024974938721455703)
            ·
              refine ⟨143531613037462408082183555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95687742024974938721455703 143531613037462408082183555)
              ·
                refine ⟨215297419556193612123275333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143531613037462408082183555 215297419556193612123275333)
                ·
                  refine ⟨40368266166786302273114125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215297419556193612123275333 40368266166786302273114125)
                  ·
                    refine ⟨15138099812544863352417797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40368266166786302273114125 15138099812544863352417797)
                    ·
                      refine ⟨2838393714852161878578337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15138099812544863352417797 2838393714852161878578337)
                      ·
                        rfl

theorem cell23_5527752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_5527752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527752 prefixEnd_5527752 := by exact prefixLift 5527752
  have htrace : WordTrace (prefixWord ++ tailWord_5527752) baseStart_5527752 baseEnd_5527752 := by
    simpa [prefixWord, tailWord_5527752, baseEnd_5527752] using wordTrace_append hprefix tailTrace_5527752
  have hstable : (prefixWord ++ tailWord_5527752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527752).length < 2 ^ (prefixWord ++ tailWord_5527752).sum := by decide
  have hdescent : baseEnd_5527752 < baseStart_5527752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527839 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 4, 5]
def baseStart_5527839 : Nat := 118140960795 + 5527839 * 2 ^ 59
def prefixEnd_5527839 : Nat := 4983230072969 + 3 ^ 40 * 5527839 * 2
def baseEnd_5527839 : Nat := 946146129223034346063479

theorem tailTrace_5527839 : CollatzResearch.WordTrace tailWord_5527839 prefixEnd_5527839 946146129223034346063479 := by
  unfold tailWord_5527839
  simp only [CollatzResearch.WordTrace]
  refine ⟨201616851820590857584282571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134411234547060571722855047 201616851820590857584282571)
  ·
    refine ⟨302425277730886286376423857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201616851820590857584282571 302425277730886286376423857)
    ·
      refine ⟨226818958298164714782317893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302425277730886286376423857 226818958298164714782317893)
      ·
        refine ⟨42528554680905884021684605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226818958298164714782317893 42528554680905884021684605)
        ·
          refine ⟨15948208005339706508131727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42528554680905884021684605 15948208005339706508131727)
          ·
            refine ⟨23922312008009559762197591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15948208005339706508131727 23922312008009559762197591)
            ·
              refine ⟨35883468012014339643296387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23922312008009559762197591 35883468012014339643296387)
              ·
                refine ⟨53825202018021509464944581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35883468012014339643296387 53825202018021509464944581)
                ·
                  refine ⟨10092225378379033024677109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53825202018021509464944581 10092225378379033024677109)
                  ·
                    refine ⟨946146129223034346063479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10092225378379033024677109 946146129223034346063479)
                    ·
                      rfl

theorem cell23_5527839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_5527839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527839 prefixEnd_5527839 := by exact prefixLift 5527839
  have htrace : WordTrace (prefixWord ++ tailWord_5527839) baseStart_5527839 baseEnd_5527839 := by
    simpa [prefixWord, tailWord_5527839, baseEnd_5527839] using wordTrace_append hprefix tailTrace_5527839
  have hstable : (prefixWord ++ tailWord_5527839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527839).length < 2 ^ (prefixWord ++ tailWord_5527839).sum := by decide
  have hdescent : baseEnd_5527839 < baseStart_5527839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527859 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 4]
def baseStart_5527859 : Nat := 118140960795 + 5527859 * 2 ^ 59
def prefixEnd_5527859 : Nat := 4983230072969 + 3 ^ 40 * 5527859 * 2
def baseEnd_5527859 : Nat := 2838448657282192959940345

theorem tailTrace_5527859 : CollatzResearch.WordTrace tailWord_5527859 prefixEnd_5527859 2838448657282192959940345 := by
  unfold tailWord_5527859
  simp only [CollatzResearch.WordTrace]
  refine ⟨201617581280518401000010631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134411720853678934000007087 201617581280518401000010631)
  ·
    refine ⟨302426371920777601500015947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201617581280518401000010631 302426371920777601500015947)
    ·
      refine ⟨453639557881166402250023921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302426371920777601500015947 453639557881166402250023921)
      ·
        refine ⟨340229668410874801687517941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453639557881166402250023921 340229668410874801687517941)
        ·
          refine ⟨31896531413519512658204807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 340229668410874801687517941 31896531413519512658204807)
          ·
            refine ⟨47844797120279268987307211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31896531413519512658204807 47844797120279268987307211)
            ·
              refine ⟨71767195680418903480960817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47844797120279268987307211 71767195680418903480960817)
              ·
                refine ⟨53825396760314177610720613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71767195680418903480960817 53825396760314177610720613)
                ·
                  refine ⟨10092261892558908302010115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53825396760314177610720613 10092261892558908302010115)
                  ·
                    refine ⟨15138392838838362453015173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10092261892558908302010115 15138392838838362453015173)
                    ·
                      refine ⟨2838448657282192959940345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15138392838838362453015173 2838448657282192959940345)
                      ·
                        rfl

theorem cell23_5527859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_5527859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527859 prefixEnd_5527859 := by exact prefixLift 5527859
  have htrace : WordTrace (prefixWord ++ tailWord_5527859) baseStart_5527859 baseEnd_5527859 := by
    simpa [prefixWord, tailWord_5527859, baseEnd_5527859] using wordTrace_append hprefix tailTrace_5527859
  have hstable : (prefixWord ++ tailWord_5527859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527859).length < 2 ^ (prefixWord ++ tailWord_5527859).sum := by decide
  have hdescent : baseEnd_5527859 < baseStart_5527859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527873 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 2, 5]
def baseStart_5527873 : Nat := 118140960795 + 5527873 * 2 ^ 59
def prefixEnd_5527873 : Nat := 4983230072969 + 3 ^ 40 * 5527873 * 2
def baseEnd_5527873 : Nat := 946151948670451968388427

theorem tailTrace_5527873 : CollatzResearch.WordTrace tailWord_5527873 prefixEnd_5527873 946151948670451968388427 := by
  unfold tailWord_5527873
  simp only [CollatzResearch.WordTrace]
  refine ⟨201618091902467681391020273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134412061268311787594013515 201618091902467681391020273)
  ·
    refine ⟨151213568926850761043265205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201618091902467681391020273 151213568926850761043265205)
    ·
      refine ⟨14176272086892258847806113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151213568926850761043265205 14176272086892258847806113)
      ·
        refine ⟨10632204065169194135854585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14176272086892258847806113 10632204065169194135854585)
        ·
          refine ⟨7974153048876895601890939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10632204065169194135854585 7974153048876895601890939)
          ·
            refine ⟨11961229573315343402836409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7974153048876895601890939 11961229573315343402836409)
            ·
              refine ⟨8970922179986507552127307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11961229573315343402836409 8970922179986507552127307)
              ·
                refine ⟨13456383269979761328190961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8970922179986507552127307 13456383269979761328190961)
                ·
                  refine ⟨10092287452484820996143221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13456383269979761328190961 10092287452484820996143221)
                  ·
                    refine ⟨946151948670451968388427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10092287452484820996143221 946151948670451968388427)
                    ·
                      rfl

theorem cell23_5527873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_5527873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527873 prefixEnd_5527873 := by exact prefixLift 5527873
  have htrace : WordTrace (prefixWord ++ tailWord_5527873) baseStart_5527873 baseEnd_5527873 := by
    simpa [prefixWord, tailWord_5527873, baseEnd_5527873] using wordTrace_append hprefix tailTrace_5527873
  have hstable : (prefixWord ++ tailWord_5527873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527873).length < 2 ^ (prefixWord ++ tailWord_5527873).sum := by decide
  have hdescent : baseEnd_5527873 < baseStart_5527873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527959 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 3, 6]
def baseStart_5527959 : Nat := 118140960795 + 5527959 * 2 ^ 59
def prefixEnd_5527959 : Nat := 4983230072969 + 3 ^ 40 * 5527959 * 2
def baseEnd_5527959 : Nat := 946166668449214189563295

theorem tailTrace_5527959 : CollatzResearch.WordTrace tailWord_5527959 prefixEnd_5527959 946166668449214189563295 := by
  unfold tailWord_5527959
  simp only [CollatzResearch.WordTrace]
  refine ⟨201621228580156118078650931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134414152386770745385767287 201621228580156118078650931)
  ·
    refine ⟨302431842870234177117976397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201621228580156118078650931 302431842870234177117976397)
    ·
      refine ⟨113411941076337816419241149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302431842870234177117976397 113411941076337816419241149)
      ·
        refine ⟨42529477903626681157215431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113411941076337816419241149 42529477903626681157215431)
        ·
          refine ⟨63794216855440021735823147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42529477903626681157215431 63794216855440021735823147)
          ·
            refine ⟨95691325283160032603734721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63794216855440021735823147 95691325283160032603734721)
            ·
              refine ⟨71768493962370024452801041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95691325283160032603734721 71768493962370024452801041)
              ·
                refine ⟨53826370471777518339600781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71768493962370024452801041 53826370471777518339600781)
                ·
                  refine ⟨20184888926916569377350293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53826370471777518339600781 20184888926916569377350293)
                  ·
                    refine ⟨946166668449214189563295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20184888926916569377350293 946166668449214189563295)
                    ·
                      rfl

theorem cell23_5527959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_5527959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527959 prefixEnd_5527959 := by exact prefixLift 5527959
  have htrace : WordTrace (prefixWord ++ tailWord_5527959) baseStart_5527959 baseEnd_5527959 := by
    simpa [prefixWord, tailWord_5527959, baseEnd_5527959] using wordTrace_append hprefix tailTrace_5527959
  have hstable : (prefixWord ++ tailWord_5527959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527959).length < 2 ^ (prefixWord ++ tailWord_5527959).sum := by decide
  have hdescent : baseEnd_5527959 < baseStart_5527959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527960 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 3, 1, 3]
def baseStart_5527960 : Nat := 118140960795 + 5527960 * 2 ^ 59
def prefixEnd_5527960 : Nat := 4983230072969 + 3 ^ 40 * 5527960 * 2
def baseEnd_5527960 : Nat := 2838500518828297064777381

theorem tailTrace_5527960 : CollatzResearch.WordTrace tailWord_5527960 prefixEnd_5527960 2838500518828297064777381 := by
  unfold tailWord_5527960
  simp only [CollatzResearch.WordTrace]
  refine ⟨100810632526576247624718667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134414176702101663499624889 100810632526576247624718667)
  ·
    refine ⟨151215948789864371437078001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100810632526576247624718667 151215948789864371437078001)
    ·
      refine ⟨113411961592398278577808501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151215948789864371437078001 113411961592398278577808501)
      ·
        refine ⟨10632371399287338616669547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113411961592398278577808501 10632371399287338616669547)
        ·
          refine ⟨15948557098931007925004321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10632371399287338616669547 15948557098931007925004321)
          ·
            refine ⟨11961417824198255943753241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15948557098931007925004321 11961417824198255943753241)
            ·
              refine ⟨8971063368148691957814931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11961417824198255943753241 8971063368148691957814931)
              ·
                refine ⟨13456595052223037936722397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8971063368148691957814931 13456595052223037936722397)
                ·
                  refine ⟨5046223144583639226270899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13456595052223037936722397 5046223144583639226270899)
                  ·
                    refine ⟨7569334716875458839406349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5046223144583639226270899 7569334716875458839406349)
                    ·
                      refine ⟨2838500518828297064777381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7569334716875458839406349 2838500518828297064777381)
                      ·
                        rfl

theorem cell23_5527960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_5527960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527960 prefixEnd_5527960 := by exact prefixLift 5527960
  have htrace : WordTrace (prefixWord ++ tailWord_5527960) baseStart_5527960 baseEnd_5527960 := by
    simpa [prefixWord, tailWord_5527960, baseEnd_5527960] using wordTrace_append hprefix tailTrace_5527960
  have hstable : (prefixWord ++ tailWord_5527960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527960).length < 2 ^ (prefixWord ++ tailWord_5527960).sum := by decide
  have hdescent : baseEnd_5527960 < baseStart_5527960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528034 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5528034 : Nat := 118140960795 + 5528034 * 2 ^ 59
def prefixEnd_5528034 : Nat := 4983230072969 + 3 ^ 40 * 5528034 * 2
def baseEnd_5528034 : Nat := 2838538516396729775252041

theorem tailTrace_5528034 : CollatzResearch.WordTrace tailWord_5528034 prefixEnd_5528034 2838538516396729775252041 := by
  unfold tailWord_5528034
  simp only [CollatzResearch.WordTrace]
  refine ⟨50405991013721101471907789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134415976036589603925087437 50405991013721101471907789)
  ·
    refine ⟨18902246630145413051965421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50405991013721101471907789 18902246630145413051965421)
    ·
      refine ⟨7088342486304529894487033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18902246630145413051965421 7088342486304529894487033)
      ·
        refine ⟨5316256864728397420865275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7088342486304529894487033 5316256864728397420865275)
        ·
          refine ⟨7974385297092596131297913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5316256864728397420865275 7974385297092596131297913)
          ·
            refine ⟨5980788972819447098473435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7974385297092596131297913 5980788972819447098473435)
            ·
              refine ⟨8971183459229170647710153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980788972819447098473435 8971183459229170647710153)
              ·
                refine ⟨6728387594421877985782615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8971183459229170647710153 6728387594421877985782615)
                ·
                  refine ⟨10092581391632816978673923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6728387594421877985782615 10092581391632816978673923)
                  ·
                    refine ⟨15138872087449225468010885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10092581391632816978673923 15138872087449225468010885)
                    ·
                      refine ⟨2838538516396729775252041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15138872087449225468010885 2838538516396729775252041)
                      ·
                        rfl

theorem cell23_5528034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5528034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528034 prefixEnd_5528034 := by exact prefixLift 5528034
  have htrace : WordTrace (prefixWord ++ tailWord_5528034) baseStart_5528034 baseEnd_5528034 := by
    simpa [prefixWord, tailWord_5528034, baseEnd_5528034] using wordTrace_append hprefix tailTrace_5528034
  have hstable : (prefixWord ++ tailWord_5528034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528034).length < 2 ^ (prefixWord ++ tailWord_5528034).sum := by decide
  have hdescent : baseEnd_5528034 < baseStart_5528034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528037 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 1, 2, 3]
def baseStart_5528037 : Nat := 118140960795 + 5528037 * 2 ^ 59
def prefixEnd_5528037 : Nat := 4983230072969 + 3 ^ 40 * 5528037 * 2
def baseEnd_5528037 : Nat := 2838540056838693263514527

theorem tailTrace_5528037 : CollatzResearch.WordTrace tailWord_5528037 prefixEnd_5528037 2838540056838693263514527 := by
  unfold tailWord_5528037
  simp only [CollatzResearch.WordTrace]
  refine ⟨201624073473873537399990365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134416048982582358266660243 201624073473873537399990365)
  ·
    refine ⟨75609027552702576524996387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201624073473873537399990365 75609027552702576524996387)
    ·
      refine ⟨113413541329053864787494581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75609027552702576524996387 113413541329053864787494581)
      ·
        refine ⟨10632519499598799823827617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113413541329053864787494581 10632519499598799823827617)
        ·
          refine ⟨7974389624699099867870713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10632519499598799823827617 7974389624699099867870713)
          ·
            refine ⟨5980792218524324900903035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7974389624699099867870713 5980792218524324900903035)
            ·
              refine ⟨8971188327786487351354553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980792218524324900903035 8971188327786487351354553)
              ·
                refine ⟨6728391245839865513515915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8971188327786487351354553 6728391245839865513515915)
                ·
                  refine ⟨10092586868759798270273873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6728391245839865513515915 10092586868759798270273873)
                  ·
                    refine ⟨7569440151569848702705405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10092586868759798270273873 7569440151569848702705405)
                    ·
                      refine ⟨2838540056838693263514527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7569440151569848702705405 2838540056838693263514527)
                      ·
                        rfl

theorem cell23_5528037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_5528037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528037 prefixEnd_5528037 := by exact prefixLift 5528037
  have htrace : WordTrace (prefixWord ++ tailWord_5528037) baseStart_5528037 baseEnd_5528037 := by
    simpa [prefixWord, tailWord_5528037, baseEnd_5528037] using wordTrace_append hprefix tailTrace_5528037
  have hstable : (prefixWord ++ tailWord_5528037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528037).length < 2 ^ (prefixWord ++ tailWord_5528037).sum := by decide
  have hdescent : baseEnd_5528037 < baseStart_5528037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528043 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 3, 3, 2]
def baseStart_5528043 : Nat := 118140960795 + 5528043 * 2 ^ 59
def prefixEnd_5528043 : Nat := 4983230072969 + 3 ^ 40 * 5528043 * 2
def baseEnd_5528043 : Nat := 2838543137722620240039499

theorem tailTrace_5528043 : CollatzResearch.WordTrace tailWord_5528043 prefixEnd_5528043 2838543137722620240039499 := by
  unfold tailWord_5528043
  simp only [CollatzResearch.WordTrace]
  refine ⟨201624292311851800424708783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134416194874567866949805855 201624292311851800424708783)
  ·
    refine ⟨302436438467777700637063175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201624292311851800424708783 302436438467777700637063175)
    ·
      refine ⟨453654657701666550955594763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302436438467777700637063175 453654657701666550955594763)
      ·
        refine ⟨680481986552499826433392145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453654657701666550955594763 680481986552499826433392145)
        ·
          refine ⟨510361489914374869825044109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680481986552499826433392145 510361489914374869825044109)
          ·
            refine ⟨191385558717890576184391541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 510361489914374869825044109 191385558717890576184391541)
            ·
              refine ⟨17942396129802241517286707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191385558717890576184391541 17942396129802241517286707)
              ·
                refine ⟨26913594194703362275930061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17942396129802241517286707 26913594194703362275930061)
                ·
                  refine ⟨10092597823013760853473773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26913594194703362275930061 10092597823013760853473773)
                  ·
                    refine ⟨3784724183630160320052665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10092597823013760853473773 3784724183630160320052665)
                    ·
                      refine ⟨2838543137722620240039499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784724183630160320052665 2838543137722620240039499)
                      ·
                        rfl

theorem cell23_5528043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 3, 2].length) (baseStart_5528043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528043 prefixEnd_5528043 := by exact prefixLift 5528043
  have htrace : WordTrace (prefixWord ++ tailWord_5528043) baseStart_5528043 baseEnd_5528043 := by
    simpa [prefixWord, tailWord_5528043, baseEnd_5528043] using wordTrace_append hprefix tailTrace_5528043
  have hstable : (prefixWord ++ tailWord_5528043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528043).length < 2 ^ (prefixWord ++ tailWord_5528043).sum := by decide
  have hdescent : baseEnd_5528043 < baseStart_5528043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528050 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_5528050 : Nat := 118140960795 + 5528050 * 2 ^ 59
def prefixEnd_5528050 : Nat := 4983230072969 + 3 ^ 40 * 5528050 * 2
def baseEnd_5528050 : Nat := 2838546732087201712651967

theorem tailTrace_5528050 : CollatzResearch.WordTrace tailWord_5528050 prefixEnd_5528050 2838546732087201712651967 := by
  unfold tailWord_5528050
  simp only [CollatzResearch.WordTrace]
  refine ⟨50406136905706610155053401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134416365081884293746809069 50406136905706610155053401)
  ·
    refine ⟨37804602679279957616290051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50406136905706610155053401 37804602679279957616290051)
    ·
      refine ⟨56706904018919936424435077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37804602679279957616290051 56706904018919936424435077)
      ·
        refine ⟨10632544503547488079581577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56706904018919936424435077 10632544503547488079581577)
        ·
          refine ⟨7974408377660616059686183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10632544503547488079581577 7974408377660616059686183)
          ·
            refine ⟨11961612566490924089529275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7974408377660616059686183 11961612566490924089529275)
            ·
              refine ⟨17942418849736386134293913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11961612566490924089529275 17942418849736386134293913)
              ·
                refine ⟨13456814137302289600720435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17942418849736386134293913 13456814137302289600720435)
                ·
                  refine ⟨20185221205953434401080653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13456814137302289600720435 20185221205953434401080653)
                  ·
                    refine ⟨7569457952232537900405245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20185221205953434401080653 7569457952232537900405245)
                    ·
                      refine ⟨2838546732087201712651967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7569457952232537900405245 2838546732087201712651967)
                      ·
                        rfl

theorem cell23_5528050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_5528050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528050 prefixEnd_5528050 := by exact prefixLift 5528050
  have htrace : WordTrace (prefixWord ++ tailWord_5528050) baseStart_5528050 baseEnd_5528050 := by
    simpa [prefixWord, tailWord_5528050, baseEnd_5528050] using wordTrace_append hprefix tailTrace_5528050
  have hstable : (prefixWord ++ tailWord_5528050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528050).length < 2 ^ (prefixWord ++ tailWord_5528050).sum := by decide
  have hdescent : baseEnd_5528050 < baseStart_5528050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528113 : List Nat := [1, 2, 2, 3, 1, 1, 3, 5, 5]
def baseStart_5528113 : Nat := 118140960795 + 5528113 * 2 ^ 59
def prefixEnd_5528113 : Nat := 4983230072969 + 3 ^ 40 * 5528113 * 2
def baseEnd_5528113 : Nat := 315397675707603885129353

theorem tailTrace_5528113 : CollatzResearch.WordTrace tailWord_5528113 prefixEnd_5528113 315397675707603885129353 := by
  unfold tailWord_5528113
  simp only [CollatzResearch.WordTrace]
  refine ⟨201626845421598202379756993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134417896947732134919837995 201626845421598202379756993)
  ·
    refine ⟨151220134066198651784817745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201626845421598202379756993 151220134066198651784817745)
    ·
      refine ⟨113415100549648988838613309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151220134066198651784817745 113415100549648988838613309)
      ·
        refine ⟨42530662706118370814479991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113415100549648988838613309 42530662706118370814479991)
        ·
          refine ⟨63795994059177556221719987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42530662706118370814479991 63795994059177556221719987)
          ·
            refine ⟨95693991088766334332579981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63795994059177556221719987 95693991088766334332579981)
            ·
              refine ⟨35885246658287375374717493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95693991088766334332579981 35885246658287375374717493)
              ·
                refine ⟨3364241874214441441379765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35885246658287375374717493 3364241874214441441379765)
                ·
                  refine ⟨315397675707603885129353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3364241874214441441379765 315397675707603885129353)
                  ·
                    rfl

theorem cell23_5528113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 5].length) (baseStart_5528113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528113 prefixEnd_5528113 := by exact prefixLift 5528113
  have htrace : WordTrace (prefixWord ++ tailWord_5528113) baseStart_5528113 baseEnd_5528113 := by
    simpa [prefixWord, tailWord_5528113, baseEnd_5528113] using wordTrace_append hprefix tailTrace_5528113
  have hstable : (prefixWord ++ tailWord_5528113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528113).length < 2 ^ (prefixWord ++ tailWord_5528113).sum := by decide
  have hdescent : baseEnd_5528113 < baseStart_5528113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528124 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 2, 2, 2]
def baseStart_5528124 : Nat := 118140960795 + 5528124 * 2 ^ 59
def prefixEnd_5528124 : Nat := 4983230072969 + 3 ^ 40 * 5528124 * 2
def baseEnd_5528124 : Nat := 2838584729655634423126627

theorem tailTrace_5528124 : CollatzResearch.WordTrace tailWord_5528124 prefixEnd_5528124 2838584729655634423126627 := by
  unfold tailWord_5528124
  simp only [CollatzResearch.WordTrace]
  refine ⟨100813623312279175629203713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134418164416372234172271617 100813623312279175629203713)
  ·
    refine ⟨75610217484209381721902785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100813623312279175629203713 75610217484209381721902785)
    ·
      refine ⟨56707663113157036291427089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75610217484209381721902785 56707663113157036291427089)
      ·
        refine ⟨42530747334867777218570317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56707663113157036291427089 42530747334867777218570317)
        ·
          refine ⟨15949030250575416456963869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42530747334867777218570317 15949030250575416456963869)
          ·
            refine ⟨5980886343965781171361451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15949030250575416456963869 5980886343965781171361451)
            ·
              refine ⟨8971329515948671757042177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980886343965781171361451 8971329515948671757042177)
              ·
                refine ⟨6728497136961503817781633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8971329515948671757042177 6728497136961503817781633)
                ·
                  refine ⟨5046372852721127863336225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6728497136961503817781633 5046372852721127863336225)
                  ·
                    refine ⟨3784779639540845897502169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5046372852721127863336225 3784779639540845897502169)
                    ·
                      refine ⟨2838584729655634423126627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784779639540845897502169 2838584729655634423126627)
                      ·
                        rfl

theorem cell23_5528124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_5528124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528124 prefixEnd_5528124 := by exact prefixLift 5528124
  have htrace : WordTrace (prefixWord ++ tailWord_5528124) baseStart_5528124 baseEnd_5528124 := by
    simpa [prefixWord, tailWord_5528124, baseEnd_5528124] using wordTrace_append hprefix tailTrace_5528124
  have hstable : (prefixWord ++ tailWord_5528124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528124).length < 2 ^ (prefixWord ++ tailWord_5528124).sum := by decide
  have hdescent : baseEnd_5528124 < baseStart_5528124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528136 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_5528136 : Nat := 118140960795 + 5528136 * 2 ^ 59
def prefixEnd_5528136 : Nat := 4983230072969 + 3 ^ 40 * 5528136 * 2
def baseEnd_5528136 : Nat := 2838590891423488376176571

theorem tailTrace_5528136 : CollatzResearch.WordTrace tailWord_5528136 prefixEnd_5528136 2838590891423488376176571 := by
  unfold tailWord_5528136
  simp only [CollatzResearch.WordTrace]
  refine ⟨100813842150257438653922131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134418456200343251538562841 100813842150257438653922131)
  ·
    refine ⟨151220763225386157980883197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100813842150257438653922131 151220763225386157980883197)
    ·
      refine ⟨56707786209519809242831199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151220763225386157980883197 56707786209519809242831199)
      ·
        refine ⟨85061679314279713864246799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56707786209519809242831199 85061679314279713864246799)
        ·
          refine ⟨127592518971419570796370199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85061679314279713864246799 127592518971419570796370199)
          ·
            refine ⟨191388778457129356194555299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127592518971419570796370199 191388778457129356194555299)
            ·
              refine ⟨287083167685694034291832949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191388778457129356194555299 287083167685694034291832949)
              ·
                refine ⟨26914046970533815714859339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287083167685694034291832949 26914046970533815714859339)
                ·
                  refine ⟨40371070455800723572289009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26914046970533815714859339 40371070455800723572289009)
                  ·
                    refine ⟨30278302841850542679216757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40371070455800723572289009 30278302841850542679216757)
                    ·
                      refine ⟨2838590891423488376176571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30278302841850542679216757 2838590891423488376176571)
                      ·
                        rfl

theorem cell23_5528136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_5528136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528136 prefixEnd_5528136 := by exact prefixLift 5528136
  have htrace : WordTrace (prefixWord ++ tailWord_5528136) baseStart_5528136 baseEnd_5528136 := by
    simpa [prefixWord, tailWord_5528136, baseEnd_5528136] using wordTrace_append hprefix tailTrace_5528136
  have hstable : (prefixWord ++ tailWord_5528136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528136).length < 2 ^ (prefixWord ++ tailWord_5528136).sum := by decide
  have hdescent : baseEnd_5528136 < baseStart_5528136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528141 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_5528141 : Nat := 118140960795 + 5528141 * 2 ^ 59
def prefixEnd_5528141 : Nat := 4983230072969 + 3 ^ 40 * 5528141 * 2
def baseEnd_5528141 : Nat := 2838593458826760856614049

theorem tailTrace_5528141 : CollatzResearch.WordTrace tailWord_5528141 prefixEnd_5528141 2838593458826760856614049 := by
  unfold tailWord_5528141
  simp only [CollatzResearch.WordTrace]
  refine ⟨201627866665496763161776277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134418577776997842107850851 201627866665496763161776277)
  ·
    refine ⟨9451306249945160773208263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 201627866665496763161776277 9451306249945160773208263)
    ·
      refine ⟨14176959374917741159812395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9451306249945160773208263 14176959374917741159812395)
      ·
        refine ⟨21265439062376611739718593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14176959374917741159812395 21265439062376611739718593)
        ·
          refine ⟨15949079296782458804788945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21265439062376611739718593 15949079296782458804788945)
          ·
            refine ⟨11961809472586844103591709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15949079296782458804788945 11961809472586844103591709)
            ·
              refine ⟨4485678552220066538846891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11961809472586844103591709 4485678552220066538846891)
              ·
                refine ⟨6728517828330099808270337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485678552220066538846891 6728517828330099808270337)
                ·
                  refine ⟨5046388371247574856202753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6728517828330099808270337 5046388371247574856202753)
                  ·
                    refine ⟨3784791278435681142152065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5046388371247574856202753 3784791278435681142152065)
                    ·
                      refine ⟨2838593458826760856614049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784791278435681142152065 2838593458826760856614049)
                      ·
                        rfl

theorem cell23_5528141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_5528141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528141 prefixEnd_5528141 := by exact prefixLift 5528141
  have htrace : WordTrace (prefixWord ++ tailWord_5528141) baseStart_5528141 baseEnd_5528141 := by
    simpa [prefixWord, tailWord_5528141, baseEnd_5528141] using wordTrace_append hprefix tailTrace_5528141
  have hstable : (prefixWord ++ tailWord_5528141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528141).length < 2 ^ (prefixWord ++ tailWord_5528141).sum := by decide
  have hdescent : baseEnd_5528141 < baseStart_5528141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528163 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 4]
def baseStart_5528163 : Nat := 118140960795 + 5528163 * 2 ^ 59
def prefixEnd_5528163 : Nat := 4983230072969 + 3 ^ 40 * 5528163 * 2
def baseEnd_5528163 : Nat := 2838604755401159770538947

theorem tailTrace_5528163 : CollatzResearch.WordTrace tailWord_5528163 prefixEnd_5528163 2838604755401159770538947 := by
  unfold tailWord_5528163
  simp only [CollatzResearch.WordTrace]
  refine ⟨201628669071417060919077143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134419112714278040612718095 201628669071417060919077143)
  ·
    refine ⟨302443003607125591378615715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201628669071417060919077143 302443003607125591378615715)
    ·
      refine ⟨453664505410688387067923573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302443003607125591378615715 453664505410688387067923573)
      ·
        refine ⟨42531047382252036287617835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 453664505410688387067923573 42531047382252036287617835)
        ·
          refine ⟨63796571073378054431426753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42531047382252036287617835 63796571073378054431426753)
          ·
            refine ⟨47847428305033540823570065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63796571073378054431426753 47847428305033540823570065)
            ·
              refine ⟨35885571228775155617677549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47847428305033540823570065 35885571228775155617677549)
              ·
                refine ⟨13457089210790683356629081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35885571228775155617677549 13457089210790683356629081)
                ·
                  refine ⟨10092816908093012517471811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13457089210790683356629081 10092816908093012517471811)
                  ·
                    refine ⟨15139225362139518776207717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10092816908093012517471811 15139225362139518776207717)
                    ·
                      refine ⟨2838604755401159770538947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15139225362139518776207717 2838604755401159770538947)
                      ·
                        rfl

theorem cell23_5528163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_5528163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528163 prefixEnd_5528163 := by exact prefixLift 5528163
  have htrace : WordTrace (prefixWord ++ tailWord_5528163) baseStart_5528163 baseEnd_5528163 := by
    simpa [prefixWord, tailWord_5528163, baseEnd_5528163] using wordTrace_append hprefix tailTrace_5528163
  have hstable : (prefixWord ++ tailWord_5528163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528163).length < 2 ^ (prefixWord ++ tailWord_5528163).sum := by decide
  have hdescent : baseEnd_5528163 < baseStart_5528163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528183 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 3]
def baseStart_5528183 : Nat := 118140960795 + 5528183 * 2 ^ 59
def prefixEnd_5528183 : Nat := 4983230072969 + 3 ^ 40 * 5528183 * 2
def baseEnd_5528183 : Nat := 2838615025014249692288855

theorem tailTrace_5528183 : CollatzResearch.WordTrace tailWord_5528183 prefixEnd_5528183 2838615025014249692288855 := by
  unfold tailWord_5528183
  simp only [CollatzResearch.WordTrace]
  refine ⟨201629398531344604334805203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134419599020896402889870135 201629398531344604334805203)
  ·
    refine ⟨302444097797016906502207805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201629398531344604334805203 302444097797016906502207805)
    ·
      refine ⟨113416536673881339938327927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302444097797016906502207805 113416536673881339938327927)
      ·
        refine ⟨170124805010822009907491891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113416536673881339938327927 170124805010822009907491891)
        ·
          refine ⟨255187207516233014861237837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170124805010822009907491891 255187207516233014861237837)
          ·
            refine ⟨95695202818587380572964189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255187207516233014861237837 95695202818587380572964189)
            ·
              refine ⟨35885701056970267714861571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95695202818587380572964189 35885701056970267714861571)
              ·
                refine ⟨53828551585455401572292357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35885701056970267714861571 53828551585455401572292357)
                ·
                  refine ⟨10092853422272887794804817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53828551585455401572292357 10092853422272887794804817)
                  ·
                    refine ⟨7569640066704665846103613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10092853422272887794804817 7569640066704665846103613)
                    ·
                      refine ⟨2838615025014249692288855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7569640066704665846103613 2838615025014249692288855)
                      ·
                        rfl

theorem cell23_5528183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_5528183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528183 prefixEnd_5528183 := by exact prefixLift 5528183
  have htrace : WordTrace (prefixWord ++ tailWord_5528183) baseStart_5528183 baseEnd_5528183 := by
    simpa [prefixWord, tailWord_5528183, baseEnd_5528183] using wordTrace_append hprefix tailTrace_5528183
  have hstable : (prefixWord ++ tailWord_5528183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528183).length < 2 ^ (prefixWord ++ tailWord_5528183).sum := by decide
  have hdescent : baseEnd_5528183 < baseStart_5528183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528270 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_5528270 : Nat := 118140960795 + 5528270 * 2 ^ 59
def prefixEnd_5528270 : Nat := 4983230072969 + 3 ^ 40 * 5528270 * 2
def baseEnd_5528270 : Nat := 2838659697831190851900955

theorem tailTrace_5528270 : CollatzResearch.WordTrace tailWord_5528270 prefixEnd_5528270 2838659697831190851900955 := by
  unfold tailWord_5528270
  simp only [CollatzResearch.WordTrace]
  refine ⟨25204071460253677274152783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134421714454686278795481509 25204071460253677274152783)
  ·
    refine ⟨37806107190380515911229175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25204071460253677274152783 37806107190380515911229175)
    ·
      refine ⟨56709160785570773866843763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37806107190380515911229175 56709160785570773866843763)
      ·
        refine ⟨85063741178356160800265645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56709160785570773866843763 85063741178356160800265645)
        ·
          refine ⟨31898902941883560300099617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85063741178356160800265645 31898902941883560300099617)
          ·
            refine ⟨23924177206412670225074713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31898902941883560300099617 23924177206412670225074713)
            ·
              refine ⟨17943132904809502668806035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23924177206412670225074713 17943132904809502668806035)
              ·
                refine ⟨26914699357214254003209053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17943132904809502668806035 26914699357214254003209053)
                ·
                  refine ⟨10093012258955345251203395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26914699357214254003209053 10093012258955345251203395)
                  ·
                    refine ⟨15139518388433017876805093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10093012258955345251203395 15139518388433017876805093)
                    ·
                      refine ⟨2838659697831190851900955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15139518388433017876805093 2838659697831190851900955)
                      ·
                        rfl

theorem cell23_5528270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_5528270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528270 prefixEnd_5528270 := by exact prefixLift 5528270
  have htrace : WordTrace (prefixWord ++ tailWord_5528270) baseStart_5528270 baseEnd_5528270 := by
    simpa [prefixWord, tailWord_5528270, baseEnd_5528270] using wordTrace_append hprefix tailTrace_5528270
  have hstable : (prefixWord ++ tailWord_5528270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528270).length < 2 ^ (prefixWord ++ tailWord_5528270).sum := by decide
  have hdescent : baseEnd_5528270 < baseStart_5528270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528284 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 1, 5]
def baseStart_5528284 : Nat := 118140960795 + 5528284 * 2 ^ 59
def prefixEnd_5528284 : Nat := 4983230072969 + 3 ^ 40 * 5528284 * 2
def baseEnd_5528284 : Nat := 946222295520117932375297

theorem tailTrace_5528284 : CollatzResearch.WordTrace tailWord_5528284 prefixEnd_5528284 946222295520117932375297 := by
  unfold tailWord_5528284
  simp only [CollatzResearch.WordTrace]
  refine ⟨100816541151989349292115953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134422054869319132389487937 100816541151989349292115953)
  ·
    refine ⟨75612405863992011969086965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100816541151989349292115953 75612405863992011969086965)
    ·
      refine ⟨7088663049749251122101903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75612405863992011969086965 7088663049749251122101903)
      ·
        refine ⟨10632994574623876683152855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7088663049749251122101903 10632994574623876683152855)
        ·
          refine ⟨15949491861935815024729283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10632994574623876683152855 15949491861935815024729283)
          ·
            refine ⟨23924237792903722537093925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15949491861935815024729283 23924237792903722537093925)
            ·
              refine ⟨4485794586169447975705111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23924237792903722537093925 4485794586169447975705111)
              ·
                refine ⟨6728691879254171963557667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485794586169447975705111 6728691879254171963557667)
                ·
                  refine ⟨10093037818881257945336501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6728691879254171963557667 10093037818881257945336501)
                  ·
                    refine ⟨946222295520117932375297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10093037818881257945336501 946222295520117932375297)
                    ·
                      rfl

theorem cell23_5528284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_5528284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528284 prefixEnd_5528284 := by exact prefixLift 5528284
  have htrace : WordTrace (prefixWord ++ tailWord_5528284) baseStart_5528284 baseEnd_5528284 := by
    simpa [prefixWord, tailWord_5528284, baseEnd_5528284] using wordTrace_append hprefix tailTrace_5528284
  have hstable : (prefixWord ++ tailWord_5528284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528284).length < 2 ^ (prefixWord ++ tailWord_5528284).sum := by decide
  have hdescent : baseEnd_5528284 < baseStart_5528284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528287 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 1, 1, 4]
def baseStart_5528287 : Nat := 118140960795 + 5528287 * 2 ^ 59
def prefixEnd_5528287 : Nat := 4983230072969 + 3 ^ 40 * 5528287 * 2
def baseEnd_5528287 : Nat := 2838668427002317285388377

theorem tailTrace_5528287 : CollatzResearch.WordTrace tailWord_5528287 prefixEnd_5528287 2838668427002317285388377 := by
  unfold tailWord_5528287
  simp only [CollatzResearch.WordTrace]
  refine ⟨201633191722967830096591115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134422127815311886731060743 201633191722967830096591115)
  ·
    refine ⟨302449787584451745144886673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201633191722967830096591115 302449787584451745144886673)
    ·
      refine ⟨226837340688338808858665005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302449787584451745144886673 226837340688338808858665005)
      ·
        refine ⟨85064002758127053321999377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226837340688338808858665005 85064002758127053321999377)
        ·
          refine ⟨63798002068595289991499533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85064002758127053321999377 63798002068595289991499533)
          ·
            refine ⟨23924250775723233746812325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63798002068595289991499533 23924250775723233746812325)
            ·
              refine ⟨4485797020448106327527311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23924250775723233746812325 4485797020448106327527311)
              ·
                refine ⟨6728695530672159491290967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485797020448106327527311 6728695530672159491290967)
                ·
                  refine ⟨10093043296008239236936451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6728695530672159491290967 10093043296008239236936451)
                  ·
                    refine ⟨15139564944012358855404677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10093043296008239236936451 15139564944012358855404677)
                    ·
                      refine ⟨2838668427002317285388377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15139564944012358855404677 2838668427002317285388377)
                      ·
                        rfl

theorem cell23_5528287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_5528287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528287 prefixEnd_5528287 := by exact prefixLift 5528287
  have htrace : WordTrace (prefixWord ++ tailWord_5528287) baseStart_5528287 baseEnd_5528287 := by
    simpa [prefixWord, tailWord_5528287, baseEnd_5528287] using wordTrace_append hprefix tailTrace_5528287
  have hstable : (prefixWord ++ tailWord_5528287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528287).length < 2 ^ (prefixWord ++ tailWord_5528287).sum := by decide
  have hdescent : baseEnd_5528287 < baseStart_5528287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528293 : List Nat := [1, 3, 1, 4, 1, 3, 10]
def baseStart_5528293 : Nat := 118140960795 + 5528293 * 2 ^ 59
def prefixEnd_5528293 : Nat := 4983230072969 + 3 ^ 40 * 5528293 * 2
def baseEnd_5528293 : Nat := 35045327257854867431029

theorem tailTrace_5528293 : CollatzResearch.WordTrace tailWord_5528293 prefixEnd_5528293 35045327257854867431029 := by
  unfold tailWord_5528293
  simp only [CollatzResearch.WordTrace]
  refine ⟨201633410560946093121309533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134422273707297395414206355 201633410560946093121309533)
  ·
    refine ⟨75612528960354784920491075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201633410560946093121309533 75612528960354784920491075)
    ·
      refine ⟨113418793440532177380736613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75612528960354784920491075 113418793440532177380736613)
      ·
        refine ⟨21266023770099783258888115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113418793440532177380736613 21266023770099783258888115)
        ·
          refine ⟨31899035655149674888332173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21266023770099783258888115 31899035655149674888332173)
          ·
            refine ⟨11962138370681128083124565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31899035655149674888332173 11962138370681128083124565)
            ·
              refine ⟨35045327257854867431029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11962138370681128083124565 35045327257854867431029)
              ·
                rfl

theorem cell23_5528293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 10].length) (baseStart_5528293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528293 prefixEnd_5528293 := by exact prefixLift 5528293
  have htrace : WordTrace (prefixWord ++ tailWord_5528293) baseStart_5528293 baseEnd_5528293 := by
    simpa [prefixWord, tailWord_5528293, baseEnd_5528293] using wordTrace_append hprefix tailTrace_5528293
  have hstable : (prefixWord ++ tailWord_5528293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528293).length < 2 ^ (prefixWord ++ tailWord_5528293).sum := by decide
  have hdescent : baseEnd_5528293 < baseStart_5528293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528304 : List Nat := [2, 1, 1, 1, 3, 1, 3, 6, 1, 2, 2]
def baseStart_5528304 : Nat := 118140960795 + 5528304 * 2 ^ 59
def prefixEnd_5528304 : Nat := 4983230072969 + 3 ^ 40 * 5528304 * 2
def baseEnd_5528304 : Nat := 2838677156173443718875799

theorem tailTrace_5528304 : CollatzResearch.WordTrace tailWord_5528304 prefixEnd_5528304 2838677156173443718875799 := by
  unfold tailWord_5528304
  simp only [CollatzResearch.WordTrace]
  refine ⟨100816905881953120999979983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134422541175937494666639977 100816905881953120999979983)
  ·
    refine ⟨151225358822929681499969975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100816905881953120999979983 151225358822929681499969975)
    ·
      refine ⟨226838038234394522249954963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151225358822929681499969975 226838038234394522249954963)
      ·
        refine ⟨340257057351591783374932445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226838038234394522249954963 340257057351591783374932445)
        ·
          refine ⟨127596396506846918765599667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340257057351591783374932445 127596396506846918765599667)
          ·
            refine ⟨191394594760270378148399501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127596396506846918765599667 191394594760270378148399501)
            ·
              refine ⟨71772973035101391805649813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191394594760270378148399501 71772973035101391805649813)
              ·
                refine ⟨3364358111020377740889835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71772973035101391805649813 3364358111020377740889835)
                ·
                  refine ⟨5046537166530566611334753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3364358111020377740889835 5046537166530566611334753)
                  ·
                    refine ⟨3784902874897924958501065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5046537166530566611334753 3784902874897924958501065)
                    ·
                      refine ⟨2838677156173443718875799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784902874897924958501065 2838677156173443718875799)
                      ·
                        rfl

theorem cell23_5528304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 1, 2, 2].length) (baseStart_5528304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528304 prefixEnd_5528304 := by exact prefixLift 5528304
  have htrace : WordTrace (prefixWord ++ tailWord_5528304) baseStart_5528304 baseEnd_5528304 := by
    simpa [prefixWord, tailWord_5528304, baseEnd_5528304] using wordTrace_append hprefix tailTrace_5528304
  have hstable : (prefixWord ++ tailWord_5528304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528304).length < 2 ^ (prefixWord ++ tailWord_5528304).sum := by decide
  have hdescent : baseEnd_5528304 < baseStart_5528304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528320 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 8, 1, 3]
def baseStart_5528320 : Nat := 118140960795 + 5528320 * 2 ^ 59
def prefixEnd_5528320 : Nat := 4983230072969 + 3 ^ 40 * 5528320 * 2
def baseEnd_5528320 : Nat := 2838685371863915656275725

theorem tailTrace_5528320 : CollatzResearch.WordTrace tailWord_5528320 prefixEnd_5528320 2838685371863915656275725 := by
  unfold tailWord_5528320
  simp only [CollatzResearch.WordTrace]
  refine ⟨100817197665924138366271207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134422930221232184488361609 100817197665924138366271207)
  ·
    refine ⟨151225796498886207549406811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100817197665924138366271207 151225796498886207549406811)
    ·
      refine ⟨226838694748329311324110217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151225796498886207549406811 226838694748329311324110217)
      ·
        refine ⟨170129021061246983493082663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226838694748329311324110217 170129021061246983493082663)
        ·
          refine ⟨255193531591870475239623995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170129021061246983493082663 255193531591870475239623995)
          ·
            refine ⟨382790297387805712859435993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255193531591870475239623995 382790297387805712859435993)
            ·
              refine ⟨287092723040854284644576995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382790297387805712859435993 287092723040854284644576995)
              ·
                refine ⟨430639084561281426966865493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287092723040854284644576995 430639084561281426966865493)
                ·
                  refine ⟨5046551772202516722267955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 430639084561281426966865493 5046551772202516722267955)
                  ·
                    refine ⟨7569827658303775083401933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5046551772202516722267955 7569827658303775083401933)
                    ·
                      refine ⟨2838685371863915656275725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7569827658303775083401933 2838685371863915656275725)
                      ·
                        rfl

theorem cell23_5528320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_5528320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528320 prefixEnd_5528320 := by exact prefixLift 5528320
  have htrace : WordTrace (prefixWord ++ tailWord_5528320) baseStart_5528320 baseEnd_5528320 := by
    simpa [prefixWord, tailWord_5528320, baseEnd_5528320] using wordTrace_append hprefix tailTrace_5528320
  have hstable : (prefixWord ++ tailWord_5528320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528320).length < 2 ^ (prefixWord ++ tailWord_5528320).sum := by decide
  have hdescent : baseEnd_5528320 < baseStart_5528320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528327 : List Nat := [1, 1, 4, 4, 1, 3, 2, 7]
def baseStart_5528327 : Nat := 118140960795 + 5528327 * 2 ^ 59
def prefixEnd_5528327 : Nat := 4983230072969 + 3 ^ 40 * 5528327 * 2
def baseEnd_5528327 : Nat := 105136628378833226995859

theorem tailTrace_5528327 : CollatzResearch.WordTrace tailWord_5528327 prefixEnd_5528327 105136628378833226995859 := by
  unfold tailWord_5528327
  simp only [CollatzResearch.WordTrace]
  refine ⟨201634650642822916928047235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134423100428548611285364823 201634650642822916928047235)
  ·
    refine ⟨302451975964234375392070853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201634650642822916928047235 302451975964234375392070853)
    ·
      refine ⟨56709745493293945386013285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302451975964234375392070853 56709745493293945386013285)
      ·
        refine ⟨10633077279992614759877491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56709745493293945386013285 10633077279992614759877491)
        ·
          refine ⟨15949615919988922139816237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10633077279992614759877491 15949615919988922139816237)
          ·
            refine ⟨5981105969995845802431089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15949615919988922139816237 5981105969995845802431089)
            ·
              refine ⟨4485829477496884351823317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5981105969995845802431089 4485829477496884351823317)
              ·
                refine ⟨105136628378833226995859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4485829477496884351823317 105136628378833226995859)
                ·
                  rfl

theorem cell23_5528327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 7].length) (baseStart_5528327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528327 prefixEnd_5528327 := by exact prefixLift 5528327
  have htrace : WordTrace (prefixWord ++ tailWord_5528327) baseStart_5528327 baseEnd_5528327 := by
    simpa [prefixWord, tailWord_5528327, baseEnd_5528327] using wordTrace_append hprefix tailTrace_5528327
  have hstable : (prefixWord ++ tailWord_5528327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528327).length < 2 ^ (prefixWord ++ tailWord_5528327).sum := by decide
  have hdescent : baseEnd_5528327 < baseStart_5528327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528360 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_5528360 : Nat := 118140960795 + 5528360 * 2 ^ 59
def prefixEnd_5528360 : Nat := 4983230072969 + 3 ^ 40 * 5528360 * 2
def baseEnd_5528360 : Nat := 2838705911090095499775541

theorem tailTrace_5528360 : CollatzResearch.WordTrace tailWord_5528360 prefixEnd_5528360 2838705911090095499775541 := by
  unfold tailWord_5528360
  simp only [CollatzResearch.WordTrace]
  refine ⟨100817927125851681781999267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134423902834468909042665689 100817927125851681781999267)
  ·
    refine ⟨151226890688777522672998901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100817927125851681781999267 151226890688777522672998901)
    ·
      refine ⟨14177521002072892750593647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151226890688777522672998901 14177521002072892750593647)
      ·
        refine ⟨21266281503109339125890471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14177521002072892750593647 21266281503109339125890471)
        ·
          refine ⟨31899422254664008688835707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21266281503109339125890471 31899422254664008688835707)
          ·
            refine ⟨47849133381996013033253561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31899422254664008688835707 47849133381996013033253561)
            ·
              refine ⟨35886850036497009774940171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47849133381996013033253561 35886850036497009774940171)
              ·
                refine ⟨53830275054745514662410257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35886850036497009774940171 53830275054745514662410257)
                ·
                  refine ⟨40372706291059135996807693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53830275054745514662410257 40372706291059135996807693)
                  ·
                    refine ⟨15139764859147175998802885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40372706291059135996807693 15139764859147175998802885)
                    ·
                      refine ⟨2838705911090095499775541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15139764859147175998802885 2838705911090095499775541)
                      ·
                        rfl

theorem cell23_5528360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_5528360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528360 prefixEnd_5528360 := by exact prefixLift 5528360
  have htrace : WordTrace (prefixWord ++ tailWord_5528360) baseStart_5528360 baseEnd_5528360 := by
    simpa [prefixWord, tailWord_5528360, baseEnd_5528360] using wordTrace_append hprefix tailTrace_5528360
  have hstable : (prefixWord ++ tailWord_5528360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528360).length < 2 ^ (prefixWord ++ tailWord_5528360).sum := by decide
  have hdescent : baseEnd_5528360 < baseStart_5528360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528363 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 5]
def baseStart_5528363 : Nat := 118140960795 + 5528363 * 2 ^ 59
def prefixEnd_5528363 : Nat := 4983230072969 + 3 ^ 40 * 5528363 * 2
def baseEnd_5528363 : Nat := 2838707451532058988038027

theorem tailTrace_5528363 : CollatzResearch.WordTrace tailWord_5528363 prefixEnd_5528363 2838707451532058988038027 := by
  unfold tailWord_5528363
  simp only [CollatzResearch.WordTrace]
  refine ⟨201635963670692495076357743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134423975780461663384238495 201635963670692495076357743)
  ·
    refine ⟨302453945506038742614536615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201635963670692495076357743 302453945506038742614536615)
    ·
      refine ⟨453680918259058113921804923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302453945506038742614536615 453680918259058113921804923)
      ·
        refine ⟨680521377388587170882707385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453680918259058113921804923 680521377388587170882707385)
        ·
          refine ⟨510391033041440378162030539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680521377388587170882707385 510391033041440378162030539)
          ·
            refine ⟨765586549562160567243045809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510391033041440378162030539 765586549562160567243045809)
            ·
              refine ⟨574189912171620425432284357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765586549562160567243045809 574189912171620425432284357)
              ·
                refine ⟨107660608532178829768553317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 574189912171620425432284357 107660608532178829768553317)
                ·
                  refine ⟨20186364099783530581603747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107660608532178829768553317 20186364099783530581603747)
                  ·
                    refine ⟨30279546149675295872405621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20186364099783530581603747 30279546149675295872405621)
                    ·
                      refine ⟨2838707451532058988038027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30279546149675295872405621 2838707451532058988038027)
                      ·
                        rfl

theorem cell23_5528363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 5].length) (baseStart_5528363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528363 prefixEnd_5528363 := by exact prefixLift 5528363
  have htrace : WordTrace (prefixWord ++ tailWord_5528363) baseStart_5528363 baseEnd_5528363 := by
    simpa [prefixWord, tailWord_5528363, baseEnd_5528363] using wordTrace_append hprefix tailTrace_5528363
  have hstable : (prefixWord ++ tailWord_5528363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528363).length < 2 ^ (prefixWord ++ tailWord_5528363).sum := by decide
  have hdescent : baseEnd_5528363 < baseStart_5528363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528365 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_5528365 : Nat := 118140960795 + 5528365 * 2 ^ 59
def prefixEnd_5528365 : Nat := 4983230072969 + 3 ^ 40 * 5528365 * 2
def baseEnd_5528365 : Nat := 946236159497789326737673

theorem tailTrace_5528365 : CollatzResearch.WordTrace tailWord_5528365 prefixEnd_5528365 946236159497789326737673 := by
  unfold tailWord_5528365
  simp only [CollatzResearch.WordTrace]
  refine ⟨201636036616685249417930549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134424024411123499611953699 201636036616685249417930549)
  ·
    refine ⟨18903378432814242132930989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201636036616685249417930549 18903378432814242132930989)
    ·
      refine ⟨7088766912305340799849121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18903378432814242132930989 7088766912305340799849121)
      ·
        refine ⟨5316575184229005599886841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7088766912305340799849121 5316575184229005599886841)
        ·
          refine ⟨3987431388171754199915131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5316575184229005599886841 3987431388171754199915131)
          ·
            refine ⟨5981147082257631299872697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3987431388171754199915131 5981147082257631299872697)
            ·
              refine ⟨4485860311693223474904523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5981147082257631299872697 4485860311693223474904523)
              ·
                refine ⟨6728790467539835212356785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485860311693223474904523 6728790467539835212356785)
                ·
                  refine ⟨5046592850654876409267589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6728790467539835212356785 5046592850654876409267589)
                  ·
                    refine ⟨946236159497789326737673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5046592850654876409267589 946236159497789326737673)
                    ·
                      rfl

theorem cell23_5528365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_5528365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528365 prefixEnd_5528365 := by exact prefixLift 5528365
  have htrace : WordTrace (prefixWord ++ tailWord_5528365) baseStart_5528365 baseEnd_5528365 := by
    simpa [prefixWord, tailWord_5528365, baseEnd_5528365] using wordTrace_append hprefix tailTrace_5528365
  have hstable : (prefixWord ++ tailWord_5528365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528365).length < 2 ^ (prefixWord ++ tailWord_5528365).sum := by decide
  have hdescent : baseEnd_5528365 < baseStart_5528365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528371 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 2, 1, 3]
def baseStart_5528371 : Nat := 118140960795 + 5528371 * 2 ^ 59
def prefixEnd_5528371 : Nat := 4983230072969 + 3 ^ 40 * 5528371 * 2
def baseEnd_5528371 : Nat := 2838711559377294956737991

theorem tailTrace_5528371 : CollatzResearch.WordTrace tailWord_5528371 prefixEnd_5528371 2838711559377294956737991 := by
  unfold tailWord_5528371
  simp only [CollatzResearch.WordTrace]
  refine ⟨201636255454663512442648967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134424170303109008295099311 201636255454663512442648967)
  ·
    refine ⟨302454383181995268663973451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201636255454663512442648967 302454383181995268663973451)
    ·
      refine ⟨453681574772992902995960177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302454383181995268663973451 453681574772992902995960177)
      ·
        refine ⟨340261181079744677246970133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453681574772992902995960177 340261181079744677246970133)
        ·
          refine ⟨15949742863113031745951725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 340261181079744677246970133 15949742863113031745951725)
          ·
            refine ⟨5981153573667386904731897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15949742863113031745951725 5981153573667386904731897)
            ·
              refine ⟨4485865180250540178548923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5981153573667386904731897 4485865180250540178548923)
              ·
                refine ⟨6728797770375810267823385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485865180250540178548923 6728797770375810267823385)
                ·
                  refine ⟨5046598327781857700867539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6728797770375810267823385 5046598327781857700867539)
                  ·
                    refine ⟨7569897491672786551301309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5046598327781857700867539 7569897491672786551301309)
                    ·
                      refine ⟨2838711559377294956737991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7569897491672786551301309 2838711559377294956737991)
                      ·
                        rfl

theorem cell23_5528371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 2, 1, 3].length) (baseStart_5528371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528371 prefixEnd_5528371 := by exact prefixLift 5528371
  have htrace : WordTrace (prefixWord ++ tailWord_5528371) baseStart_5528371 baseEnd_5528371 := by
    simpa [prefixWord, tailWord_5528371, baseEnd_5528371] using wordTrace_append hprefix tailTrace_5528371
  have hstable : (prefixWord ++ tailWord_5528371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528371).length < 2 ^ (prefixWord ++ tailWord_5528371).sum := by decide
  have hdescent : baseEnd_5528371 < baseStart_5528371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528502 : List Nat := [5, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_5528502 : Nat := 118140960795 + 5528502 * 2 ^ 59
def prefixEnd_5528502 : Nat := 4983230072969 + 3 ^ 40 * 5528502 * 2
def baseEnd_5528502 : Nat := 315419869482559327133321

theorem tailTrace_5528502 : CollatzResearch.WordTrace tailWord_5528502 prefixEnd_5528502 315419869482559327133321 := by
  unfold tailWord_5528502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12602564588574307613479235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134427355611459281210445173 12602564588574307613479235)
  ·
    refine ⟨18903846882861461420218853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12602564588574307613479235 18903846882861461420218853)
    ·
      refine ⟨3544471290536524016291035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18903846882861461420218853 3544471290536524016291035)
      ·
        refine ⟨5316706935804786024436553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3544471290536524016291035 5316706935804786024436553)
        ·
          refine ⟨3987530201853589518327415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5316706935804786024436553 3987530201853589518327415)
          ·
            refine ⟨5981295302780384277491123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3987530201853589518327415 5981295302780384277491123)
            ·
              refine ⟨8971942954170576416236685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5981295302780384277491123 8971942954170576416236685)
              ·
                refine ⟨3364478607813966156088757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8971942954170576416236685 3364478607813966156088757)
                ·
                  refine ⟨315419869482559327133321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3364478607813966156088757 315419869482559327133321)
                  ·
                    rfl

theorem cell23_5528502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_5528502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528502 prefixEnd_5528502 := by exact prefixLift 5528502
  have htrace : WordTrace (prefixWord ++ tailWord_5528502) baseStart_5528502 baseEnd_5528502 := by
    simpa [prefixWord, tailWord_5528502, baseEnd_5528502] using wordTrace_append hprefix tailTrace_5528502
  have hstable : (prefixWord ++ tailWord_5528502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528502).length < 2 ^ (prefixWord ++ tailWord_5528502).sum := by decide
  have hdescent : baseEnd_5528502 < baseStart_5528502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528541 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 6]
def baseStart_5528541 : Nat := 118140960795 + 5528541 * 2 ^ 59
def prefixEnd_5528541 : Nat := 4983230072969 + 3 ^ 40 * 5528541 * 2
def baseEnd_5528541 : Nat := 315422094565395476845801

theorem tailTrace_5528541 : CollatzResearch.WordTrace tailWord_5528541 prefixEnd_5528541 315422094565395476845801 := by
  unfold tailWord_5528541
  simp only [CollatzResearch.WordTrace]
  refine ⟨201642455864047631476337477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134428303909365087650891651 201642455864047631476337477)
  ·
    refine ⟨37807960474508930901813277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201642455864047631476337477 37807960474508930901813277)
    ·
      refine ⟨14177985177940849088179979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37807960474508930901813277 14177985177940849088179979)
      ·
        refine ⟨21266977766911273632269969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14177985177940849088179979 21266977766911273632269969)
        ·
          refine ⟨15950233325183455224202477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21266977766911273632269969 15950233325183455224202477)
          ·
            refine ⟨5981337496943795709075929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15950233325183455224202477 5981337496943795709075929)
            ·
              refine ⟨4486003122707846781806947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5981337496943795709075929 4486003122707846781806947)
              ·
                refine ⟨6729004684061770172710421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4486003122707846781806947 6729004684061770172710421)
                ·
                  refine ⟨315422094565395476845801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6729004684061770172710421 315422094565395476845801)
                  ·
                    rfl

theorem cell23_5528541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_5528541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528541 prefixEnd_5528541 := by exact prefixLift 5528541
  have htrace : WordTrace (prefixWord ++ tailWord_5528541) baseStart_5528541 baseEnd_5528541 := by
    simpa [prefixWord, tailWord_5528541, baseEnd_5528541] using wordTrace_append hprefix tailTrace_5528541
  have hstable : (prefixWord ++ tailWord_5528541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528541).length < 2 ^ (prefixWord ++ tailWord_5528541).sum := by decide
  have hdescent : baseEnd_5528541 < baseStart_5528541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528554 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 1, 5]
def baseStart_5528554 : Nat := 118140960795 + 5528554 * 2 ^ 59
def prefixEnd_5528554 : Nat := 4983230072969 + 3 ^ 40 * 5528554 * 2
def baseEnd_5528554 : Nat := 946268508779022580249883

theorem tailTrace_5528554 : CollatzResearch.WordTrace tailWord_5528554 prefixEnd_5528554 946268508779022580249883 := by
  unfold tailWord_5528554
  simp only [CollatzResearch.WordTrace]
  refine ⟨50410732503250133674140179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134428620008667023131040477 50410732503250133674140179)
  ·
    refine ⟨75616098754875200511210269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50410732503250133674140179 75616098754875200511210269)
    ·
      refine ⟨28356037033078200191703851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75616098754875200511210269 28356037033078200191703851)
      ·
        refine ⟨42534055549617300287555777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28356037033078200191703851 42534055549617300287555777)
        ·
          refine ⟨31900541662212975215666833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42534055549617300287555777 31900541662212975215666833)
          ·
            refine ⟨23925406246659731411750125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31900541662212975215666833 23925406246659731411750125)
            ·
              refine ⟨8972027342497399279406297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23925406246659731411750125 8972027342497399279406297)
              ·
                refine ⟨6729020506873049459554723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8972027342497399279406297 6729020506873049459554723)
                ·
                  refine ⟨10093530760309574189332085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6729020506873049459554723 10093530760309574189332085)
                  ·
                    refine ⟨946268508779022580249883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10093530760309574189332085 946268508779022580249883)
                    ·
                      rfl

theorem cell23_5528554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_5528554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528554 prefixEnd_5528554 := by exact prefixLift 5528554
  have htrace : WordTrace (prefixWord ++ tailWord_5528554) baseStart_5528554 baseEnd_5528554 := by
    simpa [prefixWord, tailWord_5528554, baseEnd_5528554] using wordTrace_append hprefix tailTrace_5528554
  have hstable : (prefixWord ++ tailWord_5528554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528554).length < 2 ^ (prefixWord ++ tailWord_5528554).sum := by decide
  have hdescent : baseEnd_5528554 < baseStart_5528554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528561 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 2, 3, 2]
def baseStart_5528561 : Nat := 118140960795 + 5528561 * 2 ^ 59
def prefixEnd_5528561 : Nat := 4983230072969 + 3 ^ 40 * 5528561 * 2
def baseEnd_5528561 : Nat := 2838809120701649213362117

theorem tailTrace_5528561 : CollatzResearch.WordTrace tailWord_5528561 prefixEnd_5528561 2838809120701649213362117 := by
  unfold tailWord_5528561
  simp only [CollatzResearch.WordTrace]
  refine ⟨201643185323975174892065537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134428790215983449928043691 201643185323975174892065537)
  ·
    refine ⟨151232388992981381169049153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201643185323975174892065537 151232388992981381169049153)
    ·
      refine ⟨113424291744736035876786865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151232388992981381169049153 113424291744736035876786865)
      ·
        refine ⟨85068218808552026907590149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113424291744736035876786865 85068218808552026907590149)
        ·
          refine ⟨15950291026603505045173153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85068218808552026907590149 15950291026603505045173153)
          ·
            refine ⟨11962718269952628783879865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15950291026603505045173153 11962718269952628783879865)
            ·
              refine ⟨8972038702464471587909899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11962718269952628783879865 8972038702464471587909899)
              ·
                refine ⟨13458058053696707381864849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8972038702464471587909899 13458058053696707381864849)
                ·
                  refine ⟨10093543540272530536398637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13458058053696707381864849 10093543540272530536398637)
                  ·
                    refine ⟨3785078827602198951149489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10093543540272530536398637 3785078827602198951149489)
                    ·
                      refine ⟨2838809120701649213362117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785078827602198951149489 2838809120701649213362117)
                      ·
                        rfl

theorem cell23_5528561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_5528561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528561 prefixEnd_5528561 := by exact prefixLift 5528561
  have htrace : WordTrace (prefixWord ++ tailWord_5528561) baseStart_5528561 baseEnd_5528561 := by
    simpa [prefixWord, tailWord_5528561, baseEnd_5528561] using wordTrace_append hprefix tailTrace_5528561
  have hstable : (prefixWord ++ tailWord_5528561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528561).length < 2 ^ (prefixWord ++ tailWord_5528561).sum := by decide
  have hdescent : baseEnd_5528561 < baseStart_5528561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528580 : List Nat := [2, 3, 2, 16]
def baseStart_5528580 : Nat := 118140960795 + 5528580 * 2 ^ 59
def prefixEnd_5528580 : Nat := 4983230072969 + 3 ^ 40 * 5528580 * 2
def baseEnd_5528580 : Nat := 1298042467688195994067

theorem tailTrace_5528580 : CollatzResearch.WordTrace tailWord_5528580 prefixEnd_5528580 1298042467688195994067 := by
  unfold tailWord_5528580
  simp only [CollatzResearch.WordTrace]
  refine ⟨100821939155453170568503597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134429252207270894091338129 100821939155453170568503597)
  ·
    refine ⟨37808227183294938963188849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100821939155453170568503597 37808227183294938963188849)
    ·
      refine ⟨28356170387471204222391637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37808227183294938963188849 28356170387471204222391637)
      ·
        refine ⟨1298042467688195994067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 28356170387471204222391637 1298042467688195994067)
        ·
          rfl

theorem cell23_5528580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 16].length) (baseStart_5528580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528580 prefixEnd_5528580 := by exact prefixLift 5528580
  have htrace : WordTrace (prefixWord ++ tailWord_5528580) baseStart_5528580 baseEnd_5528580 := by
    simpa [prefixWord, tailWord_5528580, baseEnd_5528580] using wordTrace_append hprefix tailTrace_5528580
  have hstable : (prefixWord ++ tailWord_5528580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528580).length < 2 ^ (prefixWord ++ tailWord_5528580).sum := by decide
  have hdescent : baseEnd_5528580 < baseStart_5528580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528584 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 2, 4]
def baseStart_5528584 : Nat := 118140960795 + 5528584 * 2 ^ 59
def prefixEnd_5528584 : Nat := 4983230072969 + 3 ^ 40 * 5528584 * 2
def baseEnd_5528584 : Nat := 946273643585567541124837

theorem tailTrace_5528584 : CollatzResearch.WordTrace tailWord_5528584 prefixEnd_5528584 946273643585567541124837 := by
  unfold tailWord_5528584
  simp only [CollatzResearch.WordTrace]
  refine ⟨100822012101445924910076403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134429349468594566546768537 100822012101445924910076403)
  ·
    refine ⟨151233018152168887365114605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100822012101445924910076403 151233018152168887365114605)
    ·
      refine ⟨56712381807063332761917977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151233018152168887365114605 56712381807063332761917977)
      ·
        refine ⟨42534286355297499571438483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56712381807063332761917977 42534286355297499571438483)
        ·
          refine ⟨63801429532946249357157725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42534286355297499571438483 63801429532946249357157725)
          ·
            refine ⟨23925536074854843508934147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63801429532946249357157725 23925536074854843508934147)
            ·
              refine ⟨35888304112282265263401221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23925536074854843508934147 35888304112282265263401221)
              ·
                refine ⟨6729057021052924736887729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35888304112282265263401221 6729057021052924736887729)
                ·
                  refine ⟨5046792765789693552665797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6729057021052924736887729 5046792765789693552665797)
                  ·
                    refine ⟨946273643585567541124837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5046792765789693552665797 946273643585567541124837)
                    ·
                      rfl

theorem cell23_5528584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_5528584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528584 prefixEnd_5528584 := by exact prefixLift 5528584
  have htrace : WordTrace (prefixWord ++ tailWord_5528584) baseStart_5528584 baseEnd_5528584 := by
    simpa [prefixWord, tailWord_5528584, baseEnd_5528584] using wordTrace_append hprefix tailTrace_5528584
  have hstable : (prefixWord ++ tailWord_5528584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528584).length < 2 ^ (prefixWord ++ tailWord_5528584).sum := by decide
  have hdescent : baseEnd_5528584 < baseStart_5528584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528597 : List Nat := [1, 3, 2, 1, 4, 1, 3, 8]
def baseStart_5528597 : Nat := 118140960795 + 5528597 * 2 ^ 59
def prefixEnd_5528597 : Nat := 4983230072969 + 3 ^ 40 * 5528597 * 2
def baseEnd_5528597 : Nat := 105141763185378187870813

theorem tailTrace_5528597 : CollatzResearch.WordTrace tailWord_5528597 prefixEnd_5528597 105141763185378187870813 := by
  unfold tailWord_5528597
  simp only [CollatzResearch.WordTrace]
  refine ⟨201644498351844753040376045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134429665567896502026917363 201644498351844753040376045)
  ·
    refine ⟨75616686881941782390141017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201644498351844753040376045 75616686881941782390141017)
    ·
      refine ⟨56712515161456336792605763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75616686881941782390141017 56712515161456336792605763)
      ·
        refine ⟨85068772742184505188908645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56712515161456336792605763 85068772742184505188908645)
        ·
          refine ⟨15950394889159594722920371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85068772742184505188908645 15950394889159594722920371)
          ·
            refine ⟨23925592333739392084380557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15950394889159594722920371 23925592333739392084380557)
            ·
              refine ⟨8972097125152272031642709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23925592333739392084380557 8972097125152272031642709)
              ·
                refine ⟨105141763185378187870813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8972097125152272031642709 105141763185378187870813)
                ·
                  rfl

theorem cell23_5528597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 8].length) (baseStart_5528597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528597 prefixEnd_5528597 := by exact prefixLift 5528597
  have htrace : WordTrace (prefixWord ++ tailWord_5528597) baseStart_5528597 baseEnd_5528597 := by
    simpa [prefixWord, tailWord_5528597, baseEnd_5528597] using wordTrace_append hprefix tailTrace_5528597
  have hstable : (prefixWord ++ tailWord_5528597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528597).length < 2 ^ (prefixWord ++ tailWord_5528597).sum := by decide
  have hdescent : baseEnd_5528597 < baseStart_5528597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528624 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 4, 1, 3]
def baseStart_5528624 : Nat := 118140960795 + 5528624 * 2 ^ 59
def prefixEnd_5528624 : Nat := 4983230072969 + 3 ^ 40 * 5528624 * 2
def baseEnd_5528624 : Nat := 2838841469982882466874327

theorem tailTrace_5528624 : CollatzResearch.WordTrace tailWord_5528624 prefixEnd_5528624 2838841469982882466874327 := by
  unfold tailWord_5528624
  simp only [CollatzResearch.WordTrace]
  refine ⟨100822741561373468325804463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134430322081831291101072617 100822741561373468325804463)
  ·
    refine ⟨151234112342060202488706695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100822741561373468325804463 151234112342060202488706695)
    ·
      refine ⟨226851168513090303733060043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151234112342060202488706695 226851168513090303733060043)
      ·
        refine ⟨340276752769635455599590065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226851168513090303733060043 340276752769635455599590065)
        ·
          refine ⟨255207564577226591699692549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340276752769635455599590065 255207564577226591699692549)
          ·
            refine ⟨47851418358229985943692353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255207564577226591699692549 47851418358229985943692353)
            ·
              refine ⟨35888563768672489457769265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47851418358229985943692353 35888563768672489457769265)
              ·
                refine ⟨26916422826504367093326949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35888563768672489457769265 26916422826504367093326949)
                ·
                  refine ⟨5046829279969568829998803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26916422826504367093326949 5046829279969568829998803)
                  ·
                    refine ⟨7570243919954353244998205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5046829279969568829998803 7570243919954353244998205)
                    ·
                      refine ⟨2838841469982882466874327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7570243919954353244998205 2838841469982882466874327)
                      ·
                        rfl

theorem cell23_5528624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4, 1, 3].length) (baseStart_5528624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528624 prefixEnd_5528624 := by exact prefixLift 5528624
  have htrace : WordTrace (prefixWord ++ tailWord_5528624) baseStart_5528624 baseEnd_5528624 := by
    simpa [prefixWord, tailWord_5528624, baseEnd_5528624] using wordTrace_append hprefix tailTrace_5528624
  have hstable : (prefixWord ++ tailWord_5528624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528624).length < 2 ^ (prefixWord ++ tailWord_5528624).sum := by decide
  have hdescent : baseEnd_5528624 < baseStart_5528624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528628 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_5528628 : Nat := 118140960795 + 5528628 * 2 ^ 59
def prefixEnd_5528628 : Nat := 4983230072969 + 3 ^ 40 * 5528628 * 2
def baseEnd_5528628 : Nat := 2838843523905500451224309

theorem tailTrace_5528628 : CollatzResearch.WordTrace tailWord_5528628 prefixEnd_5528628 2838843523905500451224309 := by
  unfold tailWord_5528628
  simp only [CollatzResearch.WordTrace]
  refine ⟨100822814507366222667377269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134430419343154963556503025 100822814507366222667377269)
  ·
    refine ⟨9452138860065583375066619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100822814507366222667377269 9452138860065583375066619)
    ·
      refine ⟨14178208290098375062599929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9452138860065583375066619 14178208290098375062599929)
      ·
        refine ⟨10633656217573781296949947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14178208290098375062599929 10633656217573781296949947)
        ·
          refine ⟨15950484326360671945424921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10633656217573781296949947 15950484326360671945424921)
          ·
            refine ⟨11962863244770503959068691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15950484326360671945424921 11962863244770503959068691)
            ·
              refine ⟨17944294867155755938603037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11962863244770503959068691 17944294867155755938603037)
              ·
                refine ⟨6729110575183408476976139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17944294867155755938603037 6729110575183408476976139)
                ·
                  refine ⟨10093665862775112715464209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6729110575183408476976139 10093665862775112715464209)
                  ·
                    refine ⟨7570249397081334536598157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10093665862775112715464209 7570249397081334536598157)
                    ·
                      refine ⟨2838843523905500451224309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7570249397081334536598157 2838843523905500451224309)
                      ·
                        rfl

theorem cell23_5528628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_5528628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528628 prefixEnd_5528628 := by exact prefixLift 5528628
  have htrace : WordTrace (prefixWord ++ tailWord_5528628) baseStart_5528628 baseEnd_5528628 := by
    simpa [prefixWord, tailWord_5528628, baseEnd_5528628] using wordTrace_append hprefix tailTrace_5528628
  have hstable : (prefixWord ++ tailWord_5528628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528628).length < 2 ^ (prefixWord ++ tailWord_5528628).sum := by decide
  have hdescent : baseEnd_5528628 < baseStart_5528628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528657 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 2, 6]
def baseStart_5528657 : Nat := 118140960795 + 5528657 * 2 ^ 59
def prefixEnd_5528657 : Nat := 4983230072969 + 3 ^ 40 * 5528657 * 2
def baseEnd_5528657 : Nat := 946286138281493612587225

theorem tailTrace_5528657 : CollatzResearch.WordTrace tailWord_5528657 prefixEnd_5528657 946286138281493612587225 := by
  unfold tailWord_5528657
  simp only [CollatzResearch.WordTrace]
  refine ⟨201646686731627383287560225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134431124487751588858373483 201646686731627383287560225)
  ·
    refine ⟨151235015048720537465670169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201646686731627383287560225 151235015048720537465670169)
    ·
      refine ⟨113426261286540403099252627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151235015048720537465670169 113426261286540403099252627)
      ·
        refine ⟨170139391929810604648878941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113426261286540403099252627 170139391929810604648878941)
        ·
          refine ⟨63802271973678976743329603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170139391929810604648878941 63802271973678976743329603)
          ·
            refine ⟨95703407960518465114994405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63802271973678976743329603 95703407960518465114994405)
            ·
              refine ⟨17944388992597212209061451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95703407960518465114994405 17944388992597212209061451)
              ·
                refine ⟨26916583488895818313592177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17944388992597212209061451 26916583488895818313592177)
                ·
                  refine ⟨20187437616671863735194133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26916583488895818313592177 20187437616671863735194133)
                  ·
                    refine ⟨946286138281493612587225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20187437616671863735194133 946286138281493612587225)
                    ·
                      rfl

theorem cell23_5528657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_5528657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528657 prefixEnd_5528657 := by exact prefixLift 5528657
  have htrace : WordTrace (prefixWord ++ tailWord_5528657) baseStart_5528657 baseEnd_5528657 := by
    simpa [prefixWord, tailWord_5528657, baseEnd_5528657] using wordTrace_append hprefix tailTrace_5528657
  have hstable : (prefixWord ++ tailWord_5528657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528657).length < 2 ^ (prefixWord ++ tailWord_5528657).sum := by decide
  have hdescent : baseEnd_5528657 < baseStart_5528657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528668 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_5528668 : Nat := 118140960795 + 5528668 * 2 ^ 59
def prefixEnd_5528668 : Nat := 4983230072969 + 3 ^ 40 * 5528668 * 2
def baseEnd_5528668 : Nat := 2838864063131680294724125

theorem tailTrace_5528668 : CollatzResearch.WordTrace tailWord_5528668 prefixEnd_5528668 2838864063131680294724125 := by
  unfold tailWord_5528668
  simp only [CollatzResearch.WordTrace]
  refine ⟨100823543967293766083105329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134431391956391688110807105 100823543967293766083105329)
  ·
    refine ⟨75617657975470324562328997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100823543967293766083105329 75617657975470324562328997)
    ·
      refine ⟨14178310870400685855436687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75617657975470324562328997 14178310870400685855436687)
      ·
        refine ⟨21267466305601028783155031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14178310870400685855436687 21267466305601028783155031)
        ·
          refine ⟨31901199458401543174732547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21267466305601028783155031 31901199458401543174732547)
          ·
            refine ⟨47851799187602314762098821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31901199458401543174732547 47851799187602314762098821)
            ·
              refine ⟨8972212347675434017893529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47851799187602314762098821 8972212347675434017893529)
              ·
                refine ⟨6729159260756575513420147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8972212347675434017893529 6729159260756575513420147)
                ·
                  refine ⟨10093738891134863270130221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6729159260756575513420147 10093738891134863270130221)
                  ·
                    refine ⟨3785152084175573726298833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10093738891134863270130221 3785152084175573726298833)
                    ·
                      refine ⟨2838864063131680294724125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785152084175573726298833 2838864063131680294724125)
                      ·
                        rfl

theorem cell23_5528668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_5528668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528668 prefixEnd_5528668 := by exact prefixLift 5528668
  have htrace : WordTrace (prefixWord ++ tailWord_5528668) baseStart_5528668 baseEnd_5528668 := by
    simpa [prefixWord, tailWord_5528668, baseEnd_5528668] using wordTrace_append hprefix tailTrace_5528668
  have hstable : (prefixWord ++ tailWord_5528668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528668).length < 2 ^ (prefixWord ++ tailWord_5528668).sum := by decide
  have hdescent : baseEnd_5528668 < baseStart_5528668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528681 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 4, 2, 2]
def baseStart_5528681 : Nat := 118140960795 + 5528681 * 2 ^ 59
def prefixEnd_5528681 : Nat := 4983230072969 + 3 ^ 40 * 5528681 * 2
def baseEnd_5528681 : Nat := 2838870738380188743861565

theorem tailTrace_5528681 : CollatzResearch.WordTrace tailWord_5528681 prefixEnd_5528681 2838870738380188743861565 := by
  unfold tailWord_5528681
  simp only [CollatzResearch.WordTrace]
  refine ⟨201647562083540435386433897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134431708055693623590955931 201647562083540435386433897)
  ·
    refine ⟨151235671562655326539825423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201647562083540435386433897 151235671562655326539825423)
    ·
      refine ⟨226853507343982989809738135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151235671562655326539825423 226853507343982989809738135)
      ·
        refine ⟨340280261015974484714607203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226853507343982989809738135 340280261015974484714607203)
        ·
          refine ⟨510420391523961727071910805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340280261015974484714607203 510420391523961727071910805)
          ·
            refine ⟨23925955852685705956495819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 510420391523961727071910805 23925955852685705956495819)
            ·
              refine ⟨35888933779028558934743729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23925955852685705956495819 35888933779028558934743729)
              ·
                refine ⟨26916700334271419201057797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35888933779028558934743729 26916700334271419201057797)
                ·
                  refine ⟨5046881312675891100198337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26916700334271419201057797 5046881312675891100198337)
                  ·
                    refine ⟨3785160984506918325148753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5046881312675891100198337 3785160984506918325148753)
                    ·
                      refine ⟨2838870738380188743861565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785160984506918325148753 2838870738380188743861565)
                      ·
                        rfl

theorem cell23_5528681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 2, 2].length) (baseStart_5528681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528681 prefixEnd_5528681 := by exact prefixLift 5528681
  have htrace : WordTrace (prefixWord ++ tailWord_5528681) baseStart_5528681 baseEnd_5528681 := by
    simpa [prefixWord, tailWord_5528681, baseEnd_5528681] using wordTrace_append hprefix tailTrace_5528681
  have hstable : (prefixWord ++ tailWord_5528681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528681).length < 2 ^ (prefixWord ++ tailWord_5528681).sum := by decide
  have hdescent : baseEnd_5528681 < baseStart_5528681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528704 : List Nat := [2, 1, 1, 2, 1, 3, 2, 6, 5]
def baseStart_5528704 : Nat := 118140960795 + 5528704 * 2 ^ 59
def prefixEnd_5528704 : Nat := 4983230072969 + 3 ^ 40 * 5528704 * 2
def baseEnd_5528704 : Nat := 315431394270582461541551

theorem tailTrace_5528704 : CollatzResearch.WordTrace tailWord_5528704 prefixEnd_5528704 315431394270582461541551 := by
  unfold tailWord_5528704
  simp only [CollatzResearch.WordTrace]
  refine ⟨100824200481228555157260583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134432267308304740209680777 100824200481228555157260583)
  ·
    refine ⟨151236300721842832735890875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100824200481228555157260583 151236300721842832735890875)
    ·
      refine ⟨226854451082764249103836313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151236300721842832735890875 226854451082764249103836313)
      ·
        refine ⟨170140838312073186827877235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226854451082764249103836313 170140838312073186827877235)
        ·
          refine ⟨255211257468109780241815853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170140838312073186827877235 255211257468109780241815853)
          ·
            refine ⟨95704221550541167590680945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255211257468109780241815853 95704221550541167590680945)
            ·
              refine ⟨71778166162905875693010709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95704221550541167590680945 71778166162905875693010709)
              ·
                refine ⟨3364601538886212923109877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71778166162905875693010709 3364601538886212923109877)
                ·
                  refine ⟨315431394270582461541551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3364601538886212923109877 315431394270582461541551)
                  ·
                    rfl

theorem cell23_5528704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 5].length) (baseStart_5528704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528704 prefixEnd_5528704 := by exact prefixLift 5528704
  have htrace : WordTrace (prefixWord ++ tailWord_5528704) baseStart_5528704 baseEnd_5528704 := by
    simpa [prefixWord, tailWord_5528704, baseEnd_5528704] using wordTrace_append hprefix tailTrace_5528704
  have hstable : (prefixWord ++ tailWord_5528704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528704).length < 2 ^ (prefixWord ++ tailWord_5528704).sum := by decide
  have hdescent : baseEnd_5528704 < baseStart_5528704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528714 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_5528714 : Nat := 118140960795 + 5528714 * 2 ^ 59
def prefixEnd_5528714 : Nat := 4983230072969 + 3 ^ 40 * 5528714 * 2
def baseEnd_5528714 : Nat := 2838887683241787114748913

theorem tailTrace_5528714 : CollatzResearch.WordTrace tailWord_5528714 prefixEnd_5528714 2838887683241787114748913 := by
  unfold tailWord_5528714
  simp only [CollatzResearch.WordTrace]
  refine ⟨50412191423105220505596299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134432510461613921348256797 50412191423105220505596299)
  ·
    refine ⟨75618287134657830758394449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50412191423105220505596299 75618287134657830758394449)
    ·
      refine ⟨56713715350993373068795837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75618287134657830758394449 56713715350993373068795837)
      ·
        refine ⟨21267643256622514900798439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56713715350993373068795837 21267643256622514900798439)
        ·
          refine ⟨31901464884933772351197659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21267643256622514900798439 31901464884933772351197659)
          ·
            refine ⟨47852197327400658526796489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31901464884933772351197659 47852197327400658526796489)
            ·
              refine ⟨35889147995550493895097367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47852197327400658526796489 35889147995550493895097367)
              ·
                refine ⟨53833721993325740842646051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35889147995550493895097367 53833721993325740842646051)
                ·
                  refine ⟨80750582989988611263969077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53833721993325740842646051 80750582989988611263969077)
                  ·
                    refine ⟨7570367155311432305997101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80750582989988611263969077 7570367155311432305997101)
                    ·
                      refine ⟨2838887683241787114748913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7570367155311432305997101 2838887683241787114748913)
                      ·
                        rfl

theorem cell23_5528714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_5528714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528714 prefixEnd_5528714 := by exact prefixLift 5528714
  have htrace : WordTrace (prefixWord ++ tailWord_5528714) baseStart_5528714 baseEnd_5528714 := by
    simpa [prefixWord, tailWord_5528714, baseEnd_5528714] using wordTrace_append hprefix tailTrace_5528714
  have hstable : (prefixWord ++ tailWord_5528714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528714).length < 2 ^ (prefixWord ++ tailWord_5528714).sum := by decide
  have hdescent : baseEnd_5528714 < baseStart_5528714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528788 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5528788 : Nat := 118140960795 + 5528788 * 2 ^ 59
def prefixEnd_5528788 : Nat := 4983230072969 + 3 ^ 40 * 5528788 * 2
def baseEnd_5528788 : Nat := 2838925680810219825223573

theorem tailTrace_5528788 : CollatzResearch.WordTrace tailWord_5528788 prefixEnd_5528788 2838925680810219825223573 := by
  unfold tailWord_5528788
  simp only [CollatzResearch.WordTrace]
  refine ⟨100825732347076396330289509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134434309796101861773719345 100825732347076396330289509)
  ·
    refine ⟨18904824815076824311929283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100825732347076396330289509 18904824815076824311929283)
    ·
      refine ⟨28357237222615236467893925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18904824815076824311929283 28357237222615236467893925)
      ·
        refine ⟨5316981979240356837730111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28357237222615236467893925 5316981979240356837730111)
        ·
          refine ⟨7975472968860535256595167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5316981979240356837730111 7975472968860535256595167)
          ·
            refine ⟨11963209453290802884892751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7975472968860535256595167 11963209453290802884892751)
            ·
              refine ⟨17944814179936204327339127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11963209453290802884892751 17944814179936204327339127)
              ·
                refine ⟨26917221269904306491008691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17944814179936204327339127 26917221269904306491008691)
                ·
                  refine ⟨40375831904856459736513037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26917221269904306491008691 40375831904856459736513037)
                  ·
                    refine ⟨15140936964321172401192389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40375831904856459736513037 15140936964321172401192389)
                    ·
                      refine ⟨2838925680810219825223573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15140936964321172401192389 2838925680810219825223573)
                      ·
                        rfl

theorem cell23_5528788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5528788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528788 prefixEnd_5528788 := by exact prefixLift 5528788
  have htrace : WordTrace (prefixWord ++ tailWord_5528788) baseStart_5528788 baseEnd_5528788 := by
    simpa [prefixWord, tailWord_5528788, baseEnd_5528788] using wordTrace_append hprefix tailTrace_5528788
  have hstable : (prefixWord ++ tailWord_5528788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528788).length < 2 ^ (prefixWord ++ tailWord_5528788).sum := by decide
  have hdescent : baseEnd_5528788 < baseStart_5528788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528791 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 3]
def baseStart_5528791 : Nat := 118140960795 + 5528791 * 2 ^ 59
def prefixEnd_5528791 : Nat := 4983230072969 + 3 ^ 40 * 5528791 * 2
def baseEnd_5528791 : Nat := 2838927221252183313486059

theorem tailTrace_5528791 : CollatzResearch.WordTrace tailWord_5528791 prefixEnd_5528791 2838927221252183313486059 := by
  unfold tailWord_5528791
  simp only [CollatzResearch.WordTrace]
  refine ⟨201651574113141924172938227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134434382742094616115292151 201651574113141924172938227)
  ·
    refine ⟨302477361169712886259407341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201651574113141924172938227 302477361169712886259407341)
    ·
      refine ⟨113429010438642332347277753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302477361169712886259407341 113429010438642332347277753)
      ·
        refine ⟨85071757828981749260458315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113429010438642332347277753 85071757828981749260458315)
        ·
          refine ⟨127607636743472623890687473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85071757828981749260458315 127607636743472623890687473)
          ·
            refine ⟨95705727557604467918015605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127607636743472623890687473 95705727557604467918015605)
            ·
              refine ⟨8972411958525418867313963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95705727557604467918015605 8972411958525418867313963)
              ·
                refine ⟨13458617937788128300970945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8972411958525418867313963 13458617937788128300970945)
                ·
                  refine ⟨10093963453341096225728209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13458617937788128300970945 10093963453341096225728209)
                  ·
                    refine ⟨7570472590005822169296157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10093963453341096225728209 7570472590005822169296157)
                    ·
                      refine ⟨2838927221252183313486059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7570472590005822169296157 2838927221252183313486059)
                      ·
                        rfl

theorem cell23_5528791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_5528791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528791 prefixEnd_5528791 := by exact prefixLift 5528791
  have htrace : WordTrace (prefixWord ++ tailWord_5528791) baseStart_5528791 baseEnd_5528791 := by
    simpa [prefixWord, tailWord_5528791, baseEnd_5528791] using wordTrace_append hprefix tailTrace_5528791
  have hstable : (prefixWord ++ tailWord_5528791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528791).length < 2 ^ (prefixWord ++ tailWord_5528791).sum := by decide
  have hdescent : baseEnd_5528791 < baseStart_5528791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528811 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 6]
def baseStart_5528811 : Nat := 118140960795 + 5528811 * 2 ^ 59
def prefixEnd_5528811 : Nat := 4983230072969 + 3 ^ 40 * 5528811 * 2
def baseEnd_5528811 : Nat := 315437498985030359470663

theorem tailTrace_5528811 : CollatzResearch.WordTrace tailWord_5528811 prefixEnd_5528811 315437498985030359470663 := by
  unfold tailWord_5528811
  simp only [CollatzResearch.WordTrace]
  refine ⟨201652303573069467588666287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134434869048712978392444191 201652303573069467588666287)
  ·
    refine ⟨302478455359604201382999431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201652303573069467588666287 302478455359604201382999431)
    ·
      refine ⟨453717683039406302074499147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302478455359604201382999431 453717683039406302074499147)
      ·
        refine ⟨680576524559109453111748721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453717683039406302074499147 680576524559109453111748721)
        ·
          refine ⟨510432393419332089833811541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680576524559109453111748721 510432393419332089833811541)
          ·
            refine ⟨5981629610382797927739979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 510432393419332089833811541 5981629610382797927739979)
            ·
              refine ⟨8972444415574196891609969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5981629610382797927739979 8972444415574196891609969)
              ·
                refine ⟨6729333311680647668707477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8972444415574196891609969 6729333311680647668707477)
                ·
                  refine ⟨315437498985030359470663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6729333311680647668707477 315437498985030359470663)
                  ·
                    rfl

theorem cell23_5528811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 6].length) (baseStart_5528811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528811 prefixEnd_5528811 := by exact prefixLift 5528811
  have htrace : WordTrace (prefixWord ++ tailWord_5528811) baseStart_5528811 baseEnd_5528811 := by
    simpa [prefixWord, tailWord_5528811, baseEnd_5528811] using wordTrace_append hprefix tailTrace_5528811
  have hstable : (prefixWord ++ tailWord_5528811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528811).length < 2 ^ (prefixWord ++ tailWord_5528811).sum := by decide
  have hdescent : baseEnd_5528811 < baseStart_5528811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528814 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_5528814 : Nat := 118140960795 + 5528814 * 2 ^ 59
def prefixEnd_5528814 : Nat := 4983230072969 + 3 ^ 40 * 5528814 * 2
def baseEnd_5528814 : Nat := 2838939031307236723498453

theorem tailTrace_5528814 : CollatzResearch.WordTrace tailWord_5528814 prefixEnd_5528814 2838939031307236723498453 := by
  unfold tailWord_5528814
  simp only [CollatzResearch.WordTrace]
  refine ⟨25206551624007324887628187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134434941994705732734016997 25206551624007324887628187)
  ·
    refine ⟨37809827436010987331442281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25206551624007324887628187 37809827436010987331442281)
    ·
      refine ⟨28357370577008240498581711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37809827436010987331442281 28357370577008240498581711)
      ·
        refine ⟨42536055865512360747872567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28357370577008240498581711 42536055865512360747872567)
        ·
          refine ⟨63804083798268541121808851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42536055865512360747872567 63804083798268541121808851)
          ·
            refine ⟨95706125697402811682713277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63804083798268541121808851 95706125697402811682713277)
            ·
              refine ⟨35889797136526054381017479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95706125697402811682713277 35889797136526054381017479)
              ·
                refine ⟨53834695704789081571526219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35889797136526054381017479 53834695704789081571526219)
                ·
                  refine ⟨80752043557183622357289329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53834695704789081571526219 80752043557183622357289329)
                  ·
                    refine ⟨60564032667887716767966997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80752043557183622357289329 60564032667887716767966997)
                    ·
                      refine ⟨2838939031307236723498453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60564032667887716767966997 2838939031307236723498453)
                      ·
                        rfl

theorem cell23_5528814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_5528814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528814 prefixEnd_5528814 := by exact prefixLift 5528814
  have htrace : WordTrace (prefixWord ++ tailWord_5528814) baseStart_5528814 baseEnd_5528814 := by
    simpa [prefixWord, tailWord_5528814, baseEnd_5528814] using wordTrace_append hprefix tailTrace_5528814
  have hstable : (prefixWord ++ tailWord_5528814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528814).length < 2 ^ (prefixWord ++ tailWord_5528814).sum := by decide
  have hdescent : baseEnd_5528814 < baseStart_5528814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528828 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 6]
def baseStart_5528828 : Nat := 118140960795 + 5528828 * 2 ^ 59
def prefixEnd_5528828 : Nat := 4983230072969 + 3 ^ 40 * 5528828 * 2
def baseEnd_5528828 : Nat := 315438468892933296524821

theorem tailTrace_5528828 : CollatzResearch.WordTrace tailWord_5528828 prefixEnd_5528828 315438468892933296524821 := by
  unfold tailWord_5528828
  simp only [CollatzResearch.WordTrace]
  refine ⟨100826461807003939746017569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134435282409338586328023425 100826461807003939746017569)
  ·
    refine ⟨75619846355252954809513177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100826461807003939746017569 75619846355252954809513177)
    ·
      refine ⟨56714884766439716107134883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75619846355252954809513177 56714884766439716107134883)
      ·
        refine ⟨85072327149659574160702325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56714884766439716107134883 85072327149659574160702325)
        ·
          refine ⟨7975530670280585077565843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85072327149659574160702325 7975530670280585077565843)
          ·
            refine ⟨11963296005420877616348765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7975530670280585077565843 11963296005420877616348765)
            ·
              refine ⟨4486236002032829106130787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11963296005420877616348765 4486236002032829106130787)
              ·
                refine ⟨6729354003049243659196181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4486236002032829106130787 6729354003049243659196181)
                ·
                  refine ⟨315438468892933296524821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6729354003049243659196181 315438468892933296524821)
                  ·
                    rfl

theorem cell23_5528828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_5528828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528828 prefixEnd_5528828 := by exact prefixLift 5528828
  have htrace : WordTrace (prefixWord ++ tailWord_5528828) baseStart_5528828 baseEnd_5528828 := by
    simpa [prefixWord, tailWord_5528828, baseEnd_5528828] using wordTrace_append hprefix tailTrace_5528828
  have hstable : (prefixWord ++ tailWord_5528828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528828).length < 2 ^ (prefixWord ++ tailWord_5528828).sum := by decide
  have hdescent : baseEnd_5528828 < baseStart_5528828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528831 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 1, 5, 2]
def baseStart_5528831 : Nat := 118140960795 + 5528831 * 2 ^ 59
def prefixEnd_5528831 : Nat := 4983230072969 + 3 ^ 40 * 5528831 * 2
def baseEnd_5528831 : Nat := 2838947760478363156985875

theorem tailTrace_5528831 : CollatzResearch.WordTrace tailWord_5528831 prefixEnd_5528831 2838947760478363156985875 := by
  unfold tailWord_5528831
  simp only [CollatzResearch.WordTrace]
  refine ⟨201653033032997011004394347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134435355355331340669596231 201653033032997011004394347)
  ·
    refine ⟨302479549549495516506591521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201653033032997011004394347 302479549549495516506591521)
    ·
      refine ⟨226859662162121637379943641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302479549549495516506591521 226859662162121637379943641)
      ·
        refine ⟨170144746621591228034957731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226859662162121637379943641 170144746621591228034957731)
        ·
          refine ⟨255217119932386842052436597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170144746621591228034957731 255217119932386842052436597)
          ·
            refine ⟨23926604993661266442415931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 255217119932386842052436597 23926604993661266442415931)
            ·
              refine ⟨35889907490491899663623897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23926604993661266442415931 35889907490491899663623897)
              ·
                refine ⟨26917430617868924747717923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35889907490491899663623897 26917430617868924747717923)
                ·
                  refine ⟨40376145926803387121576885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26917430617868924747717923 40376145926803387121576885)
                  ·
                    refine ⟨3785263680637817542647833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40376145926803387121576885 3785263680637817542647833)
                    ·
                      refine ⟨2838947760478363156985875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785263680637817542647833 2838947760478363156985875)
                      ·
                        rfl

theorem cell23_5528831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 5, 2].length) (baseStart_5528831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528831 prefixEnd_5528831 := by exact prefixLift 5528831
  have htrace : WordTrace (prefixWord ++ tailWord_5528831) baseStart_5528831 baseEnd_5528831 := by
    simpa [prefixWord, tailWord_5528831, baseEnd_5528831] using wordTrace_append hprefix tailTrace_5528831
  have hstable : (prefixWord ++ tailWord_5528831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528831).length < 2 ^ (prefixWord ++ tailWord_5528831).sum := by decide
  have hdescent : baseEnd_5528831 < baseStart_5528831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528841 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 1, 5]
def baseStart_5528841 : Nat := 118140960795 + 5528841 * 2 ^ 59
def prefixEnd_5528841 : Nat := 4983230072969 + 3 ^ 40 * 5528841 * 2
def baseEnd_5528841 : Nat := 946317631761636039286943

theorem tailTrace_5528841 : CollatzResearch.WordTrace tailWord_5528841 prefixEnd_5528841 946317631761636039286943 := by
  unfold tailWord_5528841
  simp only [CollatzResearch.WordTrace]
  refine ⟨201653397762960782712258377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134435598508640521808172251 201653397762960782712258377)
  ·
    refine ⟨151240048322220587034193783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201653397762960782712258377 151240048322220587034193783)
    ·
      refine ⟨226860072483330880551290675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151240048322220587034193783 226860072483330880551290675)
      ·
        refine ⟨340290108724996320826936013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226860072483330880551290675 340290108724996320826936013)
        ·
          refine ⟨127608790771873620310101005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340290108724996320826936013 127608790771873620310101005)
          ·
            refine ⟨47853296539452607616287877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127608790771873620310101005 47853296539452607616287877)
            ·
              refine ⟨8972493101147363928053977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47853296539452607616287877 8972493101147363928053977)
              ·
                refine ⟨6729369825860522946040483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8972493101147363928053977 6729369825860522946040483)
                ·
                  refine ⟨10094054738790784419060725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6729369825860522946040483 10094054738790784419060725)
                  ·
                    refine ⟨946317631761636039286943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10094054738790784419060725 946317631761636039286943)
                    ·
                      rfl

theorem cell23_5528841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 5].length) (baseStart_5528841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528841 prefixEnd_5528841 := by exact prefixLift 5528841
  have htrace : WordTrace (prefixWord ++ tailWord_5528841) baseStart_5528841 baseEnd_5528841 := by
    simpa [prefixWord, tailWord_5528841, baseEnd_5528841] using wordTrace_append hprefix tailTrace_5528841
  have hstable : (prefixWord ++ tailWord_5528841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528841).length < 2 ^ (prefixWord ++ tailWord_5528841).sum := by decide
  have hdescent : baseEnd_5528841 < baseStart_5528841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528881 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_5528881 : Nat := 118140960795 + 5528881 * 2 ^ 59
def prefixEnd_5528881 : Nat := 4983230072969 + 3 ^ 40 * 5528881 * 2
def baseEnd_5528881 : Nat := 2838973434511087961360645

theorem tailTrace_5528881 : CollatzResearch.WordTrace tailWord_5528881 prefixEnd_5528881 2838973434511087961360645 := by
  unfold tailWord_5528881
  simp only [CollatzResearch.WordTrace]
  refine ⟨201654856682815869543714497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134436571121877246362476331 201654856682815869543714497)
  ·
    refine ⟨151241142512111902157785873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201654856682815869543714497 151241142512111902157785873)
    ·
      refine ⟨113430856884083926618339405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151241142512111902157785873 113430856884083926618339405)
      ·
        refine ⟨42536571331531472481877277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113430856884083926618339405 42536571331531472481877277)
        ·
          refine ⟨15951214249324302180703979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42536571331531472481877277 15951214249324302180703979)
          ·
            refine ⟨23926821373986453271055969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15951214249324302180703979 23926821373986453271055969)
            ·
              refine ⟨17945116030489839953291977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23926821373986453271055969 17945116030489839953291977)
              ·
                refine ⟨13458837022867379964968983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17945116030489839953291977 13458837022867379964968983)
                ·
                  refine ⟨20188255534301069947453475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13458837022867379964968983 20188255534301069947453475)
                  ·
                    refine ⟨30282383301451604921180213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20188255534301069947453475 30282383301451604921180213)
                    ·
                      refine ⟨2838973434511087961360645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30282383301451604921180213 2838973434511087961360645)
                      ·
                        rfl

theorem cell23_5528881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_5528881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528881 prefixEnd_5528881 := by exact prefixLift 5528881
  have htrace : WordTrace (prefixWord ++ tailWord_5528881) baseStart_5528881 baseEnd_5528881 := by
    simpa [prefixWord, tailWord_5528881, baseEnd_5528881] using wordTrace_append hprefix tailTrace_5528881
  have hstable : (prefixWord ++ tailWord_5528881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528881).length < 2 ^ (prefixWord ++ tailWord_5528881).sum := by decide
  have hdescent : baseEnd_5528881 < baseStart_5528881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528981 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_5528981 : Nat := 118140960795 + 5528981 * 2 ^ 59
def prefixEnd_5528981 : Nat := 4983230072969 + 3 ^ 40 * 5528981 * 2
def baseEnd_5528981 : Nat := 2839024782576537570110185

theorem tailTrace_5528981 : CollatzResearch.WordTrace tailWord_5528981 prefixEnd_5528981 2839024782576537570110185 := by
  unfold tailWord_5528981
  simp only [CollatzResearch.WordTrace]
  refine ⟨201658503982453586622354797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134439002654969057748236531 201658503982453586622354797)
  ·
    refine ⟨75621938993420094983383049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201658503982453586622354797 75621938993420094983383049)
    ·
      refine ⟨56716454245065071237537287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75621938993420094983383049 56716454245065071237537287)
      ·
        refine ⟨85074681367597606856305931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56716454245065071237537287 85074681367597606856305931)
        ·
          refine ⟨127612022051396410284458897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85074681367597606856305931 127612022051396410284458897)
          ·
            refine ⟨95709016538547307713344173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127612022051396410284458897 95709016538547307713344173)
            ·
              refine ⟨35890881201955240392504065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95709016538547307713344173 35890881201955240392504065)
              ·
                refine ⟨26918160901466430294378049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35890881201955240392504065 26918160901466430294378049)
                ·
                  refine ⟨20188620676099822720783537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26918160901466430294378049 20188620676099822720783537)
                  ·
                    refine ⟨15141465507074867040587653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20188620676099822720783537 15141465507074867040587653)
                    ·
                      refine ⟨2839024782576537570110185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15141465507074867040587653 2839024782576537570110185)
                      ·
                        rfl

theorem cell23_5528981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_5528981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528981 prefixEnd_5528981 := by exact prefixLift 5528981
  have htrace : WordTrace (prefixWord ++ tailWord_5528981) baseStart_5528981 baseEnd_5528981 := by
    simpa [prefixWord, tailWord_5528981, baseEnd_5528981] using wordTrace_append hprefix tailTrace_5528981
  have hstable : (prefixWord ++ tailWord_5528981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528981).length < 2 ^ (prefixWord ++ tailWord_5528981).sum := by decide
  have hdescent : baseEnd_5528981 < baseStart_5528981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528985 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 4, 2, 2]
def baseStart_5528985 : Nat := 118140960795 + 5528985 * 2 ^ 59
def prefixEnd_5528985 : Nat := 4983230072969 + 3 ^ 40 * 5528985 * 2
def baseEnd_5528985 : Nat := 2839026836499155554460167

theorem tailTrace_5528985 : CollatzResearch.WordTrace tailWord_5528985 prefixEnd_5528985 2839026836499155554460167 := by
  unfold tailWord_5528985
  simp only [CollatzResearch.WordTrace]
  refine ⟨201658649874439095305500409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134439099916292730203666939 201658649874439095305500409)
  ·
    refine ⟨151243987405829321479125307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201658649874439095305500409 151243987405829321479125307)
    ·
      refine ⟨226865981108743982218687961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151243987405829321479125307 226865981108743982218687961)
      ·
        refine ⟨170149485831557986664015971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226865981108743982218687961 170149485831557986664015971)
        ·
          refine ⟨255224228747336979996023957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170149485831557986664015971 255224228747336979996023957)
          ·
            refine ⟨11963635722531420937313623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 255224228747336979996023957 11963635722531420937313623)
            ·
              refine ⟨17945453583797131405970435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11963635722531420937313623 17945453583797131405970435)
              ·
                refine ⟨26918180375695697108955653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17945453583797131405970435 26918180375695697108955653)
                ·
                  refine ⟨5047158820442943207929185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26918180375695697108955653 5047158820442943207929185)
                  ·
                    refine ⟨3785369115332207405946889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5047158820442943207929185 3785369115332207405946889)
                    ·
                      refine ⟨2839026836499155554460167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785369115332207405946889 2839026836499155554460167)
                      ·
                        rfl

theorem cell23_5528985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 2, 2].length) (baseStart_5528985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528985 prefixEnd_5528985 := by exact prefixLift 5528985
  have htrace : WordTrace (prefixWord ++ tailWord_5528985) baseStart_5528985 baseEnd_5528985 := by
    simpa [prefixWord, tailWord_5528985, baseEnd_5528985] using wordTrace_append hprefix tailTrace_5528985
  have hstable : (prefixWord ++ tailWord_5528985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528985).length < 2 ^ (prefixWord ++ tailWord_5528985).sum := by decide
  have hdescent : baseEnd_5528985 < baseStart_5528985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5528991 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 7]
def baseStart_5528991 : Nat := 118140960795 + 5528991 * 2 ^ 59
def prefixEnd_5528991 : Nat := 4983230072969 + 3 ^ 40 * 5528991 * 2
def baseEnd_5528991 : Nat := 315447768598120281220571

theorem tailTrace_5528991 : CollatzResearch.WordTrace tailWord_5528991 prefixEnd_5528991 315447768598120281220571 := by
  unfold tailWord_5528991
  simp only [CollatzResearch.WordTrace]
  refine ⟨201658868712417358330218827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134439245808278238886812551 201658868712417358330218827)
  ·
    refine ⟨302488303068626037495328241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201658868712417358330218827 302488303068626037495328241)
    ·
      refine ⟨226866227301469528121496181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302488303068626037495328241 226866227301469528121496181)
      ·
        refine ⟨21268708809512768261390267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226866227301469528121496181 21268708809512768261390267)
        ·
          refine ⟨31903063214269152392085401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21268708809512768261390267 31903063214269152392085401)
          ·
            refine ⟨23927297410701864294064051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31903063214269152392085401 23927297410701864294064051)
            ·
              refine ⟨35890946116052796441096077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23927297410701864294064051 35890946116052796441096077)
              ·
                refine ⟨13459104793519798665411029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35890946116052796441096077 13459104793519798665411029)
                ·
                  refine ⟨315447768598120281220571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13459104793519798665411029 315447768598120281220571)
                  ·
                    rfl

theorem cell23_5528991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 7].length) (baseStart_5528991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5528991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5528991 prefixEnd_5528991 := by exact prefixLift 5528991
  have htrace : WordTrace (prefixWord ++ tailWord_5528991) baseStart_5528991 baseEnd_5528991 := by
    simpa [prefixWord, tailWord_5528991, baseEnd_5528991] using wordTrace_append hprefix tailTrace_5528991
  have hstable : (prefixWord ++ tailWord_5528991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5528991).length < 2 ^ (prefixWord ++ tailWord_5528991).sum := by decide
  have hdescent : baseEnd_5528991 < baseStart_5528991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5528991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529021 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_5529021 : Nat := 118140960795 + 5529021 * 2 ^ 59
def prefixEnd_5529021 : Nat := 4983230072969 + 3 ^ 40 * 5529021 * 2
def baseEnd_5529021 : Nat := 946348440600905804536667

theorem tailTrace_5529021 : CollatzResearch.WordTrace tailWord_5529021 prefixEnd_5529021 946348440600905804536667 := by
  unfold tailWord_5529021
  simp only [CollatzResearch.WordTrace]
  refine ⟨201659962902308673453810917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134439975268205782302540611 201659962902308673453810917)
  ·
    refine ⟨37811243044182876272589547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201659962902308673453810917 37811243044182876272589547)
    ·
      refine ⟨56716864566274314408884321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37811243044182876272589547 56716864566274314408884321)
      ·
        refine ⟨42537648424705735806663241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56716864566274314408884321 42537648424705735806663241)
        ·
          refine ⟨31903236318529301854997431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42537648424705735806663241 31903236318529301854997431)
          ·
            refine ⟨47854854477793952782496147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31903236318529301854997431 47854854477793952782496147)
            ·
              refine ⟨71782281716690929173744221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47854854477793952782496147 71782281716690929173744221)
              ·
                refine ⟨26918355643759098440154083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71782281716690929173744221 26918355643759098440154083)
                ·
                  refine ⟨40377533465638647660231125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26918355643759098440154083 40377533465638647660231125)
                  ·
                    refine ⟨946348440600905804536667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40377533465638647660231125 946348440600905804536667)
                    ·
                      rfl

theorem cell23_5529021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_5529021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529021 prefixEnd_5529021 := by exact prefixLift 5529021
  have htrace : WordTrace (prefixWord ++ tailWord_5529021) baseStart_5529021 baseEnd_5529021 := by
    simpa [prefixWord, tailWord_5529021, baseEnd_5529021] using wordTrace_append hprefix tailTrace_5529021
  have hstable : (prefixWord ++ tailWord_5529021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529021).length < 2 ^ (prefixWord ++ tailWord_5529021).sum := by decide
  have hdescent : baseEnd_5529021 < baseStart_5529021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529031 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_5529031 : Nat := 118140960795 + 5529031 * 2 ^ 59
def prefixEnd_5529031 : Nat := 4983230072969 + 3 ^ 40 * 5529031 * 2
def baseEnd_5529031 : Nat := 2839050456609262374484955

theorem tailTrace_5529031 : CollatzResearch.WordTrace tailWord_5529031 prefixEnd_5529031 2839050456609262374484955 := by
  unfold tailWord_5529031
  simp only [CollatzResearch.WordTrace]
  refine ⟨201660327632272445161674947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134440218421514963441116631 201660327632272445161674947)
  ·
    refine ⟨302490491448408667742512421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201660327632272445161674947 302490491448408667742512421)
    ·
      refine ⟨56716967146576625201721079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302490491448408667742512421 56716967146576625201721079)
      ·
        refine ⟨85075450719864937802581619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56716967146576625201721079 85075450719864937802581619)
        ·
          refine ⟨127613176079797406703872429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85075450719864937802581619 127613176079797406703872429)
          ·
            refine ⟨47854941029924027513952161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127613176079797406703872429 47854941029924027513952161)
            ·
              refine ⟨35891205772443020635464121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47854941029924027513952161 35891205772443020635464121)
              ·
                refine ⟨26918404329332265476598091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35891205772443020635464121 26918404329332265476598091)
                ·
                  refine ⟨40377606493998398214897137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26918404329332265476598091 40377606493998398214897137)
                  ·
                    refine ⟨30283204870498798661172853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40377606493998398214897137 30283204870498798661172853)
                    ·
                      refine ⟨2839050456609262374484955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30283204870498798661172853 2839050456609262374484955)
                      ·
                        rfl

theorem cell23_5529031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_5529031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529031 prefixEnd_5529031 := by exact prefixLift 5529031
  have htrace : WordTrace (prefixWord ++ tailWord_5529031) baseStart_5529031 baseEnd_5529031 := by
    simpa [prefixWord, tailWord_5529031, baseEnd_5529031] using wordTrace_append hprefix tailTrace_5529031
  have hstable : (prefixWord ++ tailWord_5529031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529031).length < 2 ^ (prefixWord ++ tailWord_5529031).sum := by decide
  have hdescent : baseEnd_5529031 < baseStart_5529031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529071 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 4]
def baseStart_5529071 : Nat := 118140960795 + 5529071 * 2 ^ 59
def prefixEnd_5529071 : Nat := 4983230072969 + 3 ^ 40 * 5529071 * 2
def baseEnd_5529071 : Nat := 2839070995835442217984771

theorem tailTrace_5529071 : CollatzResearch.WordTrace tailWord_5529071 prefixEnd_5529071 2839070995835442217984771 := by
  unfold tailWord_5529071
  simp only [CollatzResearch.WordTrace]
  refine ⟨201661786552127531993131067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134441191034751687995420711 201661786552127531993131067)
  ·
    refine ⟨302492679828191297989696601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201661786552127531993131067 302492679828191297989696601)
    ·
      refine ⟨226869509871143473492272451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302492679828191297989696601 226869509871143473492272451)
      ·
        refine ⟨340304264806715210238408677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226869509871143473492272451 340304264806715210238408677)
        ·
          refine ⟨63807049651259101919701627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340304264806715210238408677 63807049651259101919701627)
          ·
            refine ⟨95710574476888652879552441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63807049651259101919701627 95710574476888652879552441)
            ·
              refine ⟨71782930857666489659664331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95710574476888652879552441 71782930857666489659664331)
              ·
                refine ⟨107674396286499734489496497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71782930857666489659664331 107674396286499734489496497)
                ·
                  refine ⟨80755797214874800867122373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107674396286499734489496497 80755797214874800867122373)
                  ·
                    refine ⟨15141711977789025162585445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80755797214874800867122373 15141711977789025162585445)
                    ·
                      refine ⟨2839070995835442217984771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15141711977789025162585445 2839070995835442217984771)
                      ·
                        rfl

theorem cell23_5529071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_5529071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529071 prefixEnd_5529071 := by exact prefixLift 5529071
  have htrace : WordTrace (prefixWord ++ tailWord_5529071) baseStart_5529071 baseEnd_5529071 := by
    simpa [prefixWord, tailWord_5529071, baseEnd_5529071] using wordTrace_append hprefix tailTrace_5529071
  have hstable : (prefixWord ++ tailWord_5529071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529071).length < 2 ^ (prefixWord ++ tailWord_5529071).sum := by decide
  have hdescent : baseEnd_5529071 < baseStart_5529071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529095 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_5529095 : Nat := 118140960795 + 5529095 * 2 ^ 59
def prefixEnd_5529095 : Nat := 4983230072969 + 3 ^ 40 * 5529095 * 2
def baseEnd_5529095 : Nat := 2839083319371150124084661

theorem tailTrace_5529095 : CollatzResearch.WordTrace tailWord_5529095 prefixEnd_5529095 2839083319371150124084661 := by
  unfold tailWord_5529095
  simp only [CollatzResearch.WordTrace]
  refine ⟨201662661904040584092004739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134441774602693722728003159 201662661904040584092004739)
  ·
    refine ⟨302493992856060876138007109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201662661904040584092004739 302493992856060876138007109)
    ·
      refine ⟨56717623660511414275876333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302493992856060876138007109 56717623660511414275876333)
      ·
        refine ⟨21269108872691780353453625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56717623660511414275876333 21269108872691780353453625)
        ·
          refine ⟨15951831654518835265090219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21269108872691780353453625 15951831654518835265090219)
          ·
            refine ⟨23927747481778252897635329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15951831654518835265090219 23927747481778252897635329)
            ·
              refine ⟨17945810611333689673226497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23927747481778252897635329 17945810611333689673226497)
              ·
                refine ⟨13459357958500267254919873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17945810611333689673226497 13459357958500267254919873)
                ·
                  refine ⟨10094518468875200441189905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13459357958500267254919873 10094518468875200441189905)
                  ·
                    refine ⟨7570888851656400330892429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10094518468875200441189905 7570888851656400330892429)
                    ·
                      refine ⟨2839083319371150124084661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7570888851656400330892429 2839083319371150124084661)
                      ·
                        rfl

theorem cell23_5529095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_5529095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529095 prefixEnd_5529095 := by exact prefixLift 5529095
  have htrace : WordTrace (prefixWord ++ tailWord_5529095) baseStart_5529095 baseEnd_5529095 := by
    simpa [prefixWord, tailWord_5529095, baseEnd_5529095] using wordTrace_append hprefix tailTrace_5529095
  have hstable : (prefixWord ++ tailWord_5529095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529095).length < 2 ^ (prefixWord ++ tailWord_5529095).sum := by decide
  have hdescent : baseEnd_5529095 < baseStart_5529095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529098 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 6]
def baseStart_5529098 : Nat := 118140960795 + 5529098 * 2 ^ 59
def prefixEnd_5529098 : Nat := 4983230072969 + 3 ^ 40 * 5529098 * 2
def baseEnd_5529098 : Nat := 315453873312568179149683

theorem tailTrace_5529098 : CollatzResearch.WordTrace tailWord_5529098 prefixEnd_5529098 315453873312568179149683 := by
  unfold tailWord_5529098
  simp only [CollatzResearch.WordTrace]
  refine ⟨50415692830757428901090987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134441847548686477069575965 50415692830757428901090987)
  ·
    refine ⟨75623539246136143351636481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50415692830757428901090987 75623539246136143351636481)
    ·
      refine ⟨56717654434602107513727361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75623539246136143351636481 56717654434602107513727361)
      ·
        refine ⟨42538240825951580635295521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56717654434602107513727361 42538240825951580635295521)
        ·
          refine ⟨31903680619463685476471641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42538240825951580635295521 31903680619463685476471641)
          ·
            refine ⟨23927760464597764107353731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31903680619463685476471641 23927760464597764107353731)
            ·
              refine ⟨35891640696896646161030597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23927760464597764107353731 35891640696896646161030597)
              ·
                refine ⟨6729682630668121155193237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35891640696896646161030597 6729682630668121155193237)
                ·
                  refine ⟨315453873312568179149683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6729682630668121155193237 315453873312568179149683)
                  ·
                    rfl

theorem cell23_5529098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_5529098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529098 prefixEnd_5529098 := by exact prefixLift 5529098
  have htrace : WordTrace (prefixWord ++ tailWord_5529098) baseStart_5529098 baseEnd_5529098 := by
    simpa [prefixWord, tailWord_5529098, baseEnd_5529098] using wordTrace_append hprefix tailTrace_5529098
  have hstable : (prefixWord ++ tailWord_5529098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529098).length < 2 ^ (prefixWord ++ tailWord_5529098).sum := by decide
  have hdescent : baseEnd_5529098 < baseStart_5529098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529145 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 1, 5]
def baseStart_5529145 : Nat := 118140960795 + 5529145 * 2 ^ 59
def prefixEnd_5529145 : Nat := 4983230072969 + 3 ^ 40 * 5529145 * 2
def baseEnd_5529145 : Nat := 946369664467958309486477

theorem tailTrace_5529145 : CollatzResearch.WordTrace tailWord_5529145 prefixEnd_5529145 946369664467958309486477 := by
  unfold tailWord_5529145
  simp only [CollatzResearch.WordTrace]
  refine ⟨201664485553859442631324889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134442990369239628420883259 201664485553859442631324889)
  ·
    refine ⟨151248364165394581973493667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201664485553859442631324889 151248364165394581973493667)
    ·
      refine ⟨226872546248091872960240501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151248364165394581973493667 226872546248091872960240501)
      ·
        refine ⟨21269301210758613090022547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226872546248091872960240501 21269301210758613090022547)
        ·
          refine ⟨31903951816137919635033821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21269301210758613090022547 31903951816137919635033821)
          ·
            refine ⟨11963981931051719863137683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31903951816137919635033821 11963981931051719863137683)
            ·
              refine ⟨17945972896577579794706525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11963981931051719863137683 17945972896577579794706525)
              ·
                refine ⟨6729739836216592423014947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17945972896577579794706525 6729739836216592423014947)
                ·
                  refine ⟨10094609754324888634522421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6729739836216592423014947 10094609754324888634522421)
                  ·
                    refine ⟨946369664467958309486477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10094609754324888634522421 946369664467958309486477)
                    ·
                      rfl

theorem cell23_5529145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 5].length) (baseStart_5529145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529145 prefixEnd_5529145 := by exact prefixLift 5529145
  have htrace : WordTrace (prefixWord ++ tailWord_5529145) baseStart_5529145 baseEnd_5529145 := by
    simpa [prefixWord, tailWord_5529145, baseEnd_5529145] using wordTrace_append hprefix tailTrace_5529145
  have hstable : (prefixWord ++ tailWord_5529145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529145).length < 2 ^ (prefixWord ++ tailWord_5529145).sum := by decide
  have hdescent : baseEnd_5529145 < baseStart_5529145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529168 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 5]
def baseStart_5529168 : Nat := 118140960795 + 5529168 * 2 ^ 59
def prefixEnd_5529168 : Nat := 4983230072969 + 3 ^ 40 * 5529168 * 2
def baseEnd_5529168 : Nat := 2839120803458928338471825

theorem tailTrace_5529168 : CollatzResearch.WordTrace tailWord_5529168 prefixEnd_5529168 2839120803458928338471825 := by
  unfold tailWord_5529168
  simp only [CollatzResearch.WordTrace]
  refine ⟨100832662216388058779706079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134443549621850745039608105 100832662216388058779706079)
  ·
    refine ⟨151248993324582088169559119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100832662216388058779706079 151248993324582088169559119)
    ·
      refine ⟨226873489986873132254338679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151248993324582088169559119 226873489986873132254338679)
      ·
        refine ⟨340310234980309698381508019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226873489986873132254338679 340310234980309698381508019)
        ·
          refine ⟨510465352470464547572262029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340310234980309698381508019 510465352470464547572262029)
          ·
            refine ⟨191424507176424205339598261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 510465352470464547572262029 191424507176424205339598261)
            ·
              refine ⟨17946047547789769250587337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191424507176424205339598261 17946047547789769250587337)
              ·
                refine ⟨13459535660842326937940503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17946047547789769250587337 13459535660842326937940503)
                ·
                  refine ⟨20189303491263490406910755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13459535660842326937940503 20189303491263490406910755)
                  ·
                    refine ⟨30283955236895235610366133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20189303491263490406910755 30283955236895235610366133)
                    ·
                      refine ⟨2839120803458928338471825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30283955236895235610366133 2839120803458928338471825)
                      ·
                        rfl

theorem cell23_5529168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_5529168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529168 prefixEnd_5529168 := by exact prefixLift 5529168
  have htrace : WordTrace (prefixWord ++ tailWord_5529168) baseStart_5529168 baseEnd_5529168 := by
    simpa [prefixWord, tailWord_5529168, baseEnd_5529168] using wordTrace_append hprefix tailTrace_5529168
  have hstable : (prefixWord ++ tailWord_5529168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529168).length < 2 ^ (prefixWord ++ tailWord_5529168).sum := by decide
  have hdescent : baseEnd_5529168 < baseStart_5529168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529175 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 1, 6]
def baseStart_5529175 : Nat := 118140960795 + 5529175 * 2 ^ 59
def prefixEnd_5529175 : Nat := 4983230072969 + 3 ^ 40 * 5529175 * 2
def baseEnd_5529175 : Nat := 946374799274503270361431

theorem tailTrace_5529175 : CollatzResearch.WordTrace tailWord_5529175 prefixEnd_5529175 946374799274503270361431 := by
  unfold tailWord_5529175
  simp only [CollatzResearch.WordTrace]
  refine ⟨201665579743750757754916979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134443719829167171836611319 201665579743750757754916979)
  ·
    refine ⟨302498369615626136632375469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201665579743750757754916979 302498369615626136632375469)
    ·
      refine ⟨113436888605859801237140801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302498369615626136632375469 113436888605859801237140801)
      ·
        refine ⟨85077666454394850927855601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113436888605859801237140801 85077666454394850927855601)
        ·
          refine ⟨63808249840796138195891701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85077666454394850927855601 63808249840796138195891701)
          ·
            refine ⟨5982023422574637955864847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63808249840796138195891701 5982023422574637955864847)
            ·
              refine ⟨8973035133861956933797271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5982023422574637955864847 8973035133861956933797271)
              ·
                refine ⟨13459552700792935400695907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8973035133861956933797271 13459552700792935400695907)
                ·
                  refine ⟨20189329051189403101043861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13459552700792935400695907 20189329051189403101043861)
                  ·
                    refine ⟨946374799274503270361431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20189329051189403101043861 946374799274503270361431)
                    ·
                      rfl

theorem cell23_5529175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_5529175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529175 prefixEnd_5529175 := by exact prefixLift 5529175
  have htrace : WordTrace (prefixWord ++ tailWord_5529175) baseStart_5529175 baseEnd_5529175 := by
    simpa [prefixWord, tailWord_5529175, baseEnd_5529175] using wordTrace_append hprefix tailTrace_5529175
  have hstable : (prefixWord ++ tailWord_5529175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529175).length < 2 ^ (prefixWord ++ tailWord_5529175).sum := by decide
  have hdescent : baseEnd_5529175 < baseStart_5529175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529188 : List Nat := [2, 3, 1, 1, 2, 4, 1, 9]
def baseStart_5529188 : Nat := 118140960795 + 5529188 * 2 ^ 59
def prefixEnd_5529188 : Nat := 4983230072969 + 3 ^ 40 * 5529188 * 2
def baseEnd_5529188 : Nat := 105153002706371046674879

theorem tailTrace_5529188 : CollatzResearch.WordTrace tailWord_5529188 prefixEnd_5529188 105153002706371046674879 := by
  unfold tailWord_5529188
  simp only [CollatzResearch.WordTrace]
  refine ⟨100833026946351830487570109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134444035928469107316760145 100833026946351830487570109)
  ·
    refine ⟨37812385104881936432838791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100833026946351830487570109 37812385104881936432838791)
    ·
      refine ⟨56718577657322904649258187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37812385104881936432838791 56718577657322904649258187)
      ·
        refine ⟨85077866485984356973887281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56718577657322904649258187 85077866485984356973887281)
        ·
          refine ⟨63808399864488267730415461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85077866485984356973887281 63808399864488267730415461)
          ·
            refine ⟨11964074974591550199452899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63808399864488267730415461 11964074974591550199452899)
            ·
              refine ⟨17946112461887325299179349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11964074974591550199452899 17946112461887325299179349)
              ·
                refine ⟨105153002706371046674879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17946112461887325299179349 105153002706371046674879)
                ·
                  rfl

theorem cell23_5529188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 9].length) (baseStart_5529188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529188 prefixEnd_5529188 := by exact prefixLift 5529188
  have htrace : WordTrace (prefixWord ++ tailWord_5529188) baseStart_5529188 baseEnd_5529188 := by
    simpa [prefixWord, tailWord_5529188, baseEnd_5529188] using wordTrace_append hprefix tailTrace_5529188
  have hstable : (prefixWord ++ tailWord_5529188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529188).length < 2 ^ (prefixWord ++ tailWord_5529188).sum := by decide
  have hdescent : baseEnd_5529188 < baseStart_5529188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529202 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_5529202 : Nat := 118140960795 + 5529202 * 2 ^ 59
def prefixEnd_5529202 : Nat := 4983230072969 + 3 ^ 40 * 5529202 * 2
def baseEnd_5529202 : Nat := 2839138261801181205446669

theorem tailTrace_5529202 : CollatzResearch.WordTrace tailWord_5529202 prefixEnd_5529202 2839138261801181205446669 := by
  unfold tailWord_5529202
  simp only [CollatzResearch.WordTrace]
  refine ⟨50416641128663235341537465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134444376343101960910766573 50416641128663235341537465)
  ·
    refine ⟨37812480846497426506153099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50416641128663235341537465 37812480846497426506153099)
    ·
      refine ⟨56718721269746139759229649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37812480846497426506153099 56718721269746139759229649)
      ·
        refine ⟨42539040952309604819422237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56718721269746139759229649 42539040952309604819422237)
        ·
          refine ⟨15952140357116101807283339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42539040952309604819422237 15952140357116101807283339)
          ·
            refine ⟨23928210535674152710925009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15952140357116101807283339 23928210535674152710925009)
            ·
              refine ⟨17946157901755614533193757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23928210535674152710925009 17946157901755614533193757)
              ·
                refine ⟨6729809213158355449947659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17946157901755614533193757 6729809213158355449947659)
                ·
                  refine ⟨10094713819737533174921489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6729809213158355449947659 10094713819737533174921489)
                  ·
                    refine ⟨7571035364803149881191117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10094713819737533174921489 7571035364803149881191117)
                    ·
                      refine ⟨2839138261801181205446669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7571035364803149881191117 2839138261801181205446669)
                      ·
                        rfl

theorem cell23_5529202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_5529202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529202 prefixEnd_5529202 := by exact prefixLift 5529202
  have htrace : WordTrace (prefixWord ++ tailWord_5529202) baseStart_5529202 baseEnd_5529202 := by
    simpa [prefixWord, tailWord_5529202, baseEnd_5529202] using wordTrace_append hprefix tailTrace_5529202
  have hstable : (prefixWord ++ tailWord_5529202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529202).length < 2 ^ (prefixWord ++ tailWord_5529202).sum := by decide
  have hdescent : baseEnd_5529202 < baseStart_5529202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529205 : List Nat := [1, 3, 4, 2, 1, 3, 9]
def baseStart_5529205 : Nat := 118140960795 + 5529205 * 2 ^ 59
def prefixEnd_5529205 : Nat := 4983230072969 + 3 ^ 40 * 5529205 * 2
def baseEnd_5529205 : Nat := 35051108669668453008755

theorem tailTrace_5529205 : CollatzResearch.WordTrace tailWord_5529205 prefixEnd_5529205 35051108669668453008755 := by
  unfold tailWord_5529205
  simp only [CollatzResearch.WordTrace]
  refine ⟨201666673933642072878509069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134444449289094715252339379 201666673933642072878509069)
  ·
    refine ⟨75625002725115777329440901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201666673933642072878509069 75625002725115777329440901)
    ·
      refine ⟨14179688010959208249270169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75625002725115777329440901 14179688010959208249270169)
      ·
        refine ⟨10634766008219406186952627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14179688010959208249270169 10634766008219406186952627)
        ·
          refine ⟨15952149012329109280428941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10634766008219406186952627 15952149012329109280428941)
          ·
            refine ⟨5982055879623415980160853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15952149012329109280428941 5982055879623415980160853)
            ·
              refine ⟨35051108669668453008755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5982055879623415980160853 35051108669668453008755)
              ·
                rfl

theorem cell23_5529205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 9].length) (baseStart_5529205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529205 prefixEnd_5529205 := by exact prefixLift 5529205
  have htrace : WordTrace (prefixWord ++ tailWord_5529205) baseStart_5529205 baseEnd_5529205 := by
    simpa [prefixWord, tailWord_5529205, baseEnd_5529205] using wordTrace_append hprefix tailTrace_5529205
  have hstable : (prefixWord ++ tailWord_5529205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529205).length < 2 ^ (prefixWord ++ tailWord_5529205).sum := by decide
  have hdescent : baseEnd_5529205 < baseStart_5529205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529216 : List Nat := [2, 1, 1, 2, 1, 4, 5, 2, 1, 2, 2]
def baseStart_5529216 : Nat := 118140960795 + 5529216 * 2 ^ 59
def prefixEnd_5529216 : Nat := 4983230072969 + 3 ^ 40 * 5529216 * 2
def baseEnd_5529216 : Nat := 2839145450530344150671605

theorem tailTrace_5529216 : CollatzResearch.WordTrace tailWord_5529216 prefixEnd_5529216 2839145450530344150671605 := by
  unfold tailWord_5529216
  simp only [CollatzResearch.WordTrace]
  refine ⟨100833537568301110878579751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134444716757734814504773001 100833537568301110878579751)
  ·
    refine ⟨151250306352451666317869627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100833537568301110878579751 151250306352451666317869627)
    ·
      refine ⟨226875459528677499476804441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151250306352451666317869627 226875459528677499476804441)
      ·
        refine ⟨170156594646508124607603331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226875459528677499476804441 170156594646508124607603331)
        ·
          refine ⟨255234891969762186911404997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170156594646508124607603331 255234891969762186911404997)
          ·
            refine ⟨47856542244330410045888437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255234891969762186911404997 47856542244330410045888437)
            ·
              refine ⟨4486550835405975941802041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47856542244330410045888437 4486550835405975941802041)
              ·
                refine ⟨3364913126554481956351531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4486550835405975941802041 3364913126554481956351531)
                ·
                  refine ⟨5047369689831722934527297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3364913126554481956351531 5047369689831722934527297)
                  ·
                    refine ⟨3785527267373792200895473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5047369689831722934527297 3785527267373792200895473)
                    ·
                      refine ⟨2839145450530344150671605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785527267373792200895473 2839145450530344150671605)
                      ·
                        rfl

theorem cell23_5529216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 1, 2, 2].length) (baseStart_5529216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529216 prefixEnd_5529216 := by exact prefixLift 5529216
  have htrace : WordTrace (prefixWord ++ tailWord_5529216) baseStart_5529216 baseEnd_5529216 := by
    simpa [prefixWord, tailWord_5529216, baseEnd_5529216] using wordTrace_append hprefix tailTrace_5529216
  have hstable : (prefixWord ++ tailWord_5529216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529216).length < 2 ^ (prefixWord ++ tailWord_5529216).sum := by decide
  have hdescent : baseEnd_5529216 < baseStart_5529216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529236 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_5529236 : Nat := 118140960795 + 5529236 * 2 ^ 59
def prefixEnd_5529236 : Nat := 4983230072969 + 3 ^ 40 * 5529236 * 2
def baseEnd_5529236 : Nat := 2839155720143434072421513

theorem tailTrace_5529236 : CollatzResearch.WordTrace tailWord_5529236 prefixEnd_5529236 2839155720143434072421513 := by
  unfold tailWord_5529236
  simp only [CollatzResearch.WordTrace]
  refine ⟨100833902298264882586443781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134445203064353176781925041 100833902298264882586443781)
  ·
    refine ⟨18906356680924665484958209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100833902298264882586443781 18906356680924665484958209)
    ·
      refine ⟨14179767510693499113718657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18906356680924665484958209 14179767510693499113718657)
      ·
        refine ⟨10634825633020124335288993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14179767510693499113718657 10634825633020124335288993)
        ·
          refine ⟨7976119224765093251466745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10634825633020124335288993 7976119224765093251466745)
          ·
            refine ⟨5982089418573819938600059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7976119224765093251466745 5982089418573819938600059)
            ·
              refine ⟨8973134127860729907900089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5982089418573819938600059 8973134127860729907900089)
              ·
                refine ⟨6729850595895547430925067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8973134127860729907900089 6729850595895547430925067)
                ·
                  refine ⟨10094775893843321146387601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6729850595895547430925067 10094775893843321146387601)
                  ·
                    refine ⟨7571081920382490859790701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10094775893843321146387601 7571081920382490859790701)
                    ·
                      refine ⟨2839155720143434072421513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7571081920382490859790701 2839155720143434072421513)
                      ·
                        rfl

theorem cell23_5529236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_5529236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529236 prefixEnd_5529236 := by exact prefixLift 5529236
  have htrace : WordTrace (prefixWord ++ tailWord_5529236) baseStart_5529236 baseEnd_5529236 := by
    simpa [prefixWord, tailWord_5529236, baseEnd_5529236] using wordTrace_append hprefix tailTrace_5529236
  have hstable : (prefixWord ++ tailWord_5529236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529236).length < 2 ^ (prefixWord ++ tailWord_5529236).sum := by decide
  have hdescent : baseEnd_5529236 < baseStart_5529236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529272 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 4, 2, 2]
def baseStart_5529272 : Nat := 118140960795 + 5529272 * 2 ^ 59
def prefixEnd_5529272 : Nat := 4983230072969 + 3 ^ 40 * 5529272 * 2
def baseEnd_5529272 : Nat := 2839174205446995931571347

theorem tailTrace_5529272 : CollatzResearch.WordTrace tailWord_5529272 prefixEnd_5529272 2839174205446995931571347 := by
  unfold tailWord_5529272
  simp only [CollatzResearch.WordTrace]
  refine ⟨100834558812199671660599035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134446078416266228880798713 100834558812199671660599035)
  ·
    refine ⟨151251838218299507490898553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100834558812199671660599035 151251838218299507490898553)
    ·
      refine ⟨113438878663724630618173915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151251838218299507490898553 113438878663724630618173915)
      ·
        refine ⟨170158317995586945927260873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113438878663724630618173915 170158317995586945927260873)
        ·
          refine ⟨127618738496690209445445655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170158317995586945927260873 127618738496690209445445655)
          ·
            refine ⟨191428107745035314168168483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127618738496690209445445655 191428107745035314168168483)
            ·
              refine ⟨287142161617552971252252725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191428107745035314168168483 287142161617552971252252725)
              ·
                refine ⟨26919577651645591054898693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287142161617552971252252725 26919577651645591054898693)
                ·
                  refine ⟨5047420809683548322793505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26919577651645591054898693 5047420809683548322793505)
                  ·
                    refine ⟨3785565607262661242095129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5047420809683548322793505 3785565607262661242095129)
                    ·
                      refine ⟨2839174205446995931571347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785565607262661242095129 2839174205446995931571347)
                      ·
                        rfl

theorem cell23_5529272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4, 2, 2].length) (baseStart_5529272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529272 prefixEnd_5529272 := by exact prefixLift 5529272
  have htrace : WordTrace (prefixWord ++ tailWord_5529272) baseStart_5529272 baseEnd_5529272 := by
    simpa [prefixWord, tailWord_5529272, baseEnd_5529272] using wordTrace_append hprefix tailTrace_5529272
  have hstable : (prefixWord ++ tailWord_5529272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529272).length < 2 ^ (prefixWord ++ tailWord_5529272).sum := by decide
  have hdescent : baseEnd_5529272 < baseStart_5529272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529345 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_5529345 : Nat := 118140960795 + 5529345 * 2 ^ 59
def prefixEnd_5529345 : Nat := 4983230072969 + 3 ^ 40 * 5529345 * 2
def baseEnd_5529345 : Nat := 2839211689534774145958511

theorem tailTrace_5529345 : CollatzResearch.WordTrace tailWord_5529345 prefixEnd_5529345 2839211689534774145958511 := by
  unfold tailWord_5529345
  simp only [CollatzResearch.WordTrace]
  refine ⟨201671780153134876788605489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134447853435423251192403659 201671780153134876788605489)
  ·
    refine ⟨151253835114851157591454117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201671780153134876788605489 151253835114851157591454117)
    ·
      refine ⟨28360094084034592048397647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151253835114851157591454117 28360094084034592048397647)
      ·
        refine ⟨42540141126051888072596471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28360094084034592048397647 42540141126051888072596471)
        ·
          refine ⟨63810211689077832108894707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42540141126051888072596471 63810211689077832108894707)
          ·
            refine ⟨95715317533616748163342061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63810211689077832108894707 95715317533616748163342061)
            ·
              refine ⟨35893244075106280561253273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95715317533616748163342061 35893244075106280561253273)
              ·
                refine ⟨26919933056329710420939955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35893244075106280561253273 26919933056329710420939955)
                ·
                  refine ⟨40379899584494565631409933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26919933056329710420939955 40379899584494565631409933)
                  ·
                    refine ⟨15142462344185462111778725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40379899584494565631409933 15142462344185462111778725)
                    ·
                      refine ⟨2839211689534774145958511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15142462344185462111778725 2839211689534774145958511)
                      ·
                        rfl

theorem cell23_5529345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_5529345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529345 prefixEnd_5529345 := by exact prefixLift 5529345
  have htrace : WordTrace (prefixWord ++ tailWord_5529345) baseStart_5529345 baseEnd_5529345 := by
    simpa [prefixWord, tailWord_5529345, baseEnd_5529345] using wordTrace_append hprefix tailTrace_5529345
  have hstable : (prefixWord ++ tailWord_5529345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529345).length < 2 ^ (prefixWord ++ tailWord_5529345).sum := by decide
  have hdescent : baseEnd_5529345 < baseStart_5529345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529402 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 6]
def baseStart_5529402 : Nat := 118140960795 + 5529402 * 2 ^ 59
def prefixEnd_5529402 : Nat := 4983230072969 + 3 ^ 40 * 5529402 * 2
def baseEnd_5529402 : Nat := 315471217548008935882861

theorem tailTrace_5529402 : CollatzResearch.WordTrace tailWord_5529402 prefixEnd_5529402 315471217548008935882861 := by
  unfold tailWord_5529402
  simp only [CollatzResearch.WordTrace]
  refine ⟨50418464778482093880857615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134449239409285583682286973 50418464778482093880857615)
  ·
    refine ⟨75627697167723140821286423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50418464778482093880857615 75627697167723140821286423)
    ·
      refine ⟨113441545751584711231929635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75627697167723140821286423 113441545751584711231929635)
      ·
        refine ⟨170162318627377066847894453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113441545751584711231929635 170162318627377066847894453)
        ·
          refine ⟨15952717371316600016990105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170162318627377066847894453 15952717371316600016990105)
          ·
            refine ⟨11964538028487450012742579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15952717371316600016990105 11964538028487450012742579)
            ·
              refine ⟨17946807042731175019113869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11964538028487450012742579 17946807042731175019113869)
              ·
                refine ⟨6730052641024190632167701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17946807042731175019113869 6730052641024190632167701)
                ·
                  refine ⟨315471217548008935882861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6730052641024190632167701 315471217548008935882861)
                  ·
                    rfl

theorem cell23_5529402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_5529402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529402 prefixEnd_5529402 := by exact prefixLift 5529402
  have htrace : WordTrace (prefixWord ++ tailWord_5529402) baseStart_5529402 baseEnd_5529402 := by
    simpa [prefixWord, tailWord_5529402, baseEnd_5529402] using wordTrace_append hprefix tailTrace_5529402
  have hstable : (prefixWord ++ tailWord_5529402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529402).length < 2 ^ (prefixWord ++ tailWord_5529402).sum := by decide
  have hdescent : baseEnd_5529402 < baseStart_5529402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529439 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 2, 3, 2]
def baseStart_5529439 : Nat := 118140960795 + 5529439 * 2 ^ 59
def prefixEnd_5529439 : Nat := 4983230072969 + 3 ^ 40 * 5529439 * 2
def baseEnd_5529439 : Nat := 2839259956716296778183079

theorem tailTrace_5529439 : CollatzResearch.WordTrace tailWord_5529439 prefixEnd_5529439 2839259956716296778183079 := by
  unfold tailWord_5529439
  simp only [CollatzResearch.WordTrace]
  refine ⟨201675208614794330842527371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134450139076529553895018247 201675208614794330842527371)
  ·
    refine ⟨302512812922191496263791057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201675208614794330842527371 302512812922191496263791057)
    ·
      refine ⟨226884609691643622197843293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302512812922191496263791057 226884609691643622197843293)
      ·
        refine ⟨85081728634366358324191235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226884609691643622197843293 85081728634366358324191235)
        ·
          refine ⟨127622592951549537486286853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85081728634366358324191235 127622592951549537486286853)
          ·
            refine ⟨23929236178415538278678785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127622592951549537486286853 23929236178415538278678785)
            ·
              refine ⟨17946927133811653709009089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23929236178415538278678785 17946927133811653709009089)
              ·
                refine ⟨13460195350358740281756817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17946927133811653709009089 13460195350358740281756817)
                ·
                  refine ⟨10095146512769055211317613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13460195350358740281756817 10095146512769055211317613)
                  ·
                    refine ⟨3785679942288395704244105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10095146512769055211317613 3785679942288395704244105)
                    ·
                      refine ⟨2839259956716296778183079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785679942288395704244105 2839259956716296778183079)
                      ·
                        rfl

theorem cell23_5529439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_5529439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529439 prefixEnd_5529439 := by exact prefixLift 5529439
  have htrace : WordTrace (prefixWord ++ tailWord_5529439) baseStart_5529439 baseEnd_5529439 := by
    simpa [prefixWord, tailWord_5529439, baseEnd_5529439] using wordTrace_append hprefix tailTrace_5529439
  have hstable : (prefixWord ++ tailWord_5529439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529439).length < 2 ^ (prefixWord ++ tailWord_5529439).sum := by decide
  have hdescent : baseEnd_5529439 < baseStart_5529439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529445 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_5529445 : Nat := 118140960795 + 5529445 * 2 ^ 59
def prefixEnd_5529445 : Nat := 4983230072969 + 3 ^ 40 * 5529445 * 2
def baseEnd_5529445 : Nat := 946421012533407918236017

theorem tailTrace_5529445 : CollatzResearch.WordTrace tailWord_5529445 prefixEnd_5529445 946421012533407918236017 := by
  unfold tailWord_5529445
  simp only [CollatzResearch.WordTrace]
  refine ⟨201675427452772593867245789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134450284968515062578163859 201675427452772593867245789)
  ·
    refine ⟨75628285294789722700217171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201675427452772593867245789 75628285294789722700217171)
    ·
      refine ⟨113442427942184584050325757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75628285294789722700217171 113442427942184584050325757)
      ·
        refine ⟨42540910478319219018872159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113442427942184584050325757 42540910478319219018872159)
        ·
          refine ⟨63811365717478828528308239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42540910478319219018872159 63811365717478828528308239)
          ·
            refine ⟨95717048576218242792462359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63811365717478828528308239 95717048576218242792462359)
            ·
              refine ⟨143575572864327364188693539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95717048576218242792462359 143575572864327364188693539)
              ·
                refine ⟨215363359296491046283040309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143575572864327364188693539 215363359296491046283040309)
                ·
                  refine ⟨20190314934046035589035029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215363359296491046283040309 20190314934046035589035029)
                  ·
                    refine ⟨946421012533407918236017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20190314934046035589035029 946421012533407918236017)
                    ·
                      rfl

theorem cell23_5529445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_5529445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529445 prefixEnd_5529445 := by exact prefixLift 5529445
  have htrace : WordTrace (prefixWord ++ tailWord_5529445) baseStart_5529445 baseEnd_5529445 := by
    simpa [prefixWord, tailWord_5529445, baseEnd_5529445] using wordTrace_append hprefix tailTrace_5529445
  have hstable : (prefixWord ++ tailWord_5529445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529445).length < 2 ^ (prefixWord ++ tailWord_5529445).sum := by decide
  have hdescent : baseEnd_5529445 < baseStart_5529445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529452 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_5529452 : Nat := 118140960795 + 5529452 * 2 ^ 59
def prefixEnd_5529452 : Nat := 4983230072969 + 3 ^ 40 * 5529452 * 2
def baseEnd_5529452 : Nat := 2839266631964805227320519

theorem tailTrace_5529452 : CollatzResearch.WordTrace tailWord_5529452 prefixEnd_5529452 2839266631964805227320519 := by
  unfold tailWord_5529452
  simp only [CollatzResearch.WordTrace]
  refine ⟨100837841381873617031375305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134450455175831489375167073 100837841381873617031375305)
  ·
    refine ⟨75628381036405212773531479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100837841381873617031375305 75628381036405212773531479)
    ·
      refine ⟨113442571554607819160297219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75628381036405212773531479 113442571554607819160297219)
      ·
        refine ⟨170163857331911728740445829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113442571554607819160297219 170163857331911728740445829)
        ·
          refine ⟨31905723249733449138833593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170163857331911728740445829 31905723249733449138833593)
          ·
            refine ⟨23929292437300086854125195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31905723249733449138833593 23929292437300086854125195)
            ·
              refine ⟨35893938655950130281187793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23929292437300086854125195 35893938655950130281187793)
              ·
                refine ⟨26920453991962597710890845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35893938655950130281187793 26920453991962597710890845)
                ·
                  refine ⟨10095170246985974141584067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26920453991962597710890845 10095170246985974141584067)
                  ·
                    refine ⟨15142755370478961212376101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10095170246985974141584067 15142755370478961212376101)
                    ·
                      refine ⟨2839266631964805227320519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15142755370478961212376101 2839266631964805227320519)
                      ·
                        rfl

theorem cell23_5529452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_5529452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529452 prefixEnd_5529452 := by exact prefixLift 5529452
  have htrace : WordTrace (prefixWord ++ tailWord_5529452) baseStart_5529452 baseEnd_5529452 := by
    simpa [prefixWord, tailWord_5529452, baseEnd_5529452] using wordTrace_append hprefix tailTrace_5529452
  have hstable : (prefixWord ++ tailWord_5529452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529452).length < 2 ^ (prefixWord ++ tailWord_5529452).sum := by decide
  have hdescent : baseEnd_5529452 < baseStart_5529452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529472 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 3]
def baseStart_5529472 : Nat := 118140960795 + 5529472 * 2 ^ 59
def prefixEnd_5529472 : Nat := 4983230072969 + 3 ^ 40 * 5529472 * 2
def baseEnd_5529472 : Nat := 2839276901577895149070427

theorem tailTrace_5529472 : CollatzResearch.WordTrace tailWord_5529472 prefixEnd_5529472 2839276901577895149070427 := by
  unfold tailWord_5529472
  simp only [CollatzResearch.WordTrace]
  refine ⟨100838206111837388739239335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134450941482449851652319113 100838206111837388739239335)
  ·
    refine ⟨151257309167756083108859003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100838206111837388739239335 151257309167756083108859003)
    ·
      refine ⟨226885963751634124663288505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151257309167756083108859003 226885963751634124663288505)
      ·
        refine ⟨170164472813725593497466379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226885963751634124663288505 170164472813725593497466379)
        ·
          refine ⟨255246709220588390246199569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170164472813725593497466379 255246709220588390246199569)
          ·
            refine ⟨191435031915441292684649677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255246709220588390246199569 191435031915441292684649677)
            ·
              refine ⟨71788136968290484756743629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191435031915441292684649677 71788136968290484756743629)
              ·
                refine ⟨26920551363108931783778861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71788136968290484756743629 26920551363108931783778861)
                ·
                  refine ⟨10095206761165849418917073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26920551363108931783778861 10095206761165849418917073)
                  ·
                    refine ⟨7571405070874387064187805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10095206761165849418917073 7571405070874387064187805)
                    ·
                      refine ⟨2839276901577895149070427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7571405070874387064187805 2839276901577895149070427)
                      ·
                        rfl

theorem cell23_5529472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_5529472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529472 prefixEnd_5529472 := by exact prefixLift 5529472
  have htrace : WordTrace (prefixWord ++ tailWord_5529472) baseStart_5529472 baseEnd_5529472 := by
    simpa [prefixWord, tailWord_5529472, baseEnd_5529472] using wordTrace_append hprefix tailTrace_5529472
  have hstable : (prefixWord ++ tailWord_5529472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529472).length < 2 ^ (prefixWord ++ tailWord_5529472).sum := by decide
  have hdescent : baseEnd_5529472 < baseStart_5529472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529492 : List Nat := [2, 4, 2, 1, 1, 3, 10]
def baseStart_5529492 : Nat := 118140960795 + 5529492 * 2 ^ 59
def prefixEnd_5529492 : Nat := 4983230072969 + 3 ^ 40 * 5529492 * 2
def baseEnd_5529492 : Nat := 35052928039394877417535

theorem tailTrace_5529492 : CollatzResearch.WordTrace tailWord_5529492 prefixEnd_5529492 35052928039394877417535 := by
  unfold tailWord_5529492
  simp only [CollatzResearch.WordTrace]
  refine ⟨100838570841801160447103365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134451427789068213929471153 100838570841801160447103365)
  ·
    refine ⟨18907232032837717583831881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100838570841801160447103365 18907232032837717583831881)
    ·
      refine ⟨14180424024628288187873911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18907232032837717583831881 14180424024628288187873911)
      ·
        refine ⟨21270636036942432281810867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14180424024628288187873911 21270636036942432281810867)
        ·
          refine ⟨31905954055413648422716301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21270636036942432281810867 31905954055413648422716301)
          ·
            refine ⟨11964732770780118158518613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31905954055413648422716301 11964732770780118158518613)
            ·
              refine ⟨35052928039394877417535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11964732770780118158518613 35052928039394877417535)
              ·
                rfl

theorem cell23_5529492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 10].length) (baseStart_5529492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529492 prefixEnd_5529492 := by exact prefixLift 5529492
  have htrace : WordTrace (prefixWord ++ tailWord_5529492) baseStart_5529492 baseEnd_5529492 := by
    simpa [prefixWord, tailWord_5529492, baseEnd_5529492] using wordTrace_append hprefix tailTrace_5529492
  have hstable : (prefixWord ++ tailWord_5529492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529492).length < 2 ^ (prefixWord ++ tailWord_5529492).sum := by decide
  have hdescent : baseEnd_5529492 < baseStart_5529492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529496 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 4, 4]
def baseStart_5529496 : Nat := 118140960795 + 5529496 * 2 ^ 59
def prefixEnd_5529496 : Nat := 4983230072969 + 3 ^ 40 * 5529496 * 2
def baseEnd_5529496 : Nat := 946429741704534351723439

theorem tailTrace_5529496 : CollatzResearch.WordTrace tailWord_5529496 prefixEnd_5529496 946429741704534351723439 := by
  unfold tailWord_5529496
  simp only [CollatzResearch.WordTrace]
  refine ⟨100838643787793914788676171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134451525050391886384901561 100838643787793914788676171)
  ·
    refine ⟨151257965681690872183014257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100838643787793914788676171 151257965681690872183014257)
    ·
      refine ⟨113443474261268154137260693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151257965681690872183014257 113443474261268154137260693)
      ·
        refine ⟨5317662855996944725184095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113443474261268154137260693 5317662855996944725184095)
        ·
          refine ⟨7976494283995417087776143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5317662855996944725184095 7976494283995417087776143)
          ·
            refine ⟨11964741425993125631664215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7976494283995417087776143 11964741425993125631664215)
            ·
              refine ⟨17947112138989688447496323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11964741425993125631664215 17947112138989688447496323)
              ·
                refine ⟨26920668208484532671244485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17947112138989688447496323 26920668208484532671244485)
                ·
                  refine ⟨5047625289090849875858341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26920668208484532671244485 5047625289090849875858341)
                  ·
                    refine ⟨946429741704534351723439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5047625289090849875858341 946429741704534351723439)
                    ·
                      rfl

theorem cell23_5529496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_5529496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529496 prefixEnd_5529496 := by exact prefixLift 5529496
  have htrace : WordTrace (prefixWord ++ tailWord_5529496) baseStart_5529496 baseEnd_5529496 := by
    simpa [prefixWord, tailWord_5529496, baseEnd_5529496] using wordTrace_append hprefix tailTrace_5529496
  have hstable : (prefixWord ++ tailWord_5529496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529496).length < 2 ^ (prefixWord ++ tailWord_5529496).sum := by decide
  have hdescent : baseEnd_5529496 < baseStart_5529496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529503 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 3, 2, 2]
def baseStart_5529503 : Nat := 118140960795 + 5529503 * 2 ^ 59
def prefixEnd_5529503 : Nat := 4983230072969 + 3 ^ 40 * 5529503 * 2
def baseEnd_5529503 : Nat := 2839292819478184527782785

theorem tailTrace_5529503 : CollatzResearch.WordTrace tailWord_5529503 prefixEnd_5529503 2839292819478184527782785 := by
  unfold tailWord_5529503
  simp only [CollatzResearch.WordTrace]
  refine ⟨201677542886562469772857163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134451695257708313181904775 201677542886562469772857163)
  ·
    refine ⟨302516314329843704659285745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201677542886562469772857163 302516314329843704659285745)
    ·
      refine ⟨226887235747382778494464309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302516314329843704659285745 226887235747382778494464309)
      ·
        refine ⟨21270678351317135483856029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226887235747382778494464309 21270678351317135483856029)
        ·
          refine ⟨7976504381743925806446011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21270678351317135483856029 7976504381743925806446011)
          ·
            refine ⟨11964756572615888709669017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7976504381743925806446011 11964756572615888709669017)
            ·
              refine ⟨8973567429461916532251763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11964756572615888709669017 8973567429461916532251763)
              ·
                refine ⟨13460351144192874798377645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8973567429461916532251763 13460351144192874798377645)
                ·
                  refine ⟨5047631679072328049391617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13460351144192874798377645 5047631679072328049391617)
                  ·
                    refine ⟨3785723759304246037043713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5047631679072328049391617 3785723759304246037043713)
                    ·
                      refine ⟨2839292819478184527782785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785723759304246037043713 2839292819478184527782785)
                      ·
                        rfl

theorem cell23_5529503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_5529503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529503 prefixEnd_5529503 := by exact prefixLift 5529503
  have htrace : WordTrace (prefixWord ++ tailWord_5529503) baseStart_5529503 baseEnd_5529503 := by
    simpa [prefixWord, tailWord_5529503, baseEnd_5529503] using wordTrace_append hprefix tailTrace_5529503
  have hstable : (prefixWord ++ tailWord_5529503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529503).length < 2 ^ (prefixWord ++ tailWord_5529503).sum := by decide
  have hdescent : baseEnd_5529503 < baseStart_5529503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529515 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 5]
def baseStart_5529515 : Nat := 118140960795 + 5529515 * 2 ^ 59
def prefixEnd_5529515 : Nat := 4983230072969 + 3 ^ 40 * 5529515 * 2
def baseEnd_5529515 : Nat := 2839298981246038480832729

theorem tailTrace_5529515 : CollatzResearch.WordTrace tailWord_5529515 prefixEnd_5529515 2839298981246038480832729 := by
  unfold tailWord_5529515
  simp only [CollatzResearch.WordTrace]
  refine ⟨201677980562518995822293999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134451987041679330548195999 201677980562518995822293999)
  ·
    refine ⟨302516970843778493733440999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201677980562518995822293999 302516970843778493733440999)
    ·
      refine ⟨453775456265667740600161499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302516970843778493733440999 453775456265667740600161499)
      ·
        refine ⟨680663184398501610900242249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453775456265667740600161499 680663184398501610900242249)
        ·
          refine ⟨510497388298876208175181687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680663184398501610900242249 510497388298876208175181687)
          ·
            refine ⟨765746082448314312262772531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510497388298876208175181687 765746082448314312262772531)
            ·
              refine ⟨1148619123672471468394158797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765746082448314312262772531 1148619123672471468394158797)
              ·
                refine ⟨430732171377176800647809549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1148619123672471468394158797 430732171377176800647809549)
                ·
                  refine ⟨161524564266441300242928581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430732171377176800647809549 161524564266441300242928581)
                  ·
                    refine ⟨30285855799957743795549109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161524564266441300242928581 30285855799957743795549109)
                    ·
                      refine ⟨2839298981246038480832729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30285855799957743795549109 2839298981246038480832729)
                      ·
                        rfl

theorem cell23_5529515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_5529515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529515 prefixEnd_5529515 := by exact prefixLift 5529515
  have htrace : WordTrace (prefixWord ++ tailWord_5529515) baseStart_5529515 baseEnd_5529515 := by
    simpa [prefixWord, tailWord_5529515, baseEnd_5529515] using wordTrace_append hprefix tailTrace_5529515
  have hstable : (prefixWord ++ tailWord_5529515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529515).length < 2 ^ (prefixWord ++ tailWord_5529515).sum := by decide
  have hdescent : baseEnd_5529515 < baseStart_5529515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529546 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2]
def baseStart_5529546 : Nat := 118140960795 + 5529546 * 2 ^ 59
def prefixEnd_5529546 : Nat := 4983230072969 + 3 ^ 40 * 5529546 * 2
def baseEnd_5529546 : Nat := 2839314899146327859545087

theorem tailTrace_5529546 : CollatzResearch.WordTrace tailWord_5529546 prefixEnd_5529546 2839314899146327859545087 := by
  unfold tailWord_5529546
  simp only [CollatzResearch.WordTrace]
  refine ⟨50419777806351672029168123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134452740816937792077781661 50419777806351672029168123)
  ·
    refine ⟨75629666709527508043752185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50419777806351672029168123 75629666709527508043752185)
    ·
      refine ⟨56722250032145631032814139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75629666709527508043752185 56722250032145631032814139)
      ·
        refine ⟨85083375048218446549221209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56722250032145631032814139 85083375048218446549221209)
        ·
          refine ⟨63812531286163834911915907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85083375048218446549221209 63812531286163834911915907)
          ·
            refine ⟨95718796929245752367873861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63812531286163834911915907 95718796929245752367873861)
            ·
              refine ⟨17947274424233578568976349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95718796929245752367873861 17947274424233578568976349)
              ·
                refine ⟨6730227909087591963366131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17947274424233578568976349 6730227909087591963366131)
                ·
                  refine ⟨10095341863631387945049197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6730227909087591963366131 10095341863631387945049197)
                  ·
                    refine ⟨3785753198861770479393449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10095341863631387945049197 3785753198861770479393449)
                    ·
                      refine ⟨2839314899146327859545087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785753198861770479393449 2839314899146327859545087)
                      ·
                        rfl

theorem cell23_5529546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_5529546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529546 prefixEnd_5529546 := by exact prefixLift 5529546
  have htrace : WordTrace (prefixWord ++ tailWord_5529546) baseStart_5529546 baseEnd_5529546 := by
    simpa [prefixWord, tailWord_5529546, baseEnd_5529546] using wordTrace_append hprefix tailTrace_5529546
  have hstable : (prefixWord ++ tailWord_5529546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529546).length < 2 ^ (prefixWord ++ tailWord_5529546).sum := by decide
  have hdescent : baseEnd_5529546 < baseStart_5529546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529564 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5529564 : Nat := 118140960795 + 5529564 * 2 ^ 59
def prefixEnd_5529564 : Nat := 4983230072969 + 3 ^ 40 * 5529564 * 2
def baseEnd_5529564 : Nat := 946441380599369596373335

theorem tailTrace_5529564 : CollatzResearch.WordTrace tailWord_5529564 prefixEnd_5529564 946441380599369596373335 := by
  unfold tailWord_5529564
  simp only [CollatzResearch.WordTrace]
  refine ⟨100839883869670738595413873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134453178492894318127218497 100839883869670738595413873)
  ·
    refine ⟨75629912902253053946560405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100839883869670738595413873 75629912902253053946560405)
    ·
      refine ⟨3545152167293111903745019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75629912902253053946560405 3545152167293111903745019)
      ·
        refine ⟨5317728250939667855617529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545152167293111903745019 5317728250939667855617529)
        ·
          refine ⟨3988296188204750891713147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5317728250939667855617529 3988296188204750891713147)
          ·
            refine ⟨5982444282307126337569721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988296188204750891713147 5982444282307126337569721)
            ·
              refine ⟨4486833211730344753177291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5982444282307126337569721 4486833211730344753177291)
              ·
                refine ⟨6730249817595517129765937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4486833211730344753177291 6730249817595517129765937)
                ·
                  refine ⟨5047687363196637847324453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6730249817595517129765937 5047687363196637847324453)
                  ·
                    refine ⟨946441380599369596373335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5047687363196637847324453 946441380599369596373335)
                    ·
                      rfl

theorem cell23_5529564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5529564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529564 prefixEnd_5529564 := by exact prefixLift 5529564
  have htrace : WordTrace (prefixWord ++ tailWord_5529564) baseStart_5529564 baseEnd_5529564 := by
    simpa [prefixWord, tailWord_5529564, baseEnd_5529564] using wordTrace_append hprefix tailTrace_5529564
  have hstable : (prefixWord ++ tailWord_5529564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529564).length < 2 ^ (prefixWord ++ tailWord_5529564).sum := by decide
  have hdescent : baseEnd_5529564 < baseStart_5529564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529570 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_5529570 : Nat := 118140960795 + 5529570 * 2 ^ 59
def prefixEnd_5529570 : Nat := 4983230072969 + 3 ^ 40 * 5529570 * 2
def baseEnd_5529570 : Nat := 2839327222682035765644977

theorem tailTrace_5529570 : CollatzResearch.WordTrace tailWord_5529570 prefixEnd_5529570 2839327222682035765644977 := by
  unfold tailWord_5529570
  simp only [CollatzResearch.WordTrace]
  refine ⟨50419996644329935053886541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134453324384879826810364109 50419996644329935053886541)
  ·
    refine ⟨18907498741623725645207453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50419996644329935053886541 18907498741623725645207453)
    ·
      refine ⟨7090312028108897116952795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18907498741623725645207453 7090312028108897116952795)
      ·
        refine ⟨10635468042163345675429193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7090312028108897116952795 10635468042163345675429193)
        ·
          refine ⟨7976601031622509256571895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10635468042163345675429193 7976601031622509256571895)
          ·
            refine ⟨11964901547433763884857843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7976601031622509256571895 11964901547433763884857843)
            ·
              refine ⟨17947352321150645827286765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11964901547433763884857843 17947352321150645827286765)
              ·
                refine ⟨6730257120431492185232537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17947352321150645827286765 6730257120431492185232537)
                ·
                  refine ⟨5047692840323619138924403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6730257120431492185232537 5047692840323619138924403)
                  ·
                    refine ⟨7571539260485428708386605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5047692840323619138924403 7571539260485428708386605)
                    ·
                      refine ⟨2839327222682035765644977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7571539260485428708386605 2839327222682035765644977)
                      ·
                        rfl

theorem cell23_5529570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_5529570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529570 prefixEnd_5529570 := by exact prefixLift 5529570
  have htrace : WordTrace (prefixWord ++ tailWord_5529570) baseStart_5529570 baseEnd_5529570 := by
    simpa [prefixWord, tailWord_5529570, baseEnd_5529570] using wordTrace_append hprefix tailTrace_5529570
  have hstable : (prefixWord ++ tailWord_5529570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529570).length < 2 ^ (prefixWord ++ tailWord_5529570).sum := by decide
  have hdescent : baseEnd_5529570 < baseStart_5529570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529572 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_5529572 : Nat := 118140960795 + 5529572 * 2 ^ 59
def prefixEnd_5529572 : Nat := 4983230072969 + 3 ^ 40 * 5529572 * 2
def baseEnd_5529572 : Nat := 2839328249643344757819967

theorem tailTrace_5529572 : CollatzResearch.WordTrace tailWord_5529572 prefixEnd_5529572 2839328249643344757819967 := by
  unfold tailWord_5529572
  simp only [CollatzResearch.WordTrace]
  refine ⟨100840029761656247278559485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134453373015541663038079313 100840029761656247278559485)
  ·
    refine ⟨37815011160621092729459807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100840029761656247278559485 37815011160621092729459807)
    ·
      refine ⟨56722516740931639094189711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37815011160621092729459807 56722516740931639094189711)
      ·
        refine ⟨85083775111397458641284567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56722516740931639094189711 85083775111397458641284567)
        ·
          refine ⟨127625662667096187961926851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85083775111397458641284567 127625662667096187961926851)
          ·
            refine ⟨191438494000644281942890277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127625662667096187961926851 191438494000644281942890277)
            ·
              refine ⟨35894717625120802864291927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191438494000644281942890277 35894717625120802864291927)
              ·
                refine ⟨53842076437681204296437891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35894717625120802864291927 53842076437681204296437891)
                ·
                  refine ⟨80763114656521806444656837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53842076437681204296437891 80763114656521806444656837)
                  ·
                    refine ⟨15143083998097838708373157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80763114656521806444656837 15143083998097838708373157)
                    ·
                      refine ⟨2839328249643344757819967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15143083998097838708373157 2839328249643344757819967)
                      ·
                        rfl

theorem cell23_5529572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_5529572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529572 prefixEnd_5529572 := by exact prefixLift 5529572
  have htrace : WordTrace (prefixWord ++ tailWord_5529572) baseStart_5529572 baseEnd_5529572 := by
    simpa [prefixWord, tailWord_5529572, baseEnd_5529572] using wordTrace_append hprefix tailTrace_5529572
  have hstable : (prefixWord ++ tailWord_5529572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529572).length < 2 ^ (prefixWord ++ tailWord_5529572).sum := by decide
  have hdescent : baseEnd_5529572 < baseStart_5529572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529610 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2]
def baseStart_5529610 : Nat := 118140960795 + 5529610 * 2 ^ 59
def prefixEnd_5529610 : Nat := 4983230072969 + 3 ^ 40 * 5529610 * 2
def baseEnd_5529610 : Nat := 2839347761908215609144793

theorem tailTrace_5529610 : CollatzResearch.WordTrace tailWord_5529610 prefixEnd_5529610 2839347761908215609144793 := by
  unfold tailWord_5529610
  simp only [CollatzResearch.WordTrace]
  refine ⟨50420361374293706761750571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134454296998116551364668189 50420361374293706761750571)
  ·
    refine ⟨75630542061440560142625857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50420361374293706761750571 75630542061440560142625857)
    ·
      refine ⟨56722906546080420106969393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75630542061440560142625857 56722906546080420106969393)
      ·
        refine ⟨42542179909560315080227045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56722906546080420106969393 42542179909560315080227045)
        ·
          refine ⟨7976658733042559077542571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42542179909560315080227045 7976658733042559077542571)
          ·
            refine ⟨11964988099563838616313857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7976658733042559077542571 11964988099563838616313857)
            ·
              refine ⟨8973741074672878962235393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11964988099563838616313857 8973741074672878962235393)
              ·
                refine ⟨6730305806004659221676545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8973741074672878962235393 6730305806004659221676545)
                ·
                  refine ⟨5047729354503494416257409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6730305806004659221676545 5047729354503494416257409)
                  ·
                    refine ⟨3785797015877620812193057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5047729354503494416257409 3785797015877620812193057)
                    ·
                      refine ⟨2839347761908215609144793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785797015877620812193057 2839347761908215609144793)
                      ·
                        rfl

theorem cell23_5529610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_5529610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529610 prefixEnd_5529610 := by exact prefixLift 5529610
  have htrace : WordTrace (prefixWord ++ tailWord_5529610) baseStart_5529610 baseEnd_5529610 := by
    simpa [prefixWord, tailWord_5529610, baseEnd_5529610] using wordTrace_append hprefix tailTrace_5529610
  have hstable : (prefixWord ++ tailWord_5529610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529610).length < 2 ^ (prefixWord ++ tailWord_5529610).sum := by decide
  have hdescent : baseEnd_5529610 < baseStart_5529610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529619 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 2, 5, 2]
def baseStart_5529619 : Nat := 118140960795 + 5529619 * 2 ^ 59
def prefixEnd_5529619 : Nat := 4983230072969 + 3 ^ 40 * 5529619 * 2
def baseEnd_5529619 : Nat := 2839352383234106073932251

theorem tailTrace_5529619 : CollatzResearch.WordTrace tailWord_5529619 prefixEnd_5529619 2839352383234106073932251 := by
  unfold tailWord_5529619
  simp only [CollatzResearch.WordTrace]
  refine ⟨201681773754142221584079911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134454515836094814389386607 201681773754142221584079911)
  ·
    refine ⟨302522660631213332376119867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201681773754142221584079911 302522660631213332376119867)
    ·
      refine ⟨453783990946819998564179801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302522660631213332376119867 453783990946819998564179801)
      ·
        refine ⟨340337993210114998923134851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453783990946819998564179801 340337993210114998923134851)
        ·
          refine ⟨510506989815172498384702277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340337993210114998923134851 510506989815172498384702277)
          ·
            refine ⟨95720060590344843447131677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 510506989815172498384702277 95720060590344843447131677)
            ·
              refine ⟨35895022721379316292674379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95720060590344843447131677 35895022721379316292674379)
              ·
                refine ⟨53842534082068974439011569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35895022721379316292674379 53842534082068974439011569)
                ·
                  refine ⟨40381900561551730829258677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53842534082068974439011569 40381900561551730829258677)
                  ·
                    refine ⟨3785803177645474765243001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40381900561551730829258677 3785803177645474765243001)
                    ·
                      refine ⟨2839352383234106073932251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785803177645474765243001 2839352383234106073932251)
                      ·
                        rfl

theorem cell23_5529619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 5, 2].length) (baseStart_5529619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529619 prefixEnd_5529619 := by exact prefixLift 5529619
  have htrace : WordTrace (prefixWord ++ tailWord_5529619) baseStart_5529619 baseEnd_5529619 := by
    simpa [prefixWord, tailWord_5529619, baseEnd_5529619] using wordTrace_append hprefix tailTrace_5529619
  have hstable : (prefixWord ++ tailWord_5529619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529619).length < 2 ^ (prefixWord ++ tailWord_5529619).sum := by decide
  have hdescent : baseEnd_5529619 < baseStart_5529619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529646 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_5529646 : Nat := 118140960795 + 5529646 * 2 ^ 59
def prefixEnd_5529646 : Nat := 4983230072969 + 3 ^ 40 * 5529646 * 2
def baseEnd_5529646 : Nat := 946455415737259156098209

theorem tailTrace_5529646 : CollatzResearch.WordTrace tailWord_5529646 prefixEnd_5529646 946455415737259156098209 := by
  unfold tailWord_5529646
  simp only [CollatzResearch.WordTrace]
  refine ⟨25210344815630550649414099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134455172350029603463541861 25210344815630550649414099)
  ·
    refine ⟨37815517223445825974121149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25210344815630550649414099 37815517223445825974121149)
    ·
      refine ⟨14180818958792184740295431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37815517223445825974121149 14180818958792184740295431)
      ·
        refine ⟨21271228438188277110443147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14180818958792184740295431 21271228438188277110443147)
        ·
          refine ⟨31906842657282415665664721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21271228438188277110443147 31906842657282415665664721)
          ·
            refine ⟨23930131992961811749248541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31906842657282415665664721 23930131992961811749248541)
            ·
              refine ⟨8973799497360679405968203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23930131992961811749248541 8973799497360679405968203)
              ·
                refine ⟨13460699246041019108952305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8973799497360679405968203 13460699246041019108952305)
                ·
                  refine ⟨10095524434530764331714229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13460699246041019108952305 10095524434530764331714229)
                  ·
                    refine ⟨946455415737259156098209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10095524434530764331714229 946455415737259156098209)
                    ·
                      rfl

theorem cell23_5529646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_5529646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529646 prefixEnd_5529646 := by exact prefixLift 5529646
  have htrace : WordTrace (prefixWord ++ tailWord_5529646) baseStart_5529646 baseEnd_5529646 := by
    simpa [prefixWord, tailWord_5529646, baseEnd_5529646] using wordTrace_append hprefix tailTrace_5529646
  have hstable : (prefixWord ++ tailWord_5529646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529646).length < 2 ^ (prefixWord ++ tailWord_5529646).sum := by decide
  have hdescent : baseEnd_5529646 < baseStart_5529646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529649 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_5529649 : Nat := 118140960795 + 5529649 * 2 ^ 59
def prefixEnd_5529649 : Nat := 4983230072969 + 3 ^ 40 * 5529649 * 2
def baseEnd_5529649 : Nat := 2839367787653740956557113

theorem tailTrace_5529649 : CollatzResearch.WordTrace tailWord_5529649 prefixEnd_5529649 2839367787653740956557113 := by
  unfold tailWord_5529649
  simp only [CollatzResearch.WordTrace]
  refine ⟨201682867944033536707672001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134455245296022357805114667 201682867944033536707672001)
  ·
    refine ⟨151262150958025152530754001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201682867944033536707672001 151262150958025152530754001)
    ·
      refine ⟨113446613218518864398065501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151262150958025152530754001 113446613218518864398065501)
      ·
        refine ⟨42542479956944574149274563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113446613218518864398065501 42542479956944574149274563)
        ·
          refine ⟨63813719935416861223911845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42542479956944574149274563 63813719935416861223911845)
          ·
            refine ⟨11965072487890661479483471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63813719935416861223911845 11965072487890661479483471)
            ·
              refine ⟨17947608731835992219225207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11965072487890661479483471 17947608731835992219225207)
              ·
                refine ⟨26921413097753988328837811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17947608731835992219225207 26921413097753988328837811)
                ·
                  refine ⟨40382119646630982493256717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26921413097753988328837811 40382119646630982493256717)
                  ·
                    refine ⟨15143294867486618434971269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40382119646630982493256717 15143294867486618434971269)
                    ·
                      refine ⟨2839367787653740956557113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15143294867486618434971269 2839367787653740956557113)
                      ·
                        rfl

theorem cell23_5529649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_5529649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529649 prefixEnd_5529649 := by exact prefixLift 5529649
  have htrace : WordTrace (prefixWord ++ tailWord_5529649) baseStart_5529649 baseEnd_5529649 := by
    simpa [prefixWord, tailWord_5529649, baseEnd_5529649] using wordTrace_append hprefix tailTrace_5529649
  have hstable : (prefixWord ++ tailWord_5529649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529649).length < 2 ^ (prefixWord ++ tailWord_5529649).sum := by decide
  have hdescent : baseEnd_5529649 < baseStart_5529649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529669 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 4, 2, 3]
def baseStart_5529669 : Nat := 118140960795 + 5529669 * 2 ^ 59
def prefixEnd_5529669 : Nat := 4983230072969 + 3 ^ 40 * 5529669 * 2
def baseEnd_5529669 : Nat := 2839378057266830878307021

theorem tailTrace_5529669 : CollatzResearch.WordTrace tailWord_5529669 prefixEnd_5529669 2839378057266830878307021 := by
  unfold tailWord_5529669
  simp only [CollatzResearch.WordTrace]
  refine ⟨201683597403961080123400061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134455731602640720082266707 201683597403961080123400061)
  ·
    refine ⟨75631349026485405046275023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201683597403961080123400061 75631349026485405046275023)
    ·
      refine ⟨113447023539728107569412535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75631349026485405046275023 113447023539728107569412535)
      ·
        refine ⟨170170535309592161354118803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113447023539728107569412535 170170535309592161354118803)
        ·
          refine ⟨255255802964388242031178205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170170535309592161354118803 255255802964388242031178205)
          ·
            refine ⟨95720926111645590761691827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255255802964388242031178205 95720926111645590761691827)
            ·
              refine ⟨143581389167468386142537741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95720926111645590761691827 143581389167468386142537741)
              ·
                refine ⟨53843020937800644803451653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143581389167468386142537741 53843020937800644803451653)
                ·
                  refine ⟨10095566425837620900647185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53843020937800644803451653 10095566425837620900647185)
                  ·
                    refine ⟨7571674819378215675485389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10095566425837620900647185 7571674819378215675485389)
                    ·
                      refine ⟨2839378057266830878307021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7571674819378215675485389 2839378057266830878307021)
                      ·
                        rfl

theorem cell23_5529669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_5529669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529669 prefixEnd_5529669 := by exact prefixLift 5529669
  have htrace : WordTrace (prefixWord ++ tailWord_5529669) baseStart_5529669 baseEnd_5529669 := by
    simpa [prefixWord, tailWord_5529669, baseEnd_5529669] using wordTrace_append hprefix tailTrace_5529669
  have hstable : (prefixWord ++ tailWord_5529669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529669).length < 2 ^ (prefixWord ++ tailWord_5529669).sum := by decide
  have hdescent : baseEnd_5529669 < baseStart_5529669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529693 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_5529693 : Nat := 118140960795 + 5529693 * 2 ^ 59
def prefixEnd_5529693 : Nat := 4983230072969 + 3 ^ 40 * 5529693 * 2
def baseEnd_5529693 : Nat := 946463460267512928135637

theorem tailTrace_5529693 : CollatzResearch.WordTrace tailWord_5529693 prefixEnd_5529693 946463460267512928135637 := by
  unfold tailWord_5529693
  simp only [CollatzResearch.WordTrace]
  refine ⟨201684472755874132222273733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134456315170582754814849155 201684472755874132222273733)
  ·
    refine ⟨37815838641726399791676325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201684472755874132222273733 37815838641726399791676325)
    ·
      refine ⟨7090469745323699960939311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37815838641726399791676325 7090469745323699960939311)
      ·
        refine ⟨10635704617985549941408967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7090469745323699960939311 10635704617985549941408967)
        ·
          refine ⟨15953556926978324912113451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10635704617985549941408967 15953556926978324912113451)
          ·
            refine ⟨23930335390467487368170177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15953556926978324912113451 23930335390467487368170177)
            ·
              refine ⟨17947751542850615526127633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23930335390467487368170177 17947751542850615526127633)
              ·
                refine ⟨13460813657137961644595725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17947751542850615526127633 13460813657137961644595725)
                ·
                  refine ⟨5047805121426735616723397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13460813657137961644595725 5047805121426735616723397)
                  ·
                    refine ⟨946463460267512928135637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5047805121426735616723397 946463460267512928135637)
                    ·
                      rfl

theorem cell23_5529693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_5529693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529693 prefixEnd_5529693 := by exact prefixLift 5529693
  have htrace : WordTrace (prefixWord ++ tailWord_5529693) baseStart_5529693 baseEnd_5529693 := by
    simpa [prefixWord, tailWord_5529693, baseEnd_5529693] using wordTrace_append hprefix tailTrace_5529693
  have hstable : (prefixWord ++ tailWord_5529693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529693).length < 2 ^ (prefixWord ++ tailWord_5529693).sum := by decide
  have hdescent : baseEnd_5529693 < baseStart_5529693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529733 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 3, 1, 3]
def baseStart_5529733 : Nat := 118140960795 + 5529733 * 2 ^ 59
def prefixEnd_5529733 : Nat := 4983230072969 + 3 ^ 40 * 5529733 * 2
def baseEnd_5529733 : Nat := 2839410920028718627906727

theorem tailTrace_5529733 : CollatzResearch.WordTrace tailWord_5529733 prefixEnd_5529733 2839410920028718627906727 := by
  unfold tailWord_5529733
  simp only [CollatzResearch.WordTrace]
  refine ⟨201685931675729219053729853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134457287783819479369153235 201685931675729219053729853)
  ·
    refine ⟨75632224378398457145148695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201685931675729219053729853 75632224378398457145148695)
    ·
      refine ⟨113448336567597685717723043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75632224378398457145148695 113448336567597685717723043)
      ·
        refine ⟨170172504851396528576584565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113448336567597685717723043 170172504851396528576584565)
        ·
          refine ⟨15953672329818424554054803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170172504851396528576584565 15953672329818424554054803)
          ·
            refine ⟨23930508494727636831082205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15953672329818424554054803 23930508494727636831082205)
            ·
              refine ⟨8973940685522863811655827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23930508494727636831082205 8973940685522863811655827)
              ·
                refine ⟨13460911028284295717483741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8973940685522863811655827 13460911028284295717483741)
                ·
                  refine ⟨5047841635606610894056403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13460911028284295717483741 5047841635606610894056403)
                  ·
                    refine ⟨7571762453409916341084605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5047841635606610894056403 7571762453409916341084605)
                    ·
                      refine ⟨2839410920028718627906727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7571762453409916341084605 2839410920028718627906727)
                      ·
                        rfl

theorem cell23_5529733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_5529733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529733 prefixEnd_5529733 := by exact prefixLift 5529733
  have htrace : WordTrace (prefixWord ++ tailWord_5529733) baseStart_5529733 baseEnd_5529733 := by
    simpa [prefixWord, tailWord_5529733, baseEnd_5529733] using wordTrace_append hprefix tailTrace_5529733
  have hstable : (prefixWord ++ tailWord_5529733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529733).length < 2 ^ (prefixWord ++ tailWord_5529733).sum := by decide
  have hdescent : baseEnd_5529733 < baseStart_5529733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529749 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_5529749 : Nat := 118140960795 + 5529749 * 2 ^ 59
def prefixEnd_5529749 : Nat := 4983230072969 + 3 ^ 40 * 5529749 * 2
def baseEnd_5529749 : Nat := 946473045239730188435551

theorem tailTrace_5529749 : CollatzResearch.WordTrace tailWord_5529749 prefixEnd_5529749 946473045239730188435551 := by
  unfold tailWord_5529749
  simp only [CollatzResearch.WordTrace]
  refine ⟨201686515243671253786312301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134457676829114169190874867 201686515243671253786312301)
  ·
    refine ⟨75632443216376720169867113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201686515243671253786312301 75632443216376720169867113)
    ·
      refine ⟨56724332412282540127400335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75632443216376720169867113 56724332412282540127400335)
      ·
        refine ⟨85086498618423810191100503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56724332412282540127400335 85086498618423810191100503)
        ·
          refine ⟨127629747927635715286650755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85086498618423810191100503 127629747927635715286650755)
          ·
            refine ⟨191444621891453572929976133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127629747927635715286650755 191444621891453572929976133)
            ·
              refine ⟨35895866604647544924370525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191444621891453572929976133 35895866604647544924370525)
              ·
                refine ⟨13460949976742829346638947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35895866604647544924370525 13460949976742829346638947)
                ·
                  refine ⟨20191424965114244019958421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13460949976742829346638947 20191424965114244019958421)
                  ·
                    refine ⟨946473045239730188435551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20191424965114244019958421 946473045239730188435551)
                    ·
                      rfl

theorem cell23_5529749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_5529749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529749 prefixEnd_5529749 := by exact prefixLift 5529749
  have htrace : WordTrace (prefixWord ++ tailWord_5529749) baseStart_5529749 baseEnd_5529749 := by
    simpa [prefixWord, tailWord_5529749, baseEnd_5529749] using wordTrace_append hprefix tailTrace_5529749
  have hstable : (prefixWord ++ tailWord_5529749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529749).length < 2 ^ (prefixWord ++ tailWord_5529749).sum := by decide
  have hdescent : baseEnd_5529749 < baseStart_5529749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529756 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_5529756 : Nat := 118140960795 + 5529756 * 2 ^ 59
def prefixEnd_5529756 : Nat := 4983230072969 + 3 ^ 40 * 5529756 * 2
def baseEnd_5529756 : Nat := 2839422730083772037919121

theorem tailTrace_5529756 : CollatzResearch.WordTrace tailWord_5529756 prefixEnd_5529756 2839422730083772037919121 := by
  unfold tailWord_5529756
  simp only [CollatzResearch.WordTrace]
  refine ⟨100843385277322946990908561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134457847036430595987878081 100843385277322946990908561)
  ·
    refine ⟨75632538957992210243181421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100843385277322946990908561 75632538957992210243181421)
    ·
      refine ⟨28362202109247078841193033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75632538957992210243181421 28362202109247078841193033)
      ·
        refine ⟨21271651581935309130894775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28362202109247078841193033 21271651581935309130894775)
        ·
          refine ⟨31907477372902963696342163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21271651581935309130894775 31907477372902963696342163)
          ·
            refine ⟨47861216059354445544513245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31907477372902963696342163 47861216059354445544513245)
            ·
              refine ⟨17947956022257917079192467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47861216059354445544513245 17947956022257917079192467)
              ·
                refine ⟨26921934033386875618788701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17947956022257917079192467 26921934033386875618788701)
                ·
                  refine ⟨10095725262520078357045763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26921934033386875618788701 10095725262520078357045763)
                  ·
                    refine ⟨15143587893780117535568645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10095725262520078357045763 15143587893780117535568645)
                    ·
                      refine ⟨2839422730083772037919121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15143587893780117535568645 2839422730083772037919121)
                      ·
                        rfl

theorem cell23_5529756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_5529756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529756 prefixEnd_5529756 := by exact prefixLift 5529756
  have htrace : WordTrace (prefixWord ++ tailWord_5529756) baseStart_5529756 baseEnd_5529756 := by
    simpa [prefixWord, tailWord_5529756, baseEnd_5529756] using wordTrace_append hprefix tailTrace_5529756
  have hstable : (prefixWord ++ tailWord_5529756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529756).length < 2 ^ (prefixWord ++ tailWord_5529756).sum := by decide
  have hdescent : baseEnd_5529756 < baseStart_5529756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529783 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 2, 4]
def baseStart_5529783 : Nat := 118140960795 + 5529783 * 2 ^ 59
def prefixEnd_5529783 : Nat := 4983230072969 + 3 ^ 40 * 5529783 * 2
def baseEnd_5529783 : Nat := 946478864687147810760499

theorem tailTrace_5529783 : CollatzResearch.WordTrace tailWord_5529783 prefixEnd_5529783 946478864687147810760499 := by
  unfold tailWord_5529783
  simp only [CollatzResearch.WordTrace]
  refine ⟨201687755325548077593050003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134458503550365385062033335 201687755325548077593050003)
  ·
    refine ⟨302531632988322116389575005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201687755325548077593050003 302531632988322116389575005)
    ·
      refine ⟨113449362370620793646090627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302531632988322116389575005 113449362370620793646090627)
      ·
        refine ⟨170174043555931190469135941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113449362370620793646090627 170174043555931190469135941)
        ·
          refine ⟨31907633166737098212962989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170174043555931190469135941 31907633166737098212962989)
          ·
            refine ⟨11965362437526411829861121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31907633166737098212962989 11965362437526411829861121)
            ·
              refine ⟨8974021828144808872395841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11965362437526411829861121 8974021828144808872395841)
              ·
                refine ⟨6730516371108606654296881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8974021828144808872395841 6730516371108606654296881)
                ·
                  refine ⟨5047887278331454990722661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6730516371108606654296881 5047887278331454990722661)
                  ·
                    refine ⟨946478864687147810760499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5047887278331454990722661 946478864687147810760499)
                    ·
                      rfl

theorem cell23_5529783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_5529783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529783 prefixEnd_5529783 := by exact prefixLift 5529783
  have htrace : WordTrace (prefixWord ++ tailWord_5529783) baseStart_5529783 baseEnd_5529783 := by
    simpa [prefixWord, tailWord_5529783, baseEnd_5529783] using wordTrace_append hprefix tailTrace_5529783
  have hstable : (prefixWord ++ tailWord_5529783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529783).length < 2 ^ (prefixWord ++ tailWord_5529783).sum := by decide
  have hdescent : baseEnd_5529783 < baseStart_5529783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529796 : List Nat := [2, 3, 3, 1, 2, 1, 3, 8]
def baseStart_5529796 : Nat := 118140960795 + 5529796 * 2 ^ 59
def prefixEnd_5529796 : Nat := 4983230072969 + 3 ^ 40 * 5529796 * 2
def baseEnd_5529796 : Nat := 105164565529998217830331

theorem tailTrace_5529796 : CollatzResearch.WordTrace tailWord_5529796 prefixEnd_5529796 105164565529998217830331 := by
  unfold tailWord_5529796
  simp only [CollatzResearch.WordTrace]
  refine ⟨100844114737250490406636621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134458819649667320542182161 100844114737250490406636621)
  ·
    refine ⟨37816543026468933902488733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100844114737250490406636621 37816543026468933902488733)
    ·
      refine ⟨14181203634925850213433275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37816543026468933902488733 14181203634925850213433275)
      ·
        refine ⟨21271805452388775320149913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14181203634925850213433275 21271805452388775320149913)
        ·
          refine ⟨15953854089291581490112435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21271805452388775320149913 15953854089291581490112435)
          ·
            refine ⟨23930781133937372235168653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15953854089291581490112435 23930781133937372235168653)
            ·
              refine ⟨8974042925226514588188245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23930781133937372235168653 8974042925226514588188245)
              ·
                refine ⟨105164565529998217830331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8974042925226514588188245 105164565529998217830331)
                ·
                  rfl

theorem cell23_5529796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 8].length) (baseStart_5529796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529796 prefixEnd_5529796 := by exact prefixLift 5529796
  have htrace : WordTrace (prefixWord ++ tailWord_5529796) baseStart_5529796 baseEnd_5529796 := by
    simpa [prefixWord, tailWord_5529796, baseEnd_5529796] using wordTrace_append hprefix tailTrace_5529796
  have hstable : (prefixWord ++ tailWord_5529796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529796).length < 2 ^ (prefixWord ++ tailWord_5529796).sum := by decide
  have hdescent : baseEnd_5529796 < baseStart_5529796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529813 : List Nat := [1, 3, 2, 4, 2, 1, 3, 7]
def baseStart_5529813 : Nat := 118140960795 + 5529813 * 2 ^ 59
def prefixEnd_5529813 : Nat := 4983230072969 + 3 ^ 40 * 5529813 * 2
def baseEnd_5529813 : Nat := 105164888832632530181717

theorem tailTrace_5529813 : CollatzResearch.WordTrace tailWord_5529813 prefixEnd_5529813 105164888832632530181717 := by
  unfold tailWord_5529813
  simp only [CollatzResearch.WordTrace]
  refine ⟨201688849515439392716642093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134459233010292928477761395 201688849515439392716642093)
  ·
    refine ⟨75633318568289772268740785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201688849515439392716642093 75633318568289772268740785)
    ·
      refine ⟨56724988926217329201555589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75633318568289772268740785 56724988926217329201555589)
      ·
        refine ⟨10635935423665749225291673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56724988926217329201555589 10635935423665749225291673)
        ·
          refine ⟨7976951567749311918968755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10635935423665749225291673 7976951567749311918968755)
          ·
            refine ⟨11965427351623967878453133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7976951567749311918968755 11965427351623967878453133)
            ·
              refine ⟨4487035256858987954419925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11965427351623967878453133 4487035256858987954419925)
              ·
                refine ⟨105164888832632530181717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4487035256858987954419925 105164888832632530181717)
                ·
                  rfl

theorem cell23_5529813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 7].length) (baseStart_5529813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529813 prefixEnd_5529813 := by exact prefixLift 5529813
  have htrace : WordTrace (prefixWord ++ tailWord_5529813) baseStart_5529813 baseEnd_5529813 := by
    simpa [prefixWord, tailWord_5529813, baseEnd_5529813] using wordTrace_append hprefix tailTrace_5529813
  have hstable : (prefixWord ++ tailWord_5529813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529813).length < 2 ^ (prefixWord ++ tailWord_5529813).sum := by decide
  have hdescent : baseEnd_5529813 < baseStart_5529813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529833 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 1, 3, 2]
def baseStart_5529833 : Nat := 118140960795 + 5529833 * 2 ^ 59
def prefixEnd_5529833 : Nat := 4983230072969 + 3 ^ 40 * 5529833 * 2
def baseEnd_5529833 : Nat := 2839462268094168236656267

theorem tailTrace_5529833 : CollatzResearch.WordTrace tailWord_5529833 prefixEnd_5529833 2839462268094168236656267 := by
  unfold tailWord_5529833
  simp only [CollatzResearch.WordTrace]
  refine ⟨201689578975366936132370153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134459719316911290754913435 201689578975366936132370153)
  ·
    refine ⟨151267184231525202099277615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201689578975366936132370153 151267184231525202099277615)
    ·
      refine ⟨226900776347287803148916423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151267184231525202099277615 226900776347287803148916423)
      ·
        refine ⟨340351164520931704723374635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226900776347287803148916423 340351164520931704723374635)
        ·
          refine ⟨510526746781397557085061953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340351164520931704723374635 510526746781397557085061953)
          ·
            refine ⟨382895060086048167813796465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510526746781397557085061953 382895060086048167813796465)
            ·
              refine ⟨287171295064536125860347349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382895060086048167813796465 287171295064536125860347349)
              ·
                refine ⟨6730577228075065449851891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 287171295064536125860347349 6730577228075065449851891)
                ·
                  refine ⟨10095865842112598174777837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6730577228075065449851891 10095865842112598174777837)
                  ·
                    refine ⟨3785949690792224315541689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10095865842112598174777837 3785949690792224315541689)
                    ·
                      refine ⟨2839462268094168236656267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3785949690792224315541689 2839462268094168236656267)
                      ·
                        rfl

theorem cell23_5529833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 3, 2].length) (baseStart_5529833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529833 prefixEnd_5529833 := by exact prefixLift 5529833
  have htrace : WordTrace (prefixWord ++ tailWord_5529833) baseStart_5529833 baseEnd_5529833 := by
    simpa [prefixWord, tailWord_5529833, baseEnd_5529833] using wordTrace_append hprefix tailTrace_5529833
  have hstable : (prefixWord ++ tailWord_5529833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529833).length < 2 ^ (prefixWord ++ tailWord_5529833).sum := by decide
  have hdescent : baseEnd_5529833 < baseStart_5529833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529846 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_5529846 : Nat := 118140960795 + 5529846 * 2 ^ 59
def prefixEnd_5529846 : Nat := 4983230072969 + 3 ^ 40 * 5529846 * 2
def baseEnd_5529846 : Nat := 2839468943342676685793707

theorem tailTrace_5529846 : CollatzResearch.WordTrace tailWord_5529846 prefixEnd_5529846 2839468943342676685793707 := by
  unfold tailWord_5529846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12605628320269989959537087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134460035416213226235062261 12605628320269989959537087)
  ·
    refine ⟨18908442480404984939305631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12605628320269989959537087 18908442480404984939305631)
    ·
      refine ⟨28362663720607477408958447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18908442480404984939305631 28362663720607477408958447)
      ·
        refine ⟨42543995580911216113437671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28362663720607477408958447 42543995580911216113437671)
        ·
          refine ⟨63815993371366824170156507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42543995580911216113437671 63815993371366824170156507)
          ·
            refine ⟨95723990057050236255234761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63815993371366824170156507 95723990057050236255234761)
            ·
              refine ⟨71792992542787677191426071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95723990057050236255234761 71792992542787677191426071)
              ·
                refine ⟨107689488814181515787139107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71792992542787677191426071 107689488814181515787139107)
                ·
                  refine ⟨161534233221272273680708661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107689488814181515787139107 161534233221272273680708661)
                  ·
                    refine ⟨15143834364494275657566437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 161534233221272273680708661 15143834364494275657566437)
                    ·
                      refine ⟨2839468943342676685793707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15143834364494275657566437 2839468943342676685793707)
                      ·
                        rfl

theorem cell23_5529846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_5529846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529846 prefixEnd_5529846 := by exact prefixLift 5529846
  have htrace : WordTrace (prefixWord ++ tailWord_5529846) baseStart_5529846 baseEnd_5529846 := by
    simpa [prefixWord, tailWord_5529846, baseEnd_5529846] using wordTrace_append hprefix tailTrace_5529846
  have hstable : (prefixWord ++ tailWord_5529846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529846).length < 2 ^ (prefixWord ++ tailWord_5529846).sum := by decide
  have hdescent : baseEnd_5529846 < baseStart_5529846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529849 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_5529849 : Nat := 118140960795 + 5529849 * 2 ^ 59
def prefixEnd_5529849 : Nat := 4983230072969 + 3 ^ 40 * 5529849 * 2
def baseEnd_5529849 : Nat := 2839470483784640174056193

theorem tailTrace_5529849 : CollatzResearch.WordTrace tailWord_5529849 prefixEnd_5529849 2839470483784640174056193 := by
  unfold tailWord_5529849
  simp only [CollatzResearch.WordTrace]
  refine ⟨201690162543308970864952601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134460108362205980576635067 201690162543308970864952601)
  ·
    refine ⟨151267621907481728148714451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201690162543308970864952601 151267621907481728148714451)
    ·
      refine ⟨226901432861222592223071677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151267621907481728148714451 226901432861222592223071677)
      ·
        refine ⟨85088037322958472083651879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226901432861222592223071677 85088037322958472083651879)
        ·
          refine ⟨127632055984437708125477819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85088037322958472083651879 127632055984437708125477819)
          ·
            refine ⟨191448083976656562188216729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127632055984437708125477819 191448083976656562188216729)
            ·
              refine ⟨143586062982492421641162547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191448083976656562188216729 143586062982492421641162547)
              ·
                refine ⟨215379094473738632461743821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143586062982492421641162547 215379094473738632461743821)
                ·
                  refine ⟨80767160427651987173153933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215379094473738632461743821 80767160427651987173153933)
                  ·
                    refine ⟨30287685160369495189932725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80767160427651987173153933 30287685160369495189932725)
                    ·
                      refine ⟨2839470483784640174056193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30287685160369495189932725 2839470483784640174056193)
                      ·
                        rfl

theorem cell23_5529849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_5529849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529849 prefixEnd_5529849 := by exact prefixLift 5529849
  have htrace : WordTrace (prefixWord ++ tailWord_5529849) baseStart_5529849 baseEnd_5529849 := by
    simpa [prefixWord, tailWord_5529849, baseEnd_5529849] using wordTrace_append hprefix tailTrace_5529849
  have hstable : (prefixWord ++ tailWord_5529849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529849).length < 2 ^ (prefixWord ++ tailWord_5529849).sum := by decide
  have hdescent : baseEnd_5529849 < baseStart_5529849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529866 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_5529866 : Nat := 118140960795 + 5529866 * 2 ^ 59
def prefixEnd_5529866 : Nat := 4983230072969 + 3 ^ 40 * 5529866 * 2
def baseEnd_5529866 : Nat := 2839479212955766607543615

theorem tailTrace_5529866 : CollatzResearch.WordTrace tailWord_5529866 prefixEnd_5529866 2839479212955766607543615 := by
  unfold tailWord_5529866
  simp only [CollatzResearch.WordTrace]
  refine ⟨50422695646061845692080363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134460521722831588512214301 50422695646061845692080363)
  ·
    refine ⟨75634043469092768538120545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50422695646061845692080363 75634043469092768538120545)
    ·
      refine ⟨56725532601819576403590409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75634043469092768538120545 56725532601819576403590409)
      ·
        refine ⟨42544149451364682302692807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56725532601819576403590409 42544149451364682302692807)
        ·
          refine ⟨63816224177047023454039211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42544149451364682302692807 63816224177047023454039211)
          ·
            refine ⟨95724336265570535181058817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63816224177047023454039211 95724336265570535181058817)
            ·
              refine ⟨71793252199177901385794113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95724336265570535181058817 71793252199177901385794113)
              ·
                refine ⟨53844939149383426039345585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71793252199177901385794113 53844939149383426039345585)
                ·
                  refine ⟨40383704362037569529509189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53844939149383426039345585 40383704362037569529509189)
                  ·
                    refine ⟨7571944567882044286782973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40383704362037569529509189 7571944567882044286782973)
                    ·
                      refine ⟨2839479212955766607543615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7571944567882044286782973 2839479212955766607543615)
                      ·
                        rfl

theorem cell23_5529866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_5529866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529866 prefixEnd_5529866 := by exact prefixLift 5529866
  have htrace : WordTrace (prefixWord ++ tailWord_5529866) baseStart_5529866 baseEnd_5529866 := by
    simpa [prefixWord, tailWord_5529866, baseEnd_5529866] using wordTrace_append hprefix tailTrace_5529866
  have hstable : (prefixWord ++ tailWord_5529866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529866).length < 2 ^ (prefixWord ++ tailWord_5529866).sum := by decide
  have hdescent : baseEnd_5529866 < baseStart_5529866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529914 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2]
def baseStart_5529914 : Nat := 118140960795 + 5529914 * 2 ^ 59
def prefixEnd_5529914 : Nat := 4983230072969 + 3 ^ 40 * 5529914 * 2
def baseEnd_5529914 : Nat := 2839503860027182419743395

theorem tailTrace_5529914 : CollatzResearch.WordTrace tailWord_5529914 prefixEnd_5529914 2839503860027182419743395 := by
  unfold tailWord_5529914
  simp only [CollatzResearch.WordTrace]
  refine ⟨50423133322018371741517199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134461688858715657977379197 50423133322018371741517199)
  ·
    refine ⟨75634699983027557612275799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50423133322018371741517199 75634699983027557612275799)
    ·
      refine ⟨113452049974541336418413699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75634699983027557612275799 113452049974541336418413699)
      ·
        refine ⟨170178074961812004627620549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113452049974541336418413699 170178074961812004627620549)
        ·
          refine ⟨31908389055339750867678853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170178074961812004627620549 31908389055339750867678853)
          ·
            refine ⟨5982822947876203287689785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31908389055339750867678853 5982822947876203287689785)
            ·
              refine ⟨4487117210907152465767339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5982822947876203287689785 4487117210907152465767339)
              ·
                refine ⟨6730675816360728698651009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4487117210907152465767339 6730675816360728698651009)
                ·
                  refine ⟨5048006862270546523988257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6730675816360728698651009 5048006862270546523988257)
                  ·
                    refine ⟨3786005146702909892991193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5048006862270546523988257 3786005146702909892991193)
                    ·
                      refine ⟨2839503860027182419743395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3786005146702909892991193 2839503860027182419743395)
                      ·
                        rfl

theorem cell23_5529914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2].length) (baseStart_5529914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529914 prefixEnd_5529914 := by exact prefixLift 5529914
  have htrace : WordTrace (prefixWord ++ tailWord_5529914) baseStart_5529914 baseEnd_5529914 := by
    simpa [prefixWord, tailWord_5529914, baseEnd_5529914] using wordTrace_append hprefix tailTrace_5529914
  have hstable : (prefixWord ++ tailWord_5529914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529914).length < 2 ^ (prefixWord ++ tailWord_5529914).sum := by decide
  have hdescent : baseEnd_5529914 < baseStart_5529914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529916 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_5529916 : Nat := 118140960795 + 5529916 * 2 ^ 59
def prefixEnd_5529916 : Nat := 4983230072969 + 3 ^ 40 * 5529916 * 2
def baseEnd_5529916 : Nat := 946501628996163803972795

theorem tailTrace_5529916 : CollatzResearch.WordTrace tailWord_5529916 prefixEnd_5529916 946501628996163803972795 := by
  unfold tailWord_5529916
  simp only [CollatzResearch.WordTrace]
  refine ⟨100846303117033120653820801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134461737489377494205094401 100846303117033120653820801)
  ·
    refine ⟨75634727337774840490365601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100846303117033120653820801 75634727337774840490365601)
    ·
      refine ⟨56726045503331130367774201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75634727337774840490365601 56726045503331130367774201)
      ·
        refine ⟨42544534127498347775830651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56726045503331130367774201 42544534127498347775830651)
        ·
          refine ⟨63816801191247521663745977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42544534127498347775830651 63816801191247521663745977)
          ·
            refine ⟨47862600893435641247809483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63816801191247521663745977 47862600893435641247809483)
            ·
              refine ⟨71793901340153461871714225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47862600893435641247809483 71793901340153461871714225)
              ·
                refine ⟨53845426005115096403785669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71793901340153461871714225 53845426005115096403785669)
                ·
                  refine ⟨10096017375959080575709813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53845426005115096403785669 10096017375959080575709813)
                  ·
                    refine ⟨946501628996163803972795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10096017375959080575709813 946501628996163803972795)
                    ·
                      rfl

theorem cell23_5529916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_5529916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529916 prefixEnd_5529916 := by exact prefixLift 5529916
  have htrace : WordTrace (prefixWord ++ tailWord_5529916) baseStart_5529916 baseEnd_5529916 := by
    simpa [prefixWord, tailWord_5529916, baseEnd_5529916] using wordTrace_append hprefix tailTrace_5529916
  have hstable : (prefixWord ++ tailWord_5529916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529916).length < 2 ^ (prefixWord ++ tailWord_5529916).sum := by decide
  have hdescent : baseEnd_5529916 < baseStart_5529916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529956 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_5529956 : Nat := 118140960795 + 5529956 * 2 ^ 59
def prefixEnd_5529956 : Nat := 4983230072969 + 3 ^ 40 * 5529956 * 2
def baseEnd_5529956 : Nat := 2839525426214671255418201

theorem tailTrace_5529956 : CollatzResearch.WordTrace tailWord_5529956 prefixEnd_5529956 2839525426214671255418201 := by
  unfold tailWord_5529956
  simp only [CollatzResearch.WordTrace]
  refine ⟨100847032576960664069548861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134462710102614218759398481 100847032576960664069548861)
  ·
    refine ⟨37817637216360249026080823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100847032576960664069548861 37817637216360249026080823)
    ·
      refine ⟨56726455824540373539121235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37817637216360249026080823 56726455824540373539121235)
      ·
        refine ⟨85089683736810560308681853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56726455824540373539121235 85089683736810560308681853)
        ·
          refine ⟨31908631401303960115755695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85089683736810560308681853 31908631401303960115755695)
          ·
            refine ⟨47862947101955940173633543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31908631401303960115755695 47862947101955940173633543)
            ·
              refine ⟨71794420652933910260450315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47862947101955940173633543 71794420652933910260450315)
              ·
                refine ⟨107691630979400865390675473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71794420652933910260450315 107691630979400865390675473)
                ·
                  refine ⟨80768723234550649043006605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107691630979400865390675473 80768723234550649043006605)
                  ·
                    refine ⟨30288271212956493391127477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80768723234550649043006605 30288271212956493391127477)
                    ·
                      refine ⟨2839525426214671255418201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30288271212956493391127477 2839525426214671255418201)
                      ·
                        rfl

theorem cell23_5529956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_5529956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529956 prefixEnd_5529956 := by exact prefixLift 5529956
  have htrace : WordTrace (prefixWord ++ tailWord_5529956) baseStart_5529956 baseEnd_5529956 := by
    simpa [prefixWord, tailWord_5529956, baseEnd_5529956] using wordTrace_append hprefix tailTrace_5529956
  have hstable : (prefixWord ++ tailWord_5529956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529956).length < 2 ^ (prefixWord ++ tailWord_5529956).sum := by decide
  have hdescent : baseEnd_5529956 < baseStart_5529956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529970 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 2, 4, 2]
def baseStart_5529970 : Nat := 118140960795 + 5529970 * 2 ^ 59
def prefixEnd_5529970 : Nat := 4983230072969 + 3 ^ 40 * 5529970 * 2
def baseEnd_5529970 : Nat := 2839532614943834200643137

theorem tailTrace_5529970 : CollatzResearch.WordTrace tailWord_5529970 prefixEnd_5529970 2839532614943834200643137 := by
  unfold tailWord_5529970
  simp only [CollatzResearch.WordTrace]
  refine ⟨50423643943967652132526841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134463050517247072353404909 50423643943967652132526841)
  ·
    refine ⟨37817732957975739099395131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50423643943967652132526841 37817732957975739099395131)
    ·
      refine ⟨56726599436963608649092697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37817732957975739099395131 56726599436963608649092697)
      ·
        refine ⟨42544949577722706486819523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56726599436963608649092697 42544949577722706486819523)
        ·
          refine ⟨63817424366584059730229285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42544949577722706486819523 63817424366584059730229285)
          ·
            refine ⟨11965767068734511199417991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63817424366584059730229285 11965767068734511199417991)
            ·
              refine ⟨17948650603101766799126987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11965767068734511199417991 17948650603101766799126987)
              ·
                refine ⟨26922975904652650198690481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17948650603101766799126987 26922975904652650198690481)
                ·
                  refine ⟨20192231928489487649017861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26922975904652650198690481 20192231928489487649017861)
                  ·
                    refine ⟨3786043486591778934190849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20192231928489487649017861 3786043486591778934190849)
                    ·
                      refine ⟨2839532614943834200643137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3786043486591778934190849 2839532614943834200643137)
                      ·
                        rfl

theorem cell23_5529970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_5529970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529970 prefixEnd_5529970 := by exact prefixLift 5529970
  have htrace : WordTrace (prefixWord ++ tailWord_5529970) baseStart_5529970 baseEnd_5529970 := by
    simpa [prefixWord, tailWord_5529970, baseEnd_5529970] using wordTrace_append hprefix tailTrace_5529970
  have hstable : (prefixWord ++ tailWord_5529970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529970).length < 2 ^ (prefixWord ++ tailWord_5529970).sum := by decide
  have hdescent : baseEnd_5529970 < baseStart_5529970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5529987 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 2, 1, 4]
def baseStart_5529987 : Nat := 118140960795 + 5529987 * 2 ^ 59
def prefixEnd_5529987 : Nat := 4983230072969 + 3 ^ 40 * 5529987 * 2
def baseEnd_5529987 : Nat := 2839541344114960634130559

theorem tailTrace_5529987 : CollatzResearch.WordTrace tailWord_5529987 prefixEnd_5529987 2839541344114960634130559 := by
  unfold tailWord_5529987
  simp only [CollatzResearch.WordTrace]
  refine ⟨201695195816809020433476215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134463463877872680288984143 201695195816809020433476215)
  ·
    refine ⟨302542793725213530650214323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201695195816809020433476215 302542793725213530650214323)
    ·
      refine ⟨453814190587820295975321485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302542793725213530650214323 453814190587820295975321485)
      ·
        refine ⟨170180321470432610990745557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 453814190587820295975321485 170180321470432610990745557)
        ·
          refine ⟨3988601284463264320095599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 170180321470432610990745557 3988601284463264320095599)
          ·
            refine ⟨5982901926694896480143399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988601284463264320095599 5982901926694896480143399)
            ·
              refine ⟨8974352890042344720215099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5982901926694896480143399 8974352890042344720215099)
              ·
                refine ⟨13461529335063517080322649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8974352890042344720215099 13461529335063517080322649)
                ·
                  refine ⟨10096147001297637810241987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13461529335063517080322649 10096147001297637810241987)
                  ·
                    refine ⟨15144220501946456715362981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10096147001297637810241987 15144220501946456715362981)
                    ·
                      refine ⟨2839541344114960634130559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15144220501946456715362981 2839541344114960634130559)
                      ·
                        rfl

theorem cell23_5529987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 1, 4].length) (baseStart_5529987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5529987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5529987 prefixEnd_5529987 := by exact prefixLift 5529987
  have htrace : WordTrace (prefixWord ++ tailWord_5529987) baseStart_5529987 baseEnd_5529987 := by
    simpa [prefixWord, tailWord_5529987, baseEnd_5529987] using wordTrace_append hprefix tailTrace_5529987
  have hstable : (prefixWord ++ tailWord_5529987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5529987).length < 2 ^ (prefixWord ++ tailWord_5529987).sum := by decide
  have hdescent : baseEnd_5529987 < baseStart_5529987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5529987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530010 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 6]
def baseStart_5530010 : Nat := 118140960795 + 5530010 * 2 ^ 59
def prefixEnd_5530010 : Nat := 4983230072969 + 3 ^ 40 * 5530010 * 2
def baseEnd_5530010 : Nat := 315505906018890449349217

theorem tailTrace_5530010 : CollatzResearch.WordTrace tailWord_5530010 prefixEnd_5530010 315505906018890449349217 := by
  unfold tailWord_5530010
  simp only [CollatzResearch.WordTrace]
  refine ⟨50424008673931423840390871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134464023130483796907708989 50424008673931423840390871)
  ·
    refine ⟨75636013010897135760586307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50424008673931423840390871 75636013010897135760586307)
    ·
      refine ⟨113454019516345703640879461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75636013010897135760586307 113454019516345703640879461)
      ·
        refine ⟨21272628659314819432664899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113454019516345703640879461 21272628659314819432664899)
        ·
          refine ⟨31908942988972229148997349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21272628659314819432664899 31908942988972229148997349)
          ·
            refine ⟨5982926810432292965437003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31908942988972229148997349 5982926810432292965437003)
            ·
              refine ⟨8974390215648439448155505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5982926810432292965437003 8974390215648439448155505)
              ·
                refine ⟨6730792661736329586116629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8974390215648439448155505 6730792661736329586116629)
                ·
                  refine ⟨315505906018890449349217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6730792661736329586116629 315505906018890449349217)
                  ·
                    rfl

theorem cell23_5530010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_5530010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530010 prefixEnd_5530010 := by exact prefixLift 5530010
  have htrace : WordTrace (prefixWord ++ tailWord_5530010) baseStart_5530010 baseEnd_5530010 := by
    simpa [prefixWord, tailWord_5530010, baseEnd_5530010] using wordTrace_append hprefix tailTrace_5530010
  have hstable : (prefixWord ++ tailWord_5530010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530010).length < 2 ^ (prefixWord ++ tailWord_5530010).sum := by decide
  have hdescent : baseEnd_5530010 < baseStart_5530010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530014 : List Nat := [4, 3, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_5530014 : Nat := 118140960795 + 5530014 * 2 ^ 59
def prefixEnd_5530014 : Nat := 4983230072969 + 3 ^ 40 * 5530014 * 2
def baseEnd_5530014 : Nat := 946518402697544009497645

theorem tailTrace_5530014 : CollatzResearch.WordTrace tailWord_5530014 prefixEnd_5530014 946518402697544009497645 := by
  unfold tailWord_5530014
  simp only [CollatzResearch.WordTrace]
  refine ⟨25212022573463900505588637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134464120391807469363139397 25212022573463900505588637)
  ·
    refine ⟨9454508465048962689595739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25212022573463900505588637 9454508465048962689595739)
    ·
      refine ⟨14181762697573444034393609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9454508465048962689595739 14181762697573444034393609)
      ·
        refine ⟨10636322023180083025795207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14181762697573444034393609 10636322023180083025795207)
        ·
          refine ⟨15954483034770124538692811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10636322023180083025795207 15954483034770124538692811)
          ·
            refine ⟨23931724552155186808039217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15954483034770124538692811 23931724552155186808039217)
            ·
              refine ⟨17948793414116390106029413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23931724552155186808039217 17948793414116390106029413)
              ·
                refine ⟨3365398765146823144880515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17948793414116390106029413 3365398765146823144880515)
                ·
                  refine ⟨5048098147720234717320773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3365398765146823144880515 5048098147720234717320773)
                  ·
                    refine ⟨946518402697544009497645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5048098147720234717320773 946518402697544009497645)
                    ·
                      rfl

theorem cell23_5530014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_5530014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530014 prefixEnd_5530014 := by exact prefixLift 5530014
  have htrace : WordTrace (prefixWord ++ tailWord_5530014) baseStart_5530014 baseEnd_5530014 := by
    simpa [prefixWord, tailWord_5530014, baseEnd_5530014] using wordTrace_append hprefix tailTrace_5530014
  have hstable : (prefixWord ++ tailWord_5530014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530014).length < 2 ^ (prefixWord ++ tailWord_5530014).sum := by decide
  have hdescent : baseEnd_5530014 < baseStart_5530014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530020 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_5530020 : Nat := 118140960795 + 5530020 * 2 ^ 59
def prefixEnd_5530020 : Nat := 4983230072969 + 3 ^ 40 * 5530020 * 2
def baseEnd_5530020 : Nat := 2839558288976559005017907

theorem tailTrace_5530020 : CollatzResearch.WordTrace tailWord_5530020 prefixEnd_5530020 2839558288976559005017907 := by
  unfold tailWord_5530020
  simp only [CollatzResearch.WordTrace]
  refine ⟨100848199712844733534713757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134464266283792978046285009 100848199712844733534713757)
  ·
    refine ⟨37818074892316775075517659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100848199712844733534713757 37818074892316775075517659)
    ·
      refine ⟨56727112338475162613276489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37818074892316775075517659 56727112338475162613276489)
      ·
        refine ⟨42545334253856371959957367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56727112338475162613276489 42545334253856371959957367)
        ·
          refine ⟨63818001380784557939936051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42545334253856371959957367 63818001380784557939936051)
          ·
            refine ⟨95727002071176836909904077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63818001380784557939936051 95727002071176836909904077)
            ·
              refine ⟨35897625776691313841214029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95727002071176836909904077 35897625776691313841214029)
              ·
                refine ⟨13461609666259242690455261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35897625776691313841214029 13461609666259242690455261)
                ·
                  refine ⟨5048103624847216008920723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13461609666259242690455261 5048103624847216008920723)
                  ·
                    refine ⟨7572155437270824013381085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5048103624847216008920723 7572155437270824013381085)
                    ·
                      refine ⟨2839558288976559005017907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7572155437270824013381085 2839558288976559005017907)
                      ·
                        rfl

theorem cell23_5530020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_5530020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530020 prefixEnd_5530020 := by exact prefixLift 5530020
  have htrace : WordTrace (prefixWord ++ tailWord_5530020) baseStart_5530020 baseEnd_5530020 := by
    simpa [prefixWord, tailWord_5530020, baseEnd_5530020] using wordTrace_append hprefix tailTrace_5530020
  have hstable : (prefixWord ++ tailWord_5530020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530020).length < 2 ^ (prefixWord ++ tailWord_5530020).sum := by decide
  have hdescent : baseEnd_5530020 < baseStart_5530020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530063 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 3]
def baseStart_5530063 : Nat := 118140960795 + 5530063 * 2 ^ 59
def prefixEnd_5530063 : Nat := 4983230072969 + 3 ^ 40 * 5530063 * 2
def baseEnd_5530063 : Nat := 2839580368644702336780209

theorem tailTrace_5530063 : CollatzResearch.WordTrace tailWord_5530063 prefixEnd_5530063 2839580368644702336780209 := by
  unfold tailWord_5530063
  simp only [CollatzResearch.WordTrace]
  refine ⟨201697967764533685413242843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134465311843022456942161895 201697967764533685413242843)
  ·
    refine ⟨302546951646800528119864265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201697967764533685413242843 302546951646800528119864265)
    ·
      refine ⟨226910213735100396089898199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302546951646800528119864265 226910213735100396089898199)
      ·
        refine ⟨340365320602650594134847299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226910213735100396089898199 340365320602650594134847299)
        ·
          refine ⟨510547980903975891202270949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340365320602650594134847299 510547980903975891202270949)
          ·
            refine ⟨95727746419495479600425803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 510547980903975891202270949 95727746419495479600425803)
            ·
              refine ⟨143591619629243219400638705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95727746419495479600425803 143591619629243219400638705)
              ·
                refine ⟨107693714721932414550479029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143591619629243219400638705 107693714721932414550479029)
                ·
                  refine ⟨10096285755181163864107409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107693714721932414550479029 10096285755181163864107409)
                  ·
                    refine ⟨7572214316385872898080557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10096285755181163864107409 7572214316385872898080557)
                    ·
                      refine ⟨2839580368644702336780209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7572214316385872898080557 2839580368644702336780209)
                      ·
                        rfl

theorem cell23_5530063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 3].length) (baseStart_5530063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530063 prefixEnd_5530063 := by exact prefixLift 5530063
  have htrace : WordTrace (prefixWord ++ tailWord_5530063) baseStart_5530063 baseEnd_5530063 := by
    simpa [prefixWord, tailWord_5530063, baseEnd_5530063] using wordTrace_append hprefix tailTrace_5530063
  have hstable : (prefixWord ++ tailWord_5530063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530063).length < 2 ^ (prefixWord ++ tailWord_5530063).sum := by decide
  have hdescent : baseEnd_5530063 < baseStart_5530063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530114 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_5530114 : Nat := 118140960795 + 5530114 * 2 ^ 59
def prefixEnd_5530114 : Nat := 4983230072969 + 3 ^ 40 * 5530114 * 2
def baseEnd_5530114 : Nat := 2839606556158081637242475

theorem tailTrace_5530114 : CollatzResearch.WordTrace tailWord_5530114 prefixEnd_5530114 2839606556158081637242475 := by
  unfold tailWord_5530114
  simp only [CollatzResearch.WordTrace]
  refine ⟨50424956971837230280837349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134466551924899280748899597 50424956971837230280837349)
  ·
    refine ⟨9454679432219480677657003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50424956971837230280837349 9454679432219480677657003)
    ·
      refine ⟨14182019148329221016485505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9454679432219480677657003 14182019148329221016485505)
      ·
        refine ⟨10636514361246915762364129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14182019148329221016485505 10636514361246915762364129)
        ·
          refine ⟨7977385770935186821773097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10636514361246915762364129 7977385770935186821773097)
          ·
            refine ⟨5983039328201390116329823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7977385770935186821773097 5983039328201390116329823)
            ·
              refine ⟨8974558992302085174494735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5983039328201390116329823 8974558992302085174494735)
              ·
                refine ⟨13461838488453127761742103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8974558992302085174494735 13461838488453127761742103)
                ·
                  refine ⟨20192757732679691642613155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13461838488453127761742103 20192757732679691642613155)
                  ·
                    refine ⟨30289136599019537463919733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20192757732679691642613155 30289136599019537463919733)
                    ·
                      refine ⟨2839606556158081637242475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30289136599019537463919733 2839606556158081637242475)
                      ·
                        rfl

theorem cell23_5530114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_5530114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530114 prefixEnd_5530114 := by exact prefixLift 5530114
  have htrace : WordTrace (prefixWord ++ tailWord_5530114) baseStart_5530114 baseEnd_5530114 := by
    simpa [prefixWord, tailWord_5530114, baseEnd_5530114] using wordTrace_append hprefix tailTrace_5530114
  have hstable : (prefixWord ++ tailWord_5530114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530114).length < 2 ^ (prefixWord ++ tailWord_5530114).sum := by decide
  have hdescent : baseEnd_5530114 < baseStart_5530114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530133 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_5530133 : Nat := 118140960795 + 5530133 * 2 ^ 59
def prefixEnd_5530133 : Nat := 4983230072969 + 3 ^ 40 * 5530133 * 2
def baseEnd_5530133 : Nat := 2839616312290517062904887

theorem tailTrace_5530133 : CollatzResearch.WordTrace tailWord_5530133 prefixEnd_5530133 2839616312290517062904887 := by
  unfold tailWord_5530133
  simp only [CollatzResearch.WordTrace]
  refine ⟨201700520874280087368291053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134467013916186724912194035 201700520874280087368291053)
  ·
    refine ⟨75637695327855032763109145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201700520874280087368291053 75637695327855032763109145)
    ·
      refine ⟨56728271495891274572331859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75637695327855032763109145 56728271495891274572331859)
      ·
        refine ⟨85092407243836911858497789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56728271495891274572331859 85092407243836911858497789)
        ·
          refine ⟨31909652716438841946936671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85092407243836911858497789 31909652716438841946936671)
          ·
            refine ⟨47864479074658262920405007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31909652716438841946936671 47864479074658262920405007)
            ·
              refine ⟨71796718611987394380607511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47864479074658262920405007 71796718611987394380607511)
              ·
                refine ⟨107695077917981091570911267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71796718611987394380607511 107695077917981091570911267)
                ·
                  refine ⟨161542616876971637356366901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107695077917981091570911267 161542616876971637356366901)
                  ·
                    refine ⟨15144620332216091002159397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 161542616876971637356366901 15144620332216091002159397)
                    ·
                      refine ⟨2839616312290517062904887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15144620332216091002159397 2839616312290517062904887)
                      ·
                        rfl

theorem cell23_5530133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_5530133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530133 prefixEnd_5530133 := by exact prefixLift 5530133
  have htrace : WordTrace (prefixWord ++ tailWord_5530133) baseStart_5530133 baseEnd_5530133 := by
    simpa [prefixWord, tailWord_5530133, baseEnd_5530133] using wordTrace_append hprefix tailTrace_5530133
  have hstable : (prefixWord ++ tailWord_5530133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530133).length < 2 ^ (prefixWord ++ tailWord_5530133).sum := by decide
  have hdescent : baseEnd_5530133 < baseStart_5530133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530163 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 4]
def baseStart_5530163 : Nat := 118140960795 + 5530163 * 2 ^ 59
def prefixEnd_5530163 : Nat := 4983230072969 + 3 ^ 40 * 5530163 * 2
def baseEnd_5530163 : Nat := 2839631716710151945529749

theorem tailTrace_5530163 : CollatzResearch.WordTrace tailWord_5530163 prefixEnd_5530163 2839631716710151945529749 := by
  unfold tailWord_5530163
  simp only [CollatzResearch.WordTrace]
  refine ⟨201701615064171402491883143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134467743376114268327922095 201701615064171402491883143)
  ·
    refine ⟨302552422596257103737824715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201701615064171402491883143 302552422596257103737824715)
    ·
      refine ⟨453828633894385655606737073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302552422596257103737824715 453828633894385655606737073)
      ·
        refine ⟨340371475420789241705052805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453828633894385655606737073 340371475420789241705052805)
        ·
          refine ⟨63819651641397982819697401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340371475420789241705052805 63819651641397982819697401)
          ·
            refine ⟨47864738731048487114773051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63819651641397982819697401 47864738731048487114773051)
            ·
              refine ⟨71797108096572730672159577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47864738731048487114773051 71797108096572730672159577)
              ·
                refine ⟨53847831072429548004119683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71797108096572730672159577 53847831072429548004119683)
                ·
                  refine ⟨80771746608644322006179525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53847831072429548004119683 80771746608644322006179525)
                  ·
                    refine ⟨15144702489120810376158661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80771746608644322006179525 15144702489120810376158661)
                    ·
                      refine ⟨2839631716710151945529749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15144702489120810376158661 2839631716710151945529749)
                      ·
                        rfl

theorem cell23_5530163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_5530163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530163 prefixEnd_5530163 := by exact prefixLift 5530163
  have htrace : WordTrace (prefixWord ++ tailWord_5530163) baseStart_5530163 baseEnd_5530163 := by
    simpa [prefixWord, tailWord_5530163, baseEnd_5530163] using wordTrace_append hprefix tailTrace_5530163
  have hstable : (prefixWord ++ tailWord_5530163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530163).length < 2 ^ (prefixWord ++ tailWord_5530163).sum := by decide
  have hdescent : baseEnd_5530163 < baseStart_5530163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530167 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 4, 2, 2]
def baseStart_5530167 : Nat := 118140960795 + 5530167 * 2 ^ 59
def prefixEnd_5530167 : Nat := 4983230072969 + 3 ^ 40 * 5530167 * 2
def baseEnd_5530167 : Nat := 2839633770632769929879731

theorem tailTrace_5530167 : CollatzResearch.WordTrace tailWord_5530167 prefixEnd_5530167 2839633770632769929879731 := by
  unfold tailWord_5530167
  simp only [CollatzResearch.WordTrace]
  refine ⟨201701760956156911175028755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134467840637437940783352503 201701760956156911175028755)
  ·
    refine ⟨302552641434235366762543133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201701760956156911175028755 302552641434235366762543133)
    ·
      refine ⟨113457240537838262535953675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302552641434235366762543133 113457240537838262535953675)
      ·
        refine ⟨170185860806757393803930513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113457240537838262535953675 170185860806757393803930513)
        ·
          refine ⟨127639395605068045352947885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170185860806757393803930513 127639395605068045352947885)
          ·
            refine ⟨47864773351900517007355457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127639395605068045352947885 47864773351900517007355457)
            ·
              refine ⟨35898580013925387755516593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47864773351900517007355457 35898580013925387755516593)
              ·
                refine ⟨26923935010444040816637445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35898580013925387755516593 26923935010444040816637445)
                ·
                  refine ⟨5048237814458257653119521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26923935010444040816637445 5048237814458257653119521)
                  ·
                    refine ⟨3786178360843693239839641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5048237814458257653119521 3786178360843693239839641)
                    ·
                      refine ⟨2839633770632769929879731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3786178360843693239839641 2839633770632769929879731)
                      ·
                        rfl

theorem cell23_5530167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 2, 2].length) (baseStart_5530167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530167 prefixEnd_5530167 := by exact prefixLift 5530167
  have htrace : WordTrace (prefixWord ++ tailWord_5530167) baseStart_5530167 baseEnd_5530167 := by
    simpa [prefixWord, tailWord_5530167, baseEnd_5530167] using wordTrace_append hprefix tailTrace_5530167
  have hstable : (prefixWord ++ tailWord_5530167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530167).length < 2 ^ (prefixWord ++ tailWord_5530167).sum := by decide
  have hdescent : baseEnd_5530167 < baseStart_5530167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530200 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 2, 3, 3]
def baseStart_5530200 : Nat := 118140960795 + 5530200 * 2 ^ 59
def prefixEnd_5530200 : Nat := 4983230072969 + 3 ^ 40 * 5530200 * 2
def baseEnd_5530200 : Nat := 2839650715494368300767079

theorem tailTrace_5530200 : CollatzResearch.WordTrace tailWord_5530200 prefixEnd_5530200 2839650715494368300767079 := by
  unfold tailWord_5530200
  simp only [CollatzResearch.WordTrace]
  refine ⟨100851482282518678905490027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134468643043358238540653369 100851482282518678905490027)
  ·
    refine ⟨151277223423778018358235041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100851482282518678905490027 151277223423778018358235041)
    ·
      refine ⟨113457917567833513768676281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151277223423778018358235041 113457917567833513768676281)
      ·
        refine ⟨85093438175875135326507211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113457917567833513768676281 85093438175875135326507211)
        ·
          refine ⟨127640157263812702989760817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85093438175875135326507211 127640157263812702989760817)
          ·
            refine ⟨95730117947859527242320613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127640157263812702989760817 95730117947859527242320613)
            ·
              refine ⟨17949397115223661357935115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95730117947859527242320613 17949397115223661357935115)
              ·
                refine ⟨26924095672835492036902673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17949397115223661357935115 26924095672835492036902673)
                ·
                  refine ⟨20193071754626619027677005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26924095672835492036902673 20193071754626619027677005)
                  ·
                    refine ⟨7572401907984982135378877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20193071754626619027677005 7572401907984982135378877)
                    ·
                      refine ⟨2839650715494368300767079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7572401907984982135378877 2839650715494368300767079)
                      ·
                        rfl

theorem cell23_5530200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_5530200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530200 prefixEnd_5530200 := by exact prefixLift 5530200
  have htrace : WordTrace (prefixWord ++ tailWord_5530200) baseStart_5530200 baseEnd_5530200 := by
    simpa [prefixWord, tailWord_5530200, baseEnd_5530200] using wordTrace_append hprefix tailTrace_5530200
  have hstable : (prefixWord ++ tailWord_5530200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530200).length < 2 ^ (prefixWord ++ tailWord_5530200).sum := by decide
  have hdescent : baseEnd_5530200 < baseStart_5530200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530224 : List Nat := [2, 1, 1, 1, 7, 2, 1, 3, 5]
def baseStart_5530224 : Nat := 118140960795 + 5530224 * 2 ^ 59
def prefixEnd_5530224 : Nat := 4983230072969 + 3 ^ 40 * 5530224 * 2
def baseEnd_5530224 : Nat := 315518115447786245207441

theorem tailTrace_5530224 : CollatzResearch.WordTrace tailWord_5530224 prefixEnd_5530224 315518115447786245207441 := by
  unfold tailWord_5530224
  simp only [CollatzResearch.WordTrace]
  refine ⟨100851919958475204954926863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134469226611300273273235817 100851919958475204954926863)
  ·
    refine ⟨151277879937712807432390295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100851919958475204954926863 151277879937712807432390295)
    ·
      refine ⟨226916819906569211148585443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151277879937712807432390295 226916819906569211148585443)
      ·
        refine ⟨340375229859853816722878165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226916819906569211148585443 340375229859853816722878165)
        ·
          refine ⟨7977544449840323829442457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 340375229859853816722878165 7977544449840323829442457)
          ·
            refine ⟨5983158337380242872081843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7977544449840323829442457 5983158337380242872081843)
            ·
              refine ⟨8974737506070364308122765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5983158337380242872081843 8974737506070364308122765)
              ·
                refine ⟨3365526564776386615546037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8974737506070364308122765 3365526564776386615546037)
                ·
                  refine ⟨315518115447786245207441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3365526564776386615546037 315518115447786245207441)
                  ·
                    rfl

theorem cell23_5530224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 5].length) (baseStart_5530224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530224 prefixEnd_5530224 := by exact prefixLift 5530224
  have htrace : WordTrace (prefixWord ++ tailWord_5530224) baseStart_5530224 baseEnd_5530224 := by
    simpa [prefixWord, tailWord_5530224, baseEnd_5530224] using wordTrace_append hprefix tailTrace_5530224
  have hstable : (prefixWord ++ tailWord_5530224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530224).length < 2 ^ (prefixWord ++ tailWord_5530224).sum := by decide
  have hdescent : baseEnd_5530224 < baseStart_5530224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530237 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_5530237 : Nat := 118140960795 + 5530237 * 2 ^ 59
def prefixEnd_5530237 : Nat := 4983230072969 + 3 ^ 40 * 5530237 * 2
def baseEnd_5530237 : Nat := 946556571426194885334803

theorem tailTrace_5530237 : CollatzResearch.WordTrace tailWord_5530237 prefixEnd_5530237 946556571426194885334803 := by
  unfold tailWord_5530237
  simp only [CollatzResearch.WordTrace]
  refine ⟨201704314065903313130076965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134469542710602208753384643 201704314065903313130076965)
  ·
    refine ⟨37819558887356871211889431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201704314065903313130076965 37819558887356871211889431)
    ·
      refine ⟨56729338331035306817834147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37819558887356871211889431 56729338331035306817834147)
      ·
        refine ⟨85094007496552960226751221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56729338331035306817834147 85094007496552960226751221)
        ·
          refine ⟨7977563202801840021257927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85094007496552960226751221 7977563202801840021257927)
          ·
            refine ⟨11966344804202760031886891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7977563202801840021257927 11966344804202760031886891)
            ·
              refine ⟨17949517206304140047830337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11966344804202760031886891 17949517206304140047830337)
              ·
                refine ⟨13462137904728105035872753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17949517206304140047830337 13462137904728105035872753)
                ·
                  refine ⟨10096603428546078776904565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13462137904728105035872753 10096603428546078776904565)
                  ·
                    refine ⟨946556571426194885334803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10096603428546078776904565 946556571426194885334803)
                    ·
                      rfl

theorem cell23_5530237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_5530237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530237 prefixEnd_5530237 := by exact prefixLift 5530237
  have htrace : WordTrace (prefixWord ++ tailWord_5530237) baseStart_5530237 baseEnd_5530237 := by
    simpa [prefixWord, tailWord_5530237, baseEnd_5530237] using wordTrace_append hprefix tailTrace_5530237
  have hstable : (prefixWord ++ tailWord_5530237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530237).length < 2 ^ (prefixWord ++ tailWord_5530237).sum := by decide
  have hdescent : baseEnd_5530237 < baseStart_5530237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530240 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 4]
def baseStart_5530240 : Nat := 118140960795 + 5530240 * 2 ^ 59
def prefixEnd_5530240 : Nat := 4983230072969 + 3 ^ 40 * 5530240 * 2
def baseEnd_5530240 : Nat := 2839671254720548144266895

theorem tailTrace_5530240 : CollatzResearch.WordTrace tailWord_5530240 prefixEnd_5530240 2839671254720548144266895 := by
  unfold tailWord_5530240
  simp only [CollatzResearch.WordTrace]
  refine ⟨100852211742446222321218087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134469615656594963094957449 100852211742446222321218087)
  ·
    refine ⟨151278317613669333481827131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100852211742446222321218087 151278317613669333481827131)
    ·
      refine ⟨226917476420504000222740697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151278317613669333481827131 226917476420504000222740697)
      ·
        refine ⟨170188107315378000167055523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226917476420504000222740697 170188107315378000167055523)
        ·
          refine ⟨255282160973067000250583285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170188107315378000167055523 255282160973067000250583285)
          ·
            refine ⟨23932702591225031273492183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 255282160973067000250583285 23932702591225031273492183)
            ·
              refine ⟨35899053886837546910238275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23932702591225031273492183 35899053886837546910238275)
              ·
                refine ⟨53848580830256320365357413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35899053886837546910238275 53848580830256320365357413)
                ·
                  refine ⟨10096608905673060068504515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53848580830256320365357413 10096608905673060068504515)
                  ·
                    refine ⟨15144913358509590102756773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10096608905673060068504515 15144913358509590102756773)
                    ·
                      refine ⟨2839671254720548144266895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15144913358509590102756773 2839671254720548144266895)
                      ·
                        rfl

theorem cell23_5530240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_5530240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530240 prefixEnd_5530240 := by exact prefixLift 5530240
  have htrace : WordTrace (prefixWord ++ tailWord_5530240) baseStart_5530240 baseEnd_5530240 := by
    simpa [prefixWord, tailWord_5530240, baseEnd_5530240] using wordTrace_append hprefix tailTrace_5530240
  have hstable : (prefixWord ++ tailWord_5530240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530240).length < 2 ^ (prefixWord ++ tailWord_5530240).sum := by decide
  have hdescent : baseEnd_5530240 < baseStart_5530240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530300 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_5530300 : Nat := 118140960795 + 5530300 * 2 ^ 59
def prefixEnd_5530300 : Nat := 4983230072969 + 3 ^ 40 * 5530300 * 2
def baseEnd_5530300 : Nat := 2839702063559817909516619

theorem tailTrace_5530300 : CollatzResearch.WordTrace tailWord_5530300 prefixEnd_5530300 2839702063559817909516619 := by
  unfold tailWord_5530300
  simp only [CollatzResearch.WordTrace]
  refine ⟨100853305932337537444810177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134471074576450049926413569 100853305932337537444810177)
  ·
    refine ⟨75639979449253153083607633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100853305932337537444810177 75639979449253153083607633)
    ·
      refine ⟨56729984586939864812705725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75639979449253153083607633 56729984586939864812705725)
      ·
        refine ⟨21273744220102449304764647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56729984586939864812705725 21273744220102449304764647)
        ·
          refine ⟨31910616330153673957146971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21273744220102449304764647 31910616330153673957146971)
          ·
            refine ⟨47865924495230510935720457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31910616330153673957146971 47865924495230510935720457)
            ·
              refine ⟨35899443371422883201790343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47865924495230510935720457 35899443371422883201790343)
              ·
                refine ⟨53849165057134324802685515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35899443371422883201790343 53849165057134324802685515)
                ·
                  refine ⟨80773747585701487204028273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53849165057134324802685515 80773747585701487204028273)
                  ·
                    refine ⟨60580310689276115403021205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80773747585701487204028273 60580310689276115403021205)
                    ·
                      refine ⟨2839702063559817909516619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60580310689276115403021205 2839702063559817909516619)
                      ·
                        rfl

theorem cell23_5530300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_5530300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530300 prefixEnd_5530300 := by exact prefixLift 5530300
  have htrace : WordTrace (prefixWord ++ tailWord_5530300) baseStart_5530300 baseEnd_5530300 := by
    simpa [prefixWord, tailWord_5530300, baseEnd_5530300] using wordTrace_append hprefix tailTrace_5530300
  have hstable : (prefixWord ++ tailWord_5530300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530300).length < 2 ^ (prefixWord ++ tailWord_5530300).sum := by decide
  have hdescent : baseEnd_5530300 < baseStart_5530300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530301 : List Nat := [1, 4, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_5530301 : Nat := 118140960795 + 5530301 * 2 ^ 59
def prefixEnd_5530301 : Nat := 4983230072969 + 3 ^ 40 * 5530301 * 2
def baseEnd_5530301 : Nat := 946567525680157468534705

theorem tailTrace_5530301 : CollatzResearch.WordTrace tailWord_5530301 prefixEnd_5530301 946567525680157468534705 := by
  unfold tailWord_5530301
  simp only [CollatzResearch.WordTrace]
  refine ⟨201706648337671452060406757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134471098891780968040271171 201706648337671452060406757)
  ·
    refine ⟨37819996563313397261326267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201706648337671452060406757 37819996563313397261326267)
    ·
      refine ⟨56729994844970095891989401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37819996563313397261326267 56729994844970095891989401)
      ·
        refine ⟨42547496133727571918992051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56729994844970095891989401 42547496133727571918992051)
        ·
          refine ⟨63821244200591357878488077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42547496133727571918992051 63821244200591357878488077)
          ·
            refine ⟨23932966575221759204433029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63821244200591357878488077 23932966575221759204433029)
            ·
              refine ⟨4487431232854079850831193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23932966575221759204433029 4487431232854079850831193)
              ·
                refine ⟨3365573424640559888123395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4487431232854079850831193 3365573424640559888123395)
                ·
                  refine ⟨5048360136960839832185093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3365573424640559888123395 5048360136960839832185093)
                  ·
                    refine ⟨946567525680157468534705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5048360136960839832185093 946567525680157468534705)
                    ·
                      rfl

theorem cell23_5530301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_5530301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530301 prefixEnd_5530301 := by exact prefixLift 5530301
  have htrace : WordTrace (prefixWord ++ tailWord_5530301) baseStart_5530301 baseEnd_5530301 := by
    simpa [prefixWord, tailWord_5530301, baseEnd_5530301] using wordTrace_append hprefix tailTrace_5530301
  have hstable : (prefixWord ++ tailWord_5530301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530301).length < 2 ^ (prefixWord ++ tailWord_5530301).sum := by decide
  have hdescent : baseEnd_5530301 < baseStart_5530301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530341 : List Nat := [1, 3, 1, 4, 1, 2, 1, 5, 1, 1, 3]
def baseStart_5530341 : Nat := 118140960795 + 5530341 * 2 ^ 59
def prefixEnd_5530341 : Nat := 4983230072969 + 3 ^ 40 * 5530341 * 2
def baseEnd_5530341 : Nat := 2839723116266652249103931

theorem tailTrace_5530341 : CollatzResearch.WordTrace tailWord_5530341 prefixEnd_5530341 2839723116266652249103931 := by
  unfold tailWord_5530341
  simp only [CollatzResearch.WordTrace]
  refine ⟨201708107257526538891862877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134472071505017692594575251 201708107257526538891862877)
  ·
    refine ⟨75640540221572452084448579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201708107257526538891862877 75640540221572452084448579)
    ·
      refine ⟨113460810332358678126672869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75640540221572452084448579 113460810332358678126672869)
      ·
        refine ⟨21273901937317252148751163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113460810332358678126672869 21273901937317252148751163)
        ·
          refine ⟨31910852905975878223126745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21273901937317252148751163 31910852905975878223126745)
          ·
            refine ⟨23933139679481908667345059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31910852905975878223126745 23933139679481908667345059)
            ·
              refine ⟨35899709519222863001017589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23933139679481908667345059 35899709519222863001017589)
              ·
                refine ⟨3365597767427143406345399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35899709519222863001017589 3365597767427143406345399)
                ·
                  refine ⟨5048396651140715109518099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3365597767427143406345399 5048396651140715109518099)
                  ·
                    refine ⟨7572594976711072664277149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5048396651140715109518099 7572594976711072664277149)
                    ·
                      refine ⟨2839723116266652249103931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7572594976711072664277149 2839723116266652249103931)
                      ·
                        rfl

theorem cell23_5530341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_5530341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530341 prefixEnd_5530341 := by exact prefixLift 5530341
  have htrace : WordTrace (prefixWord ++ tailWord_5530341) baseStart_5530341 baseEnd_5530341 := by
    simpa [prefixWord, tailWord_5530341, baseEnd_5530341] using wordTrace_append hprefix tailTrace_5530341
  have hstable : (prefixWord ++ tailWord_5530341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530341).length < 2 ^ (prefixWord ++ tailWord_5530341).sum := by decide
  have hdescent : baseEnd_5530341 < baseStart_5530341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530344 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 1, 5]
def baseStart_5530344 : Nat := 118140960795 + 5530344 * 2 ^ 59
def prefixEnd_5530344 : Nat := 4983230072969 + 3 ^ 40 * 5530344 * 2
def baseEnd_5530344 : Nat := 946574885569538579122139

theorem tailTrace_5530344 : CollatzResearch.WordTrace tailWord_5530344 prefixEnd_5530344 946574885569538579122139 := by
  unfold tailWord_5530344
  simp only [CollatzResearch.WordTrace]
  refine ⟨100854108338257835202111043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134472144451010446936148057 100854108338257835202111043)
  ·
    refine ⟨151281162507386752803166565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100854108338257835202111043 151281162507386752803166565)
    ·
      refine ⟨28365217970135016150593731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151281162507386752803166565 28365217970135016150593731)
      ·
        refine ⟨42547826955202524225890597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28365217970135016150593731 42547826955202524225890597)
        ·
          refine ⟨7977717554100473292354487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42547826955202524225890597 7977717554100473292354487)
          ·
            refine ⟨11966576331150709938531731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7977717554100473292354487 11966576331150709938531731)
            ·
              refine ⟨17949864496726064907797597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11966576331150709938531731 17949864496726064907797597)
              ·
                refine ⟨6731199186272274340424099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17949864496726064907797597 6731199186272274340424099)
                ·
                  refine ⟨10096798779408411510636149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6731199186272274340424099 10096798779408411510636149)
                  ·
                    refine ⟨946574885569538579122139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10096798779408411510636149 946574885569538579122139)
                    ·
                      rfl

theorem cell23_5530344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_5530344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530344 prefixEnd_5530344 := by exact prefixLift 5530344
  have htrace : WordTrace (prefixWord ++ tailWord_5530344) baseStart_5530344 baseEnd_5530344 := by
    simpa [prefixWord, tailWord_5530344, baseEnd_5530344] using wordTrace_append hprefix tailTrace_5530344
  have hstable : (prefixWord ++ tailWord_5530344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530344).length < 2 ^ (prefixWord ++ tailWord_5530344).sum := by decide
  have hdescent : baseEnd_5530344 < baseStart_5530344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530360 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_5530360 : Nat := 118140960795 + 5530360 * 2 ^ 59
def prefixEnd_5530360 : Nat := 4983230072969 + 3 ^ 40 * 5530360 * 2
def baseEnd_5530360 : Nat := 2839732872399087674766343

theorem tailTrace_5530360 : CollatzResearch.WordTrace tailWord_5530360 prefixEnd_5530360 2839732872399087674766343 := by
  unfold tailWord_5530360
  simp only [CollatzResearch.WordTrace]
  refine ⟨100854400122228852568402267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134472533496305136757869689 100854400122228852568402267)
  ·
    refine ⟨151281600183343278852603401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100854400122228852568402267 151281600183343278852603401)
    ·
      refine ⟨113461200137507459139452551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151281600183343278852603401 113461200137507459139452551)
      ·
        refine ⟨170191800206261188709178827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113461200137507459139452551 170191800206261188709178827)
        ·
          refine ⟨255287700309391783063768241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170191800206261188709178827 255287700309391783063768241)
          ·
            refine ⟨191465775232043837297826181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255287700309391783063768241 191465775232043837297826181)
            ·
              refine ⟨35899832856008219493342409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191465775232043837297826181 35899832856008219493342409)
              ·
                refine ⟨26924874642006164620006807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35899832856008219493342409 26924874642006164620006807)
                ·
                  refine ⟨40387311963009246930010211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26924874642006164620006807 40387311963009246930010211)
                  ·
                    refine ⟨60580967944513870395015317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40387311963009246930010211 60580967944513870395015317)
                    ·
                      refine ⟨2839732872399087674766343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60580967944513870395015317 2839732872399087674766343)
                      ·
                        rfl

theorem cell23_5530360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_5530360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530360 prefixEnd_5530360 := by exact prefixLift 5530360
  have htrace : WordTrace (prefixWord ++ tailWord_5530360) baseStart_5530360 baseEnd_5530360 := by
    simpa [prefixWord, tailWord_5530360, baseEnd_5530360] using wordTrace_append hprefix tailTrace_5530360
  have hstable : (prefixWord ++ tailWord_5530360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530360).length < 2 ^ (prefixWord ++ tailWord_5530360).sum := by decide
  have hdescent : baseEnd_5530360 < baseStart_5530360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530377 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 4]
def baseStart_5530377 : Nat := 118140960795 + 5530377 * 2 ^ 59
def prefixEnd_5530377 : Nat := 4983230072969 + 3 ^ 40 * 5530377 * 2
def baseEnd_5530377 : Nat := 2839741601570214108253765

theorem tailTrace_5530377 : CollatzResearch.WordTrace tailWord_5530377 prefixEnd_5530377 2839741601570214108253765 := by
  unfold tailWord_5530377
  simp only [CollatzResearch.WordTrace]
  refine ⟨201709420285396117040173385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134472946856930744693448923 201709420285396117040173385)
  ·
    refine ⟨151282065214047087780130039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201709420285396117040173385 151282065214047087780130039)
    ·
      refine ⟨226923097821070631670195059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151282065214047087780130039 226923097821070631670195059)
      ·
        refine ⟨340384646731605947505292589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226923097821070631670195059 340384646731605947505292589)
        ·
          refine ⟨127644242524352230314484721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340384646731605947505292589 127644242524352230314484721)
          ·
            refine ⟨95733181893264172735863541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127644242524352230314484721 95733181893264172735863541)
            ·
              refine ⟨8974985802493516193987207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95733181893264172735863541 8974985802493516193987207)
              ·
                refine ⟨13462478703740274290980811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8974985802493516193987207 13462478703740274290980811)
                ·
                  refine ⟨20193718055610411436471217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13462478703740274290980811 20193718055610411436471217)
                  ·
                    refine ⟨15145288541707808577353413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20193718055610411436471217 15145288541707808577353413)
                    ·
                      refine ⟨2839741601570214108253765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15145288541707808577353413 2839741601570214108253765)
                      ·
                        rfl

theorem cell23_5530377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 4].length) (baseStart_5530377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530377 prefixEnd_5530377 := by exact prefixLift 5530377
  have htrace : WordTrace (prefixWord ++ tailWord_5530377) baseStart_5530377 baseEnd_5530377 := by
    simpa [prefixWord, tailWord_5530377, baseEnd_5530377] using wordTrace_append hprefix tailTrace_5530377
  have hstable : (prefixWord ++ tailWord_5530377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530377).length < 2 ^ (prefixWord ++ tailWord_5530377).sum := by decide
  have hdescent : baseEnd_5530377 < baseStart_5530377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530404 : List Nat := [2, 3, 1, 3, 4, 1, 9]
def baseStart_5530404 : Nat := 118140960795 + 5530404 * 2 ^ 59
def prefixEnd_5530404 : Nat := 4983230072969 + 3 ^ 40 * 5530404 * 2
def baseEnd_5530404 : Nat := 35058709451208462995261

theorem tailTrace_5530404 : CollatzResearch.WordTrace tailWord_5530404 prefixEnd_5530404 35058709451208462995261 := by
  unfold tailWord_5530404
  simp only [CollatzResearch.WordTrace]
  refine ⟨100855202528149150325703133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134473603370865533767604177 100855202528149150325703133)
  ·
    refine ⟨37820700948055931372138675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100855202528149150325703133 37820700948055931372138675)
    ·
      refine ⟨56731051422083897058208013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37820700948055931372138675 56731051422083897058208013)
      ·
        refine ⟨21274144283281461396828005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56731051422083897058208013 21274144283281461396828005)
        ·
          refine ⟨3988902053115274011905251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21274144283281461396828005 3988902053115274011905251)
          ·
            refine ⟨5983353079672911017857877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988902053115274011905251 5983353079672911017857877)
            ·
              refine ⟨35058709451208462995261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5983353079672911017857877 35058709451208462995261)
              ·
                rfl

theorem cell23_5530404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 9].length) (baseStart_5530404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530404 prefixEnd_5530404 := by exact prefixLift 5530404
  have htrace : WordTrace (prefixWord ++ tailWord_5530404) baseStart_5530404 baseEnd_5530404 := by
    simpa [prefixWord, tailWord_5530404, baseEnd_5530404] using wordTrace_append hprefix tailTrace_5530404
  have hstable : (prefixWord ++ tailWord_5530404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530404).length < 2 ^ (prefixWord ++ tailWord_5530404).sum := by decide
  have hdescent : baseEnd_5530404 < baseStart_5530404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530424 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 3, 3, 2]
def baseStart_5530424 : Nat := 118140960795 + 5530424 * 2 ^ 59
def prefixEnd_5530424 : Nat := 4983230072969 + 3 ^ 40 * 5530424 * 2
def baseEnd_5530424 : Nat := 2839765735160975424366049

theorem tailTrace_5530424 : CollatzResearch.WordTrace tailWord_5530424 prefixEnd_5530424 2839765735160975424366049 := by
  unfold tailWord_5530424
  simp only [CollatzResearch.WordTrace]
  refine ⟨100855567258112922033567163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134474089677483896044756217 100855567258112922033567163)
  ·
    refine ⟨151283350887169383050350745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100855567258112922033567163 151283350887169383050350745)
    ·
      refine ⟨113462513165377037287763059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151283350887169383050350745 113462513165377037287763059)
      ·
        refine ⟨170193769748065555931644589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113462513165377037287763059 170193769748065555931644589)
        ·
          refine ⟨63822663655524583474366721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170193769748065555931644589 63822663655524583474366721)
          ·
            refine ⟨47866997741643437605775041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63822663655524583474366721 47866997741643437605775041)
            ·
              refine ⟨35900248306232578204331281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47866997741643437605775041 35900248306232578204331281)
              ·
                refine ⟨26925186229674433653248461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35900248306232578204331281 26925186229674433653248461)
                ·
                  refine ⟨10096944836127912619968173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26925186229674433653248461 10096944836127912619968173)
                  ·
                    refine ⟨3786354313547967232488065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10096944836127912619968173 3786354313547967232488065)
                    ·
                      refine ⟨2839765735160975424366049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3786354313547967232488065 2839765735160975424366049)
                      ·
                        rfl

theorem cell23_5530424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 3, 2].length) (baseStart_5530424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530424 prefixEnd_5530424 := by exact prefixLift 5530424
  have htrace : WordTrace (prefixWord ++ tailWord_5530424) baseStart_5530424 baseEnd_5530424 := by
    simpa [prefixWord, tailWord_5530424, baseEnd_5530424] using wordTrace_append hprefix tailTrace_5530424
  have hstable : (prefixWord ++ tailWord_5530424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530424).length < 2 ^ (prefixWord ++ tailWord_5530424).sum := by decide
  have hdescent : baseEnd_5530424 < baseStart_5530424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530431 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 2, 1, 3]
def baseStart_5530431 : Nat := 118140960795 + 5530431 * 2 ^ 59
def prefixEnd_5530431 : Nat := 4983230072969 + 3 ^ 40 * 5530431 * 2
def baseEnd_5530431 : Nat := 2839769329525556896978517

theorem tailTrace_5530431 : CollatzResearch.WordTrace tailWord_5530431 prefixEnd_5530431 2839769329525556896978517 := by
  unfold tailWord_5530431
  simp only [CollatzResearch.WordTrace]
  refine ⟨201711389827200484262639147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134474259884800322841759431 201711389827200484262639147)
  ·
    refine ⟨302567084740800726393958721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201711389827200484262639147 302567084740800726393958721)
    ·
      refine ⟨226925313555600544795469041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302567084740800726393958721 226925313555600544795469041)
      ·
        refine ⟨170193985166700408596601781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226925313555600544795469041 170193985166700408596601781)
        ·
          refine ⟨15955686109378163305931417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170193985166700408596601781 15955686109378163305931417)
          ·
            refine ⟨11966764582033622479448563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15955686109378163305931417 11966764582033622479448563)
            ·
              refine ⟨17950146873050433719172845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11966764582033622479448563 17950146873050433719172845)
              ·
                refine ⟨6731305077393912644689817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17950146873050433719172845 6731305077393912644689817)
                ·
                  refine ⟨5048478808045434483517363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6731305077393912644689817 5048478808045434483517363)
                  ·
                    refine ⟨7572718212068151725276045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5048478808045434483517363 7572718212068151725276045)
                    ·
                      refine ⟨2839769329525556896978517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7572718212068151725276045 2839769329525556896978517)
                      ·
                        rfl

theorem cell23_5530431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_5530431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530431 prefixEnd_5530431 := by exact prefixLift 5530431
  have htrace : WordTrace (prefixWord ++ tailWord_5530431) baseStart_5530431 baseEnd_5530431 := by
    simpa [prefixWord, tailWord_5530431, baseEnd_5530431] using wordTrace_append hprefix tailTrace_5530431
  have hstable : (prefixWord ++ tailWord_5530431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530431).length < 2 ^ (prefixWord ++ tailWord_5530431).sum := by decide
  have hdescent : baseEnd_5530431 < baseStart_5530431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530441 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 1, 3, 2]
def baseStart_5530441 : Nat := 118140960795 + 5530441 * 2 ^ 59
def prefixEnd_5530441 : Nat := 4983230072969 + 3 ^ 40 * 5530441 * 2
def baseEnd_5530441 : Nat := 2839774464332101857853471

theorem tailTrace_5530441 : CollatzResearch.WordTrace tailWord_5530441 prefixEnd_5530441 2839774464332101857853471 := by
  unfold tailWord_5530441
  simp only [CollatzResearch.WordTrace]
  refine ⟨201711754557164255970503177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134474503038109503980335451 201711754557164255970503177)
  ·
    refine ⟨151283815917873191977877383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201711754557164255970503177 151283815917873191977877383)
    ·
      refine ⟨226925723876809787966816075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151283815917873191977877383 226925723876809787966816075)
      ·
        refine ⟨340388585815214681950224113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226925723876809787966816075 340388585815214681950224113)
        ·
          refine ⟨255291439361411011462668085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340388585815214681950224113 255291439361411011462668085)
          ·
            refine ⟨23933572440132282324625133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 255291439361411011462668085 23933572440132282324625133)
            ·
              refine ⟨8975089665049605871734425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23933572440132282324625133 8975089665049605871734425)
              ·
                refine ⟨6731317248787204403800819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8975089665049605871734425 6731317248787204403800819)
                ·
                  refine ⟨10096975873180806605701229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6731317248787204403800819 10096975873180806605701229)
                  ·
                    refine ⟨3786365952442802477137961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10096975873180806605701229 3786365952442802477137961)
                    ·
                      refine ⟨2839774464332101857853471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3786365952442802477137961 2839774464332101857853471)
                      ·
                        rfl

theorem cell23_5530441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 3, 2].length) (baseStart_5530441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530441 prefixEnd_5530441 := by exact prefixLift 5530441
  have htrace : WordTrace (prefixWord ++ tailWord_5530441) baseStart_5530441 baseEnd_5530441 := by
    simpa [prefixWord, tailWord_5530441, baseEnd_5530441] using wordTrace_append hprefix tailTrace_5530441
  have hstable : (prefixWord ++ tailWord_5530441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530441).length < 2 ^ (prefixWord ++ tailWord_5530441).sum := by decide
  have hdescent : baseEnd_5530441 < baseStart_5530441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530457 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 5]
def baseStart_5530457 : Nat := 118140960795 + 5530457 * 2 ^ 59
def prefixEnd_5530457 : Nat := 4983230072969 + 3 ^ 40 * 5530457 * 2
def baseEnd_5530457 : Nat := 2839782680022573795253397

theorem tailTrace_5530457 : CollatzResearch.WordTrace tailWord_5530457 prefixEnd_5530457 2839782680022573795253397 := by
  unfold tailWord_5530457
  simp only [CollatzResearch.WordTrace]
  refine ⟨201712338125106290703085625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134474892083404193802057083 201712338125106290703085625)
  ·
    refine ⟨151284253593829718027314219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201712338125106290703085625 151284253593829718027314219)
    ·
      refine ⟨226926380390744577040971329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151284253593829718027314219 226926380390744577040971329)
      ·
        refine ⟨170194785293058432780728497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226926380390744577040971329 170194785293058432780728497)
        ·
          refine ⟨127646088969793824585546373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170194785293058432780728497 127646088969793824585546373)
          ·
            refine ⟨23933641681836342109789945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127646088969793824585546373 23933641681836342109789945)
            ·
              refine ⟨17950231261377256582342459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23933641681836342109789945 17950231261377256582342459)
              ·
                refine ⟨26925346892065884873513689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17950231261377256582342459 26925346892065884873513689)
                ·
                  refine ⟨20194010169049413655135267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26925346892065884873513689 20194010169049413655135267)
                  ·
                    refine ⟨30291015253574120482702901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20194010169049413655135267 30291015253574120482702901)
                    ·
                      refine ⟨2839782680022573795253397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30291015253574120482702901 2839782680022573795253397)
                      ·
                        rfl

theorem cell23_5530457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_5530457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530457 prefixEnd_5530457 := by exact prefixLift 5530457
  have htrace : WordTrace (prefixWord ++ tailWord_5530457) baseStart_5530457 baseEnd_5530457 := by
    simpa [prefixWord, tailWord_5530457, baseEnd_5530457] using wordTrace_append hprefix tailTrace_5530457
  have hstable : (prefixWord ++ tailWord_5530457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530457).length < 2 ^ (prefixWord ++ tailWord_5530457).sum := by decide
  have hdescent : baseEnd_5530457 < baseStart_5530457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530458 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2]
def baseStart_5530458 : Nat := 118140960795 + 5530458 * 2 ^ 59
def prefixEnd_5530458 : Nat := 4983230072969 + 3 ^ 40 * 5530458 * 2
def baseEnd_5530458 : Nat := 2839783193503228291340893

theorem tailTrace_5530458 : CollatzResearch.WordTrace tailWord_5530458 prefixEnd_5530458 2839783193503228291340893 := by
  unfold tailWord_5530458
  simp only [CollatzResearch.WordTrace]
  refine ⟨50428093649525666968468007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134474916398735111915914685 50428093649525666968468007)
  ·
    refine ⟨75642140474288500452702011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50428093649525666968468007 75642140474288500452702011)
    ·
      refine ⟨113463210711432750679053017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75642140474288500452702011 113463210711432750679053017)
      ·
        refine ⟨85097408033574563009289763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113463210711432750679053017 85097408033574563009289763)
        ·
          refine ⟨127646112050361844513934645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85097408033574563009289763 127646112050361844513934645)
          ·
            refine ⟨11966823004721422923181373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127646112050361844513934645 11966823004721422923181373)
            ·
              refine ⟨4487558626770533596193015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11966823004721422923181373 4487558626770533596193015)
              ·
                refine ⟨6731337940155800394289523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4487558626770533596193015 6731337940155800394289523)
                ·
                  refine ⟨10097006910233700591434285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6731337940155800394289523 10097006910233700591434285)
                  ·
                    refine ⟨3786377591337637721787857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10097006910233700591434285 3786377591337637721787857)
                    ·
                      refine ⟨2839783193503228291340893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3786377591337637721787857 2839783193503228291340893)
                      ·
                        rfl

theorem cell23_5530458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_5530458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530458 prefixEnd_5530458 := by exact prefixLift 5530458
  have htrace : WordTrace (prefixWord ++ tailWord_5530458) baseStart_5530458 baseEnd_5530458 := by
    simpa [prefixWord, tailWord_5530458, baseEnd_5530458] using wordTrace_append hprefix tailTrace_5530458
  have hstable : (prefixWord ++ tailWord_5530458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530458).length < 2 ^ (prefixWord ++ tailWord_5530458).sum := by decide
  have hdescent : baseEnd_5530458 < baseStart_5530458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530477 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 7]
def baseStart_5530477 : Nat := 118140960795 + 5530477 * 2 ^ 59
def prefixEnd_5530477 : Nat := 4983230072969 + 3 ^ 40 * 5530477 * 2
def baseEnd_5530477 : Nat := 315532549959518190778145

theorem tailTrace_5530477 : CollatzResearch.WordTrace tailWord_5530477 prefixEnd_5530477 315532549959518190778145 := by
  unfold tailWord_5530477
  simp only [CollatzResearch.WordTrace]
  refine ⟨201713067585033834118813685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134475378390022556079209123 201713067585033834118813685)
  ·
    refine ⟨18910600086096921948638783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201713067585033834118813685 18910600086096921948638783)
    ·
      refine ⟨28365900129145382922958175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18910600086096921948638783 28365900129145382922958175)
      ·
        refine ⟨42548850193718074384437263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28365900129145382922958175 42548850193718074384437263)
        ·
          refine ⟨63823275290577111576655895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42548850193718074384437263 63823275290577111576655895)
          ·
            refine ⟨95734912935865667364983843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63823275290577111576655895 95734912935865667364983843)
            ·
              refine ⟨143602369403798501047475765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95734912935865667364983843 143602369403798501047475765)
              ·
                refine ⟨13462722131606109473200853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143602369403798501047475765 13462722131606109473200853)
                ·
                  refine ⟨315532549959518190778145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13462722131606109473200853 315532549959518190778145)
                  ·
                    rfl

theorem cell23_5530477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_5530477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530477 prefixEnd_5530477 := by exact prefixLift 5530477
  have htrace : WordTrace (prefixWord ++ tailWord_5530477) baseStart_5530477 baseEnd_5530477 := by
    simpa [prefixWord, tailWord_5530477, baseEnd_5530477] using wordTrace_append hprefix tailTrace_5530477
  have hstable : (prefixWord ++ tailWord_5530477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530477).length < 2 ^ (prefixWord ++ tailWord_5530477).sum := by decide
  have hdescent : baseEnd_5530477 < baseStart_5530477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530518 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5530518 : Nat := 118140960795 + 5530518 * 2 ^ 59
def prefixEnd_5530518 : Nat := 4983230072969 + 3 ^ 40 * 5530518 * 2
def baseEnd_5530518 : Nat := 2839814002342498056590617

theorem tailTrace_5530518 : CollatzResearch.WordTrace tailWord_5530518 prefixEnd_5530518 2839814002342498056590617 := by
  unfold tailWord_5530518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12607160186117831132566013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134476375318590198747370805 12607160186117831132566013)
  ·
    refine ⟨4727685069794186674712255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12607160186117831132566013 4727685069794186674712255)
    ·
      refine ⟨7091527604691280012068383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4727685069794186674712255 7091527604691280012068383)
      ·
        refine ⟨10637291407036920018102575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7091527604691280012068383 10637291407036920018102575)
        ·
          refine ⟨15955937110555380027153863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10637291407036920018102575 15955937110555380027153863)
          ·
            refine ⟨23933905665833070040730795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15955937110555380027153863 23933905665833070040730795)
            ·
              refine ⟨35900858498749605061096193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23933905665833070040730795 35900858498749605061096193)
              ·
                refine ⟨26925643874062203795822145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35900858498749605061096193 26925643874062203795822145)
                ·
                  refine ⟨20194232905546652846866609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26925643874062203795822145 20194232905546652846866609)
                  ·
                    refine ⟨15145674679159989635149957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20194232905546652846866609 15145674679159989635149957)
                    ·
                      refine ⟨2839814002342498056590617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15145674679159989635149957 2839814002342498056590617)
                      ·
                        rfl

theorem cell23_5530518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5530518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530518 prefixEnd_5530518 := by exact prefixLift 5530518
  have htrace : WordTrace (prefixWord ++ tailWord_5530518) baseStart_5530518 baseEnd_5530518 := by
    simpa [prefixWord, tailWord_5530518, baseEnd_5530518] using wordTrace_append hprefix tailTrace_5530518
  have hstable : (prefixWord ++ tailWord_5530518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530518).length < 2 ^ (prefixWord ++ tailWord_5530518).sum := by decide
  have hdescent : baseEnd_5530518 < baseStart_5530518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530522 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2]
def baseStart_5530522 : Nat := 118140960795 + 5530522 * 2 ^ 59
def prefixEnd_5530522 : Nat := 4983230072969 + 3 ^ 40 * 5530522 * 2
def baseEnd_5530522 : Nat := 2839816056265116040940599

theorem tailTrace_5530522 : CollatzResearch.WordTrace tailWord_5530522 prefixEnd_5530522 2839816056265116040940599 := by
  unfold tailWord_5530522
  simp only [CollatzResearch.WordTrace]
  refine ⟨50428677217467701701050455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134476472579913871202801213 50428677217467701701050455)
  ·
    refine ⟨75643015826201552551575683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50428677217467701701050455 75643015826201552551575683)
    ·
      refine ⟨113464523739302328827363525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75643015826201552551575683 113464523739302328827363525)
      ·
        refine ⟨21274598201119186655130661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113464523739302328827363525 21274598201119186655130661)
        ·
          refine ⟨3988987162709847497836999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21274598201119186655130661 3988987162709847497836999)
          ·
            refine ⟨5983480744064771246755499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988987162709847497836999 5983480744064771246755499)
            ·
              refine ⟨8975221116097156870133249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5983480744064771246755499 8975221116097156870133249)
              ·
                refine ⟨6731415837072867652599937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8975221116097156870133249 6731415837072867652599937)
                ·
                  refine ⟨5048561877804650739449953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6731415837072867652599937 5048561877804650739449953)
                  ·
                    refine ⟨3786421408353488054587465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5048561877804650739449953 3786421408353488054587465)
                    ·
                      refine ⟨2839816056265116040940599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3786421408353488054587465 2839816056265116040940599)
                      ·
                        rfl

theorem cell23_5530522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_5530522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530522 prefixEnd_5530522 := by exact prefixLift 5530522
  have htrace : WordTrace (prefixWord ++ tailWord_5530522) baseStart_5530522 baseEnd_5530522 := by
    simpa [prefixWord, tailWord_5530522, baseEnd_5530522] using wordTrace_append hprefix tailTrace_5530522
  have hstable : (prefixWord ++ tailWord_5530522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530522).length < 2 ^ (prefixWord ++ tailWord_5530522).sum := by decide
  have hdescent : baseEnd_5530522 < baseStart_5530522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530554 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 3, 4]
def baseStart_5530554 : Nat := 118140960795 + 5530554 * 2 ^ 59
def prefixEnd_5530554 : Nat := 4983230072969 + 3 ^ 40 * 5530554 * 2
def baseEnd_5530554 : Nat := 946610829215353305246817

theorem tailTrace_5530554 : CollatzResearch.WordTrace tailWord_5530554 prefixEnd_5530554 946610829215353305246817 := by
  unfold tailWord_5530554
  simp only [CollatzResearch.WordTrace]
  refine ⟨50428969001438719067341679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134477250670503250846244477 50428969001438719067341679)
  ·
    refine ⟨75643453502158078601012519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50428969001438719067341679 75643453502158078601012519)
    ·
      refine ⟨113465180253237117901518779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75643453502158078601012519 113465180253237117901518779)
      ·
        refine ⟨170197770379855676852278169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113465180253237117901518779 170197770379855676852278169)
        ·
          refine ⟨127648327784891757639208627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170197770379855676852278169 127648327784891757639208627)
          ·
            refine ⟨191472491677337636458812941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127648327784891757639208627 191472491677337636458812941)
            ·
              refine ⟨71802184379001613672054853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191472491677337636458812941 71802184379001613672054853)
              ·
                refine ⟨13462909571062802563510285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71802184379001613672054853 13462909571062802563510285)
                ·
                  refine ⟨5048591089148550961316357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13462909571062802563510285 5048591089148550961316357)
                  ·
                    refine ⟨946610829215353305246817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5048591089148550961316357 946610829215353305246817)
                    ·
                      rfl

theorem cell23_5530554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_5530554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530554 prefixEnd_5530554 := by exact prefixLift 5530554
  have htrace : WordTrace (prefixWord ++ tailWord_5530554) baseStart_5530554 baseEnd_5530554 := by
    simpa [prefixWord, tailWord_5530554, baseEnd_5530554] using wordTrace_append hprefix tailTrace_5530554
  have hstable : (prefixWord ++ tailWord_5530554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530554).length < 2 ^ (prefixWord ++ tailWord_5530554).sum := by decide
  have hdescent : baseEnd_5530554 < baseStart_5530554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530567 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 8]
def baseStart_5530567 : Nat := 118140960795 + 5530567 * 2 ^ 59
def prefixEnd_5530567 : Nat := 4983230072969 + 3 ^ 40 * 5530567 * 2
def baseEnd_5530567 : Nat := 315537684766063151653099

theorem tailTrace_5530567 : CollatzResearch.WordTrace tailWord_5530567 prefixEnd_5530567 315537684766063151653099 := by
  unfold tailWord_5530567
  simp only [CollatzResearch.WordTrace]
  refine ⟨201716350154707779489589955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134477566769805186326393303 201716350154707779489589955)
  ·
    refine ⟨302574525232061669234384933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201716350154707779489589955 302574525232061669234384933)
    ·
      refine ⟨56732723481011562981447175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302574525232061669234384933 56732723481011562981447175)
      ·
        refine ⟨85099085221517344472170763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56732723481011562981447175 85099085221517344472170763)
        ·
          refine ⟨127648627832276016708256145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85099085221517344472170763 127648627832276016708256145)
          ·
            refine ⟨95736470874207012531192109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127648627832276016708256145 95736470874207012531192109)
            ·
              refine ⟨35901176577827629699197041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95736470874207012531192109 35901176577827629699197041)
              ·
                refine ⟨26925882433370722274397781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35901176577827629699197041 26925882433370722274397781)
                ·
                  refine ⟨315537684766063151653099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26925882433370722274397781 315537684766063151653099)
                  ·
                    rfl

theorem cell23_5530567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 8].length) (baseStart_5530567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530567 prefixEnd_5530567 := by exact prefixLift 5530567
  have htrace : WordTrace (prefixWord ++ tailWord_5530567) baseStart_5530567 baseEnd_5530567 := by
    simpa [prefixWord, tailWord_5530567, baseEnd_5530567] using wordTrace_append hprefix tailTrace_5530567
  have hstable : (prefixWord ++ tailWord_5530567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530567).length < 2 ^ (prefixWord ++ tailWord_5530567).sum := by decide
  have hdescent : baseEnd_5530567 < baseStart_5530567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530638 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2]
def baseStart_5530638 : Nat := 118140960795 + 5530638 * 2 ^ 59
def prefixEnd_5530638 : Nat := 4983230072969 + 3 ^ 40 * 5530638 * 2
def baseEnd_5530638 : Nat := 2839875620021037587090065

theorem tailTrace_5530638 : CollatzResearch.WordTrace tailWord_5530638 prefixEnd_5530638 2839875620021037587090065 := by
  unfold tailWord_5530638
  simp only [CollatzResearch.WordTrace]
  refine ⟨25214867467181319826928071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134479293158300372410283045 25214867467181319826928071)
  ·
    refine ⟨37822301200771979740392107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25214867467181319826928071 37822301200771979740392107)
    ·
      refine ⟨56733451801157969610588161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37822301200771979740392107 56733451801157969610588161)
      ·
        refine ⟨42550088850868477207941121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56733451801157969610588161 42550088850868477207941121)
        ·
          refine ⟨31912566638151357905955841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42550088850868477207941121 31912566638151357905955841)
          ·
            refine ⟨23934424978613518429466881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31912566638151357905955841 23934424978613518429466881)
            ·
              refine ⟨17950818733960138822100161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23934424978613518429466881 17950818733960138822100161)
              ·
                refine ⟨13463114050470104116575121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17950818733960138822100161 13463114050470104116575121)
                ·
                  refine ⟨10097335537852578087431341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13463114050470104116575121 10097335537852578087431341)
                  ·
                    refine ⟨3786500826694716782786753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10097335537852578087431341 3786500826694716782786753)
                    ·
                      refine ⟨2839875620021037587090065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3786500826694716782786753 2839875620021037587090065)
                      ·
                        rfl

theorem cell23_5530638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_5530638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530638 prefixEnd_5530638 := by exact prefixLift 5530638
  have htrace : WordTrace (prefixWord ++ tailWord_5530638) baseStart_5530638 baseEnd_5530638 := by
    simpa [prefixWord, tailWord_5530638, baseEnd_5530638] using wordTrace_append hprefix tailTrace_5530638
  have hstable : (prefixWord ++ tailWord_5530638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530638).length < 2 ^ (prefixWord ++ tailWord_5530638).sum := by decide
  have hdescent : baseEnd_5530638 < baseStart_5530638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530645 : List Nat := [1, 3, 2, 1, 4, 2, 1, 4, 1, 1, 3]
def baseStart_5530645 : Nat := 118140960795 + 5530645 * 2 ^ 59
def prefixEnd_5530645 : Nat := 4983230072969 + 3 ^ 40 * 5530645 * 2
def baseEnd_5530645 : Nat := 2839879214385619059702533

theorem tailTrace_5530645 : CollatzResearch.WordTrace tailWord_5530645 prefixEnd_5530645 2839879214385619059702533 := by
  unfold tailWord_5530645
  simp only [CollatzResearch.WordTrace]
  refine ⟨201719195048425198810929389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134479463365616799207286259 201719195048425198810929389)
  ·
    refine ⟨75644698143159449554098521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201719195048425198810929389 75644698143159449554098521)
    ·
      refine ⟨56733523607369587165573891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75644698143159449554098521 56733523607369587165573891)
      ·
        refine ⟨85100285411054380748360837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56733523607369587165573891 85100285411054380748360837)
        ·
          refine ⟨15956303514572696390317657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85100285411054380748360837 15956303514572696390317657)
          ·
            refine ⟨11967227635929522292738243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15956303514572696390317657 11967227635929522292738243)
            ·
              refine ⟨17950841453894283439107365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11967227635929522292738243 17950841453894283439107365)
              ·
                refine ⟨3365782772605178144832631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17950841453894283439107365 3365782772605178144832631)
                ·
                  refine ⟨5048674158907767217248947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3365782772605178144832631 5048674158907767217248947)
                  ·
                    refine ⟨7573011238361650825873421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5048674158907767217248947 7573011238361650825873421)
                    ·
                      refine ⟨2839879214385619059702533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7573011238361650825873421 2839879214385619059702533)
                      ·
                        rfl

theorem cell23_5530645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_5530645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530645 prefixEnd_5530645 := by exact prefixLift 5530645
  have htrace : WordTrace (prefixWord ++ tailWord_5530645) baseStart_5530645 baseEnd_5530645 := by
    simpa [prefixWord, tailWord_5530645, baseEnd_5530645] using wordTrace_append hprefix tailTrace_5530645
  have hstable : (prefixWord ++ tailWord_5530645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530645).length < 2 ^ (prefixWord ++ tailWord_5530645).sum := by decide
  have hdescent : baseEnd_5530645 < baseStart_5530645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530661 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 2, 4]
def baseStart_5530661 : Nat := 118140960795 + 5530661 * 2 ^ 59
def prefixEnd_5530661 : Nat := 4983230072969 + 3 ^ 40 * 5530661 * 2
def baseEnd_5530661 : Nat := 946629143358696999034153

theorem tailTrace_5530661 : CollatzResearch.WordTrace tailWord_5530661 prefixEnd_5530661 946629143358696999034153 := by
  unfold tailWord_5530661
  simp only [CollatzResearch.WordTrace]
  refine ⟨201719778616367233543511837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134479852410911489029007891 201719778616367233543511837)
  ·
    refine ⟨75644916981137712578816939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201719778616367233543511837 75644916981137712578816939)
    ·
      refine ⟨113467375471706568868225409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75644916981137712578816939 113467375471706568868225409)
      ·
        refine ⟨85100531603779926651169057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113467375471706568868225409 85100531603779926651169057)
        ·
          refine ⟨63825398702834944988376793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85100531603779926651169057 63825398702834944988376793)
          ·
            refine ⟨47869049027126208741282595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63825398702834944988376793 47869049027126208741282595)
            ·
              refine ⟨71803573540689313111923893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47869049027126208741282595 71803573540689313111923893)
              ·
                refine ⟨6731585019439623104242865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71803573540689313111923893 6731585019439623104242865)
                ·
                  refine ⟨5048688764579717328182149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6731585019439623104242865 5048688764579717328182149)
                  ·
                    refine ⟨946629143358696999034153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5048688764579717328182149 946629143358696999034153)
                    ·
                      rfl

theorem cell23_5530661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_5530661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530661 prefixEnd_5530661 := by exact prefixLift 5530661
  have htrace : WordTrace (prefixWord ++ tailWord_5530661) baseStart_5530661 baseEnd_5530661 := by
    simpa [prefixWord, tailWord_5530661, baseEnd_5530661] using wordTrace_append hprefix tailTrace_5530661
  have hstable : (prefixWord ++ tailWord_5530661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530661).length < 2 ^ (prefixWord ++ tailWord_5530661).sum := by decide
  have hdescent : baseEnd_5530661 < baseStart_5530661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530668 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 3, 2, 2]
def baseStart_5530668 : Nat := 118140960795 + 5530668 * 2 ^ 59
def prefixEnd_5530668 : Nat := 4983230072969 + 3 ^ 40 * 5530668 * 2
def baseEnd_5530668 : Nat := 2839891024440672469714927

theorem tailTrace_5530668 : CollatzResearch.WordTrace tailWord_5530668 prefixEnd_5530668 2839891024440672469714927 := by
  unfold tailWord_5530668
  simp only [CollatzResearch.WordTrace]
  refine ⟨100860016963670936869508329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134480022618227915826011105 100860016963670936869508329)
  ·
    refine ⟨75645012722753202652131247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100860016963670936869508329 75645012722753202652131247)
    ·
      refine ⟨113467519084129803978196871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75645012722753202652131247 113467519084129803978196871)
      ·
        refine ⟨170201278626194705967295307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113467519084129803978196871 170201278626194705967295307)
        ·
          refine ⟨255301917939292058950942961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170201278626194705967295307 255301917939292058950942961)
          ·
            refine ⟨191476438454469044213207221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255301917939292058950942961 191476438454469044213207221)
            ·
              refine ⟨17950916105106472894988177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191476438454469044213207221 17950916105106472894988177)
              ·
                refine ⟨13463187078829854671241133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17950916105106472894988177 13463187078829854671241133)
                ·
                  refine ⟨5048695154561195501715425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13463187078829854671241133 5048695154561195501715425)
                  ·
                    refine ⟨3786521365920896626286569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5048695154561195501715425 3786521365920896626286569)
                    ·
                      refine ⟨2839891024440672469714927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3786521365920896626286569 2839891024440672469714927)
                      ·
                        rfl

theorem cell23_5530668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 2, 2].length) (baseStart_5530668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530668 prefixEnd_5530668 := by exact prefixLift 5530668
  have htrace : WordTrace (prefixWord ++ tailWord_5530668) baseStart_5530668 baseEnd_5530668 := by
    simpa [prefixWord, tailWord_5530668, baseEnd_5530668] using wordTrace_append hprefix tailTrace_5530668
  have hstable : (prefixWord ++ tailWord_5530668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530668).length < 2 ^ (prefixWord ++ tailWord_5530668).sum := by decide
  have hdescent : baseEnd_5530668 < baseStart_5530668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530681 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 4]
def baseStart_5530681 : Nat := 118140960795 + 5530681 * 2 ^ 59
def prefixEnd_5530681 : Nat := 4983230072969 + 3 ^ 40 * 5530681 * 2
def baseEnd_5530681 : Nat := 2839897699689180918852367

theorem tailTrace_5530681 : CollatzResearch.WordTrace tailWord_5530681 prefixEnd_5530681 2839897699689180918852367 := by
  unfold tailWord_5530681
  simp only [CollatzResearch.WordTrace]
  refine ⟨201720508076294776959239897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134480338717529851306159931 201720508076294776959239897)
  ·
    refine ⟨151290381057221082719429923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201720508076294776959239897 151290381057221082719429923)
    ·
      refine ⟨226935571585831624079144885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151290381057221082719429923 226935571585831624079144885)
      ·
        refine ⟨21275209836171714757419833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226935571585831624079144885 21275209836171714757419833)
        ·
          refine ⟨15956407377128786068064875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21275209836171714757419833 15956407377128786068064875)
          ·
            refine ⟨23934611065693179102097313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15956407377128786068064875 23934611065693179102097313)
            ·
              refine ⟨17950958299269884326572985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23934611065693179102097313 17950958299269884326572985)
              ·
                refine ⟨13463218724452413244929739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17950958299269884326572985 13463218724452413244929739)
                ·
                  refine ⟨20194828086678619867394609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13463218724452413244929739 20194828086678619867394609)
                  ·
                    refine ⟨15146121065008964900545957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20194828086678619867394609 15146121065008964900545957)
                    ·
                      refine ⟨2839897699689180918852367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15146121065008964900545957 2839897699689180918852367)
                      ·
                        rfl

theorem cell23_5530681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_5530681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530681 prefixEnd_5530681 := by exact prefixLift 5530681
  have htrace : WordTrace (prefixWord ++ tailWord_5530681) baseStart_5530681 baseEnd_5530681 := by
    simpa [prefixWord, tailWord_5530681, baseEnd_5530681] using wordTrace_append hprefix tailTrace_5530681
  have hstable : (prefixWord ++ tailWord_5530681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530681).length < 2 ^ (prefixWord ++ tailWord_5530681).sum := by decide
  have hdescent : baseEnd_5530681 < baseStart_5530681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530685 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 1, 1, 4]
def baseStart_5530685 : Nat := 118140960795 + 5530685 * 2 ^ 59
def prefixEnd_5530685 : Nat := 4983230072969 + 3 ^ 40 * 5530685 * 2
def baseEnd_5530685 : Nat := 2839899753611798903202349

theorem tailTrace_5530685 : CollatzResearch.WordTrace tailWord_5530685 prefixEnd_5530685 2839899753611798903202349 := by
  unfold tailWord_5530685
  simp only [CollatzResearch.WordTrace]
  refine ⟨201720653968280285642385509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134480435978853523761590339 201720653968280285642385509)
  ·
    refine ⟨37822622619052553557947283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201720653968280285642385509 37822622619052553557947283)
    ·
      refine ⟨56733933928578830336920925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37822622619052553557947283 56733933928578830336920925)
      ·
        refine ⟨21275225223217061376345347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56733933928578830336920925 21275225223217061376345347)
        ·
          refine ⟨31912837834825592064518021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21275225223217061376345347 31912837834825592064518021)
          ·
            refine ⟨5983657094029798512097129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31912837834825592064518021 5983657094029798512097129)
            ·
              refine ⟨4487742820522348884072847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5983657094029798512097129 4487742820522348884072847)
              ·
                refine ⟨6731614230783523326109271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4487742820522348884072847 6731614230783523326109271)
                ·
                  refine ⟨10097421346175284989163907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6731614230783523326109271 10097421346175284989163907)
                  ·
                    refine ⟨15146132019262927483745861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10097421346175284989163907 15146132019262927483745861)
                    ·
                      refine ⟨2839899753611798903202349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15146132019262927483745861 2839899753611798903202349)
                      ·
                        rfl

theorem cell23_5530685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_5530685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530685 prefixEnd_5530685 := by exact prefixLift 5530685
  have htrace : WordTrace (prefixWord ++ tailWord_5530685) baseStart_5530685 baseEnd_5530685 := by
    simpa [prefixWord, tailWord_5530685, baseEnd_5530685] using wordTrace_append hprefix tailTrace_5530685
  have hstable : (prefixWord ++ tailWord_5530685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530685).length < 2 ^ (prefixWord ++ tailWord_5530685).sum := by decide
  have hdescent : baseEnd_5530685 < baseStart_5530685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530744 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_5530744 : Nat := 118140960795 + 5530744 * 2 ^ 59
def prefixEnd_5530744 : Nat := 4983230072969 + 3 ^ 40 * 5530744 * 2
def baseEnd_5530744 : Nat := 2839930048970414172364577

theorem tailTrace_5530744 : CollatzResearch.WordTrace tailWord_5530744 prefixEnd_5530744 2839930048970414172364577 := by
  unfold tailWord_5530744
  simp only [CollatzResearch.WordTrace]
  refine ⟨100861402937533269359391643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134481870583377692479188857 100861402937533269359391643)
  ·
    refine ⟨151292104406299904039087465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100861402937533269359391643 151292104406299904039087465)
    ·
      refine ⟨113469078304724928029315599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151292104406299904039087465 113469078304724928029315599)
      ·
        refine ⟨170203617457087392043973399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113469078304724928029315599 170203617457087392043973399)
        ·
          refine ⟨255305426185631088065960099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170203617457087392043973399 255305426185631088065960099)
          ·
            refine ⟨382958139278446632098940149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255305426185631088065960099 382958139278446632098940149)
            ·
              refine ⟨35902325557354371759275639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 382958139278446632098940149 35902325557354371759275639)
              ·
                refine ⟨53853488336031557638913459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35902325557354371759275639 53853488336031557638913459)
                ·
                  refine ⟨80780232504047336458370189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53853488336031557638913459 80780232504047336458370189)
                  ·
                    refine ⟨30292587189017751171888821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80780232504047336458370189 30292587189017751171888821)
                    ·
                      refine ⟨2839930048970414172364577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30292587189017751171888821 2839930048970414172364577)
                      ·
                        rfl

theorem cell23_5530744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_5530744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530744 prefixEnd_5530744 := by exact prefixLift 5530744
  have htrace : WordTrace (prefixWord ++ tailWord_5530744) baseStart_5530744 baseEnd_5530744 := by
    simpa [prefixWord, tailWord_5530744, baseEnd_5530744] using wordTrace_append hprefix tailTrace_5530744
  have hstable : (prefixWord ++ tailWord_5530744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530744).length < 2 ^ (prefixWord ++ tailWord_5530744).sum := by decide
  have hdescent : baseEnd_5530744 < baseStart_5530744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530848 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 4]
def baseStart_5530848 : Nat := 118140960795 + 5530848 * 2 ^ 59
def prefixEnd_5530848 : Nat := 4983230072969 + 3 ^ 40 * 5530848 * 2
def baseEnd_5530848 : Nat := 2839983450958481765464099

theorem tailTrace_5530848 : CollatzResearch.WordTrace tailWord_5530848 prefixEnd_5530848 2839983450958481765464099 := by
  unfold tailWord_5530848
  simp only [CollatzResearch.WordTrace]
  refine ⟨100863299533344882240284599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134484399377793176320379465 100863299533344882240284599)
  ·
    refine ⟨151294949300017323360426899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100863299533344882240284599 151294949300017323360426899)
    ·
      refine ⟨226942423950025985040640349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151294949300017323360426899 226942423950025985040640349)
      ·
        refine ⟨85103408981259744390240131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226942423950025985040640349 85103408981259744390240131)
        ·
          refine ⟨127655113471889616585360197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85103408981259744390240131 127655113471889616585360197)
          ·
            refine ⟨23935333775979303109755037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127655113471889616585360197 23935333775979303109755037)
            ·
              refine ⟨8975750165992238666158139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23935333775979303109755037 8975750165992238666158139)
              ·
                refine ⟨13463625248988357999237209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8975750165992238666158139 13463625248988357999237209)
                ·
                  refine ⟨10097718936741268499427907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13463625248988357999237209 10097718936741268499427907)
                  ·
                    refine ⟨15146578405111902749141861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10097718936741268499427907 15146578405111902749141861)
                    ·
                      refine ⟨2839983450958481765464099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15146578405111902749141861 2839983450958481765464099)
                      ·
                        rfl

theorem cell23_5530848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_5530848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530848 prefixEnd_5530848 := by exact prefixLift 5530848
  have htrace : WordTrace (prefixWord ++ tailWord_5530848) baseStart_5530848 baseEnd_5530848 := by
    simpa [prefixWord, tailWord_5530848, baseEnd_5530848] using wordTrace_append hprefix tailTrace_5530848
  have hstable : (prefixWord ++ tailWord_5530848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530848).length < 2 ^ (prefixWord ++ tailWord_5530848).sum := by decide
  have hdescent : baseEnd_5530848 < baseStart_5530848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530909 : List Nat := [1, 4, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_5530909 : Nat := 118140960795 + 5530909 * 2 ^ 59
def prefixEnd_5530909 : Nat := 4983230072969 + 3 ^ 40 * 5530909 * 2
def baseEnd_5530909 : Nat := 946671591092802008933773

theorem tailTrace_5530909 : CollatzResearch.WordTrace tailWord_5530909 prefixEnd_5530909 946671591092802008933773 := by
  unfold tailWord_5530909
  simp only [CollatzResearch.WordTrace]
  refine ⟨201728823919468771898539781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134485882612979181265693187 201728823919468771898539781)
  ·
    refine ⟨37824154484900394730976209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201728823919468771898539781 37824154484900394730976209)
    ·
      refine ⟨28368115863675296048232157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37824154484900394730976209 28368115863675296048232157)
      ·
        refine ⟨10638043448878236018087059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28368115863675296048232157 10638043448878236018087059)
        ·
          refine ⟨15957065173317354027130589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10638043448878236018087059 15957065173317354027130589)
          ·
            refine ⟨5983899439994007760173971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15957065173317354027130589 5983899439994007760173971)
            ·
              refine ⟨8975849159991011640260957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5983899439994007760173971 8975849159991011640260957)
              ·
                refine ⟨3365943434996629365097859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8975849159991011640260957 3365943434996629365097859)
                ·
                  refine ⟨5048915152494944047646789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3365943434996629365097859 5048915152494944047646789)
                  ·
                    refine ⟨946671591092802008933773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5048915152494944047646789 946671591092802008933773)
                    ·
                      rfl

theorem cell23_5530909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_5530909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530909 prefixEnd_5530909 := by exact prefixLift 5530909
  have htrace : WordTrace (prefixWord ++ tailWord_5530909) baseStart_5530909 baseEnd_5530909 := by
    simpa [prefixWord, tailWord_5530909, baseEnd_5530909] using wordTrace_append hprefix tailTrace_5530909
  have hstable : (prefixWord ++ tailWord_5530909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530909).length < 2 ^ (prefixWord ++ tailWord_5530909).sum := by decide
  have hdescent : baseEnd_5530909 < baseStart_5530909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530938 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_5530938 : Nat := 118140960795 + 5530938 * 2 ^ 59
def prefixEnd_5530938 : Nat := 4983230072969 + 3 ^ 40 * 5530938 * 2
def baseEnd_5530938 : Nat := 2840029664217386413338685

theorem tailTrace_5530938 : CollatzResearch.WordTrace tailWord_5530938 prefixEnd_5530938 2840029664217386413338685 := by
  unfold tailWord_5530938
  simp only [CollatzResearch.WordTrace]
  refine ⟨50432470409090927462836367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134486587757575806567563645 50432470409090927462836367)
  ·
    refine ⟨75648705613636391194254551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50432470409090927462836367 75648705613636391194254551)
    ·
      refine ⟨113473058420454586791381827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75648705613636391194254551 113473058420454586791381827)
      ·
        refine ⟨170209587630681880187072741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113473058420454586791381827 170209587630681880187072741)
        ·
          refine ⟨31914297680752852535076139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170209587630681880187072741 31914297680752852535076139)
          ·
            refine ⟨47871446521129278802614209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31914297680752852535076139 47871446521129278802614209)
            ·
              refine ⟨35903584890846959101960657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47871446521129278802614209 35903584890846959101960657)
              ·
                refine ⟨26927688668135219326470493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35903584890846959101960657 26927688668135219326470493)
                ·
                  refine ⟨10097883250550707247426435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26927688668135219326470493 10097883250550707247426435)
                  ·
                    refine ⟨15146824875826060871139653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10097883250550707247426435 15146824875826060871139653)
                    ·
                      refine ⟨2840029664217386413338685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15146824875826060871139653 2840029664217386413338685)
                      ·
                        rfl

theorem cell23_5530938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_5530938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530938 prefixEnd_5530938 := by exact prefixLift 5530938
  have htrace : WordTrace (prefixWord ++ tailWord_5530938) baseStart_5530938 baseEnd_5530938 := by
    simpa [prefixWord, tailWord_5530938, baseEnd_5530938] using wordTrace_append hprefix tailTrace_5530938
  have hstable : (prefixWord ++ tailWord_5530938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530938).length < 2 ^ (prefixWord ++ tailWord_5530938).sum := by decide
  have hdescent : baseEnd_5530938 < baseStart_5530938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530961 : List Nat := [1, 2, 2, 1, 4, 1, 1, 11]
def baseStart_5530961 : Nat := 118140960795 + 5530961 * 2 ^ 59
def prefixEnd_5530961 : Nat := 4983230072969 + 3 ^ 40 * 5530961 * 2
def baseEnd_5530961 : Nat := 105186721269349623087077

theorem tailTrace_5530961 : CollatzResearch.WordTrace tailWord_5530961 prefixEnd_5530961 105186721269349623087077 := by
  unfold tailWord_5530961
  simp only [CollatzResearch.WordTrace]
  refine ⟨201730720515280384779432737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134487147010186923186288491 201730720515280384779432737)
  ·
    refine ⟨151298040386460288584574553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201730720515280384779432737 151298040386460288584574553)
    ·
      refine ⟨113473530289845216438430915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151298040386460288584574553 113473530289845216438430915)
      ·
        refine ⟨170210295434767824657646373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113473530289845216438430915 170210295434767824657646373)
        ·
          refine ⟨31914430394018967123308695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170210295434767824657646373 31914430394018967123308695)
          ·
            refine ⟨47871645591028450684963043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31914430394018967123308695 47871645591028450684963043)
            ·
              refine ⟨71807468386542676027444565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47871645591028450684963043 71807468386542676027444565)
              ·
                refine ⟨105186721269349623087077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 71807468386542676027444565 105186721269349623087077)
                ·
                  rfl

theorem cell23_5530961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 11].length) (baseStart_5530961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530961 prefixEnd_5530961 := by exact prefixLift 5530961
  have htrace : WordTrace (prefixWord ++ tailWord_5530961) baseStart_5530961 baseEnd_5530961 := by
    simpa [prefixWord, tailWord_5530961, baseEnd_5530961] using wordTrace_append hprefix tailTrace_5530961
  have hstable : (prefixWord ++ tailWord_5530961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530961).length < 2 ^ (prefixWord ++ tailWord_5530961).sum := by decide
  have hdescent : baseEnd_5530961 < baseStart_5530961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530968 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_5530968 : Nat := 118140960795 + 5530968 * 2 ^ 59
def prefixEnd_5530968 : Nat := 4983230072969 + 3 ^ 40 * 5530968 * 2
def baseEnd_5530968 : Nat := 2840045068637021295963547

theorem tailTrace_5530968 : CollatzResearch.WordTrace tailWord_5530968 prefixEnd_5530968 2840045068637021295963547 := by
  unfold tailWord_5530968
  simp only [CollatzResearch.WordTrace]
  refine ⟨100865487913127512487468779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134487317217503349983291705 100865487913127512487468779)
  ·
    refine ⟨151298231869691268731203169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100865487913127512487468779 151298231869691268731203169)
    ·
      refine ⟨113473673902268451548402377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151298231869691268731203169 113473673902268451548402377)
      ·
        refine ⟨85105255426701338661301783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113473673902268451548402377 85105255426701338661301783)
        ·
          refine ⟨127657883140052007991952675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85105255426701338661301783 127657883140052007991952675)
          ·
            refine ⟨191486824710078011987929013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127657883140052007991952675 191486824710078011987929013)
            ·
              refine ⟨17951889816569813623868345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191486824710078011987929013 17951889816569813623868345)
              ·
                refine ⟨13463917362427360217901259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17951889816569813623868345 13463917362427360217901259)
                ·
                  refine ⟨20195876043641040326851889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13463917362427360217901259 20195876043641040326851889)
                  ·
                    refine ⟨15146907032730780245138917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20195876043641040326851889 15146907032730780245138917)
                    ·
                      refine ⟨2840045068637021295963547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15146907032730780245138917 2840045068637021295963547)
                      ·
                        rfl

theorem cell23_5530968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_5530968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530968 prefixEnd_5530968 := by exact prefixLift 5530968
  have htrace : WordTrace (prefixWord ++ tailWord_5530968) baseStart_5530968 baseEnd_5530968 := by
    simpa [prefixWord, tailWord_5530968, baseEnd_5530968] using wordTrace_append hprefix tailTrace_5530968
  have hstable : (prefixWord ++ tailWord_5530968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530968).length < 2 ^ (prefixWord ++ tailWord_5530968).sum := by decide
  have hdescent : baseEnd_5530968 < baseStart_5530968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530983 : List Nat := [1, 1, 5, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_5530983 : Nat := 118140960795 + 5530983 * 2 ^ 59
def prefixEnd_5530983 : Nat := 4983230072969 + 3 ^ 40 * 5530983 * 2
def baseEnd_5530983 : Nat := 2840052770846838737275979

theorem tailTrace_5530983 : CollatzResearch.WordTrace tailWord_5530983 prefixEnd_5530983 2840052770846838737275979 := by
  unfold tailWord_5530983
  simp only [CollatzResearch.WordTrace]
  refine ⟨201731522921200682536733603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134487681947467121691155735 201731522921200682536733603)
  ·
    refine ⟨302597284381801023805100405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201731522921200682536733603 302597284381801023805100405)
    ·
      refine ⟨28368495410793845981728163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 302597284381801023805100405 28368495410793845981728163)
      ·
        refine ⟨42552743116190768972592245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28368495410793845981728163 42552743116190768972592245)
        ·
          refine ⟨3989319667142884591180523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42552743116190768972592245 3989319667142884591180523)
          ·
            refine ⟨5983979500714326886770785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3989319667142884591180523 5983979500714326886770785)
            ·
              refine ⟨4487984625535745165078089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5983979500714326886770785 4487984625535745165078089)
              ·
                refine ⟨3365988469151808873808567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4487984625535745165078089 3365988469151808873808567)
                ·
                  refine ⟨5048982703727713310712851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3365988469151808873808567 5048982703727713310712851)
                  ·
                    refine ⟨7573474055591569966069277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5048982703727713310712851 7573474055591569966069277)
                    ·
                      refine ⟨2840052770846838737275979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7573474055591569966069277 2840052770846838737275979)
                      ·
                        rfl

theorem cell23_5530983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_5530983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530983 prefixEnd_5530983 := by exact prefixLift 5530983
  have htrace : WordTrace (prefixWord ++ tailWord_5530983) baseStart_5530983 baseEnd_5530983 := by
    simpa [prefixWord, tailWord_5530983, baseEnd_5530983] using wordTrace_append hprefix tailTrace_5530983
  have hstable : (prefixWord ++ tailWord_5530983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530983).length < 2 ^ (prefixWord ++ tailWord_5530983).sum := by decide
  have hdescent : baseEnd_5530983 < baseStart_5530983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5530991 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 1, 9]
def baseStart_5530991 : Nat := 118140960795 + 5530991 * 2 ^ 59
def prefixEnd_5530991 : Nat := 4983230072969 + 3 ^ 40 * 5530991 * 2
def baseEnd_5530991 : Nat := 946685626230691568658647

theorem tailTrace_5530991 : CollatzResearch.WordTrace tailWord_5530991 prefixEnd_5530991 946685626230691568658647 := by
  unfold tailWord_5530991
  simp only [CollatzResearch.WordTrace]
  refine ⟨201731814705171699903024827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134487876470114466602016551 201731814705171699903024827)
  ·
    refine ⟨302597722057757549854537241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201731814705171699903024827 302597722057757549854537241)
    ·
      refine ⟨226948291543318162390902931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302597722057757549854537241 226948291543318162390902931)
      ·
        refine ⟨340422437314977243586354397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226948291543318162390902931 340422437314977243586354397)
        ·
          refine ⟨127658413993116466344882899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340422437314977243586354397 127658413993116466344882899)
          ·
            refine ⟨191487620989674699517324349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127658413993116466344882899 191487620989674699517324349)
            ·
              refine ⟨71807857871128012318996631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191487620989674699517324349 71807857871128012318996631)
              ·
                refine ⟨107711786806692018478494947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71807857871128012318996631 107711786806692018478494947)
                ·
                  refine ⟨161567680210038027717742421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107711786806692018478494947 161567680210038027717742421)
                  ·
                    refine ⟨946685626230691568658647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 161567680210038027717742421 946685626230691568658647)
                    ·
                      rfl

theorem cell23_5530991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_5530991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5530991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5530991 prefixEnd_5530991 := by exact prefixLift 5530991
  have htrace : WordTrace (prefixWord ++ tailWord_5530991) baseStart_5530991 baseEnd_5530991 := by
    simpa [prefixWord, tailWord_5530991, baseEnd_5530991] using wordTrace_append hprefix tailTrace_5530991
  have hstable : (prefixWord ++ tailWord_5530991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5530991).length < 2 ^ (prefixWord ++ tailWord_5530991).sum := by decide
  have hdescent : baseEnd_5530991 < baseStart_5530991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5530991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531005 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_5531005 : Nat := 118140960795 + 5531005 * 2 ^ 59
def prefixEnd_5531005 : Nat := 4983230072969 + 3 ^ 40 * 5531005 * 2
def baseEnd_5531005 : Nat := 2840064067421237651200877

theorem tailTrace_5531005 : CollatzResearch.WordTrace tailWord_5531005 prefixEnd_5531005 2840064067421237651200877 := by
  unfold tailWord_5531005
  simp only [CollatzResearch.WordTrace]
  refine ⟨201732325327120980294034469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134488216884747320196022979 201732325327120980294034469)
  ·
    refine ⟨37824810998835183805131463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201732325327120980294034469 37824810998835183805131463)
    ·
      refine ⟨56737216498252775707697195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37824810998835183805131463 56737216498252775707697195)
      ·
        refine ⟨85105824747379163561545793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56737216498252775707697195 85105824747379163561545793)
        ·
          refine ⟨63829368560534372671159345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85105824747379163561545793 63829368560534372671159345)
          ·
            refine ⟨47872026420400779503369509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63829368560534372671159345 47872026420400779503369509)
            ·
              refine ⟨8976004953825146156881783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47872026420400779503369509 8976004953825146156881783)
              ·
                refine ⟨13464007430737719235322675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8976004953825146156881783 13464007430737719235322675)
                ·
                  refine ⟨20196011146106578852984013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13464007430737719235322675 20196011146106578852984013)
                  ·
                    refine ⟨7573504179789967069869005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20196011146106578852984013 7573504179789967069869005)
                    ·
                      refine ⟨2840064067421237651200877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7573504179789967069869005 2840064067421237651200877)
                      ·
                        rfl

theorem cell23_5531005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_5531005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531005 prefixEnd_5531005 := by exact prefixLift 5531005
  have htrace : WordTrace (prefixWord ++ tailWord_5531005) baseStart_5531005 baseEnd_5531005 := by
    simpa [prefixWord, tailWord_5531005, baseEnd_5531005] using wordTrace_append hprefix tailTrace_5531005
  have hstable : (prefixWord ++ tailWord_5531005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531005).length < 2 ^ (prefixWord ++ tailWord_5531005).sum := by decide
  have hdescent : baseEnd_5531005 < baseStart_5531005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531039 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 2, 1, 3]
def baseStart_5531039 : Nat := 118140960795 + 5531039 * 2 ^ 59
def prefixEnd_5531039 : Nat := 4983230072969 + 3 ^ 40 * 5531039 * 2
def baseEnd_5531039 : Nat := 2840081525763490518175721

theorem tailTrace_5531039 : CollatzResearch.WordTrace tailWord_5531039 prefixEnd_5531039 2840081525763490518175721 := by
  unfold tailWord_5531039
  simp only [CollatzResearch.WordTrace]
  refine ⟨201733565408997804100772171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134489043605998536067181447 201733565408997804100772171)
  ·
    refine ⟨302600348113496706151158257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201733565408997804100772171 302600348113496706151158257)
    ·
      refine ⟨226950261085122529613368693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302600348113496706151158257 226950261085122529613368693)
      ·
        refine ⟨21276586976730237151253315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226950261085122529613368693 21276586976730237151253315)
        ·
          refine ⟨31914880465095355726879973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21276586976730237151253315 31914880465095355726879973)
          ·
            refine ⟨5984040087205379198789995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31914880465095355726879973 5984040087205379198789995)
            ·
              refine ⟨8976060130808068798184993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5984040087205379198789995 8976060130808068798184993)
              ·
                refine ⟨6732045098106051598638745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8976060130808068798184993 6732045098106051598638745)
                ·
                  refine ⟨5049033823579538698979059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6732045098106051598638745 5049033823579538698979059)
                  ·
                    refine ⟨7573550735369308048468589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5049033823579538698979059 7573550735369308048468589)
                    ·
                      refine ⟨2840081525763490518175721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7573550735369308048468589 2840081525763490518175721)
                      ·
                        rfl

theorem cell23_5531039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_5531039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531039 prefixEnd_5531039 := by exact prefixLift 5531039
  have htrace : WordTrace (prefixWord ++ tailWord_5531039) baseStart_5531039 baseEnd_5531039 := by
    simpa [prefixWord, tailWord_5531039, baseEnd_5531039] using wordTrace_append hprefix tailTrace_5531039
  have hstable : (prefixWord ++ tailWord_5531039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531039).length < 2 ^ (prefixWord ++ tailWord_5531039).sum := by decide
  have hdescent : baseEnd_5531039 < baseStart_5531039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531058 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_5531058 : Nat := 118140960795 + 5531058 * 2 ^ 59
def prefixEnd_5531058 : Nat := 4983230072969 + 3 ^ 40 * 5531058 * 2
def baseEnd_5531058 : Nat := 2840091281895925943838133

theorem tailTrace_5531058 : CollatzResearch.WordTrace tailWord_5531058 prefixEnd_5531058 2840091281895925943838133 := by
  unfold tailWord_5531058
  simp only [CollatzResearch.WordTrace]
  refine ⟨50433564598982242586428457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134489505597285980230475885 50433564598982242586428457)
  ·
    refine ⟨37825173449236681939821343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50433564598982242586428457 37825173449236681939821343)
    ·
      refine ⟨56737760173855022909732015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37825173449236681939821343 56737760173855022909732015)
      ·
        refine ⟨85106640260782534364598023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56737760173855022909732015 85106640260782534364598023)
        ·
          refine ⟨127659960391173801546897035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85106640260782534364598023 127659960391173801546897035)
          ·
            refine ⟨191489940586760702320345553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127659960391173801546897035 191489940586760702320345553)
            ·
              refine ⟨143617455440070526740259165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191489940586760702320345553 143617455440070526740259165)
              ·
                refine ⟨53856545790026447527597187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143617455440070526740259165 53856545790026447527597187)
                ·
                  refine ⟨80784818685039671291395781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53856545790026447527597187 80784818685039671291395781)
                  ·
                    refine ⟨15147153503444938367136709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80784818685039671291395781 15147153503444938367136709)
                    ·
                      refine ⟨2840091281895925943838133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15147153503444938367136709 2840091281895925943838133)
                      ·
                        rfl

theorem cell23_5531058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_5531058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531058 prefixEnd_5531058 := by exact prefixLift 5531058
  have htrace : WordTrace (prefixWord ++ tailWord_5531058) baseStart_5531058 baseEnd_5531058 := by
    simpa [prefixWord, tailWord_5531058, baseEnd_5531058] using wordTrace_append hprefix tailTrace_5531058
  have hstable : (prefixWord ++ tailWord_5531058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531058).length < 2 ^ (prefixWord ++ tailWord_5531058).sum := by decide
  have hdescent : baseEnd_5531058 < baseStart_5531058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531074 : List Nat := [3, 5, 2, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_5531074 : Nat := 118140960795 + 5531074 * 2 ^ 59
def prefixEnd_5531074 : Nat := 4983230072969 + 3 ^ 40 * 5531074 * 2
def baseEnd_5531074 : Nat := 2840099497586397881238061

theorem tailTrace_5531074 : CollatzResearch.WordTrace tailWord_5531074 prefixEnd_5531074 2840099497586397881238061 := by
  unfold tailWord_5531074
  simp only [CollatzResearch.WordTrace]
  refine ⟨50433710490967751269574069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134489894642580670052197517 50433710490967751269574069)
  ·
    refine ⟨4728160358528226681522569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50433710490967751269574069 4728160358528226681522569)
    ·
      refine ⟨3546120268896170011141927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4728160358528226681522569 3546120268896170011141927)
      ·
        refine ⟨5319180403344255016712891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546120268896170011141927 5319180403344255016712891)
        ·
          refine ⟨7978770605016382525069337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5319180403344255016712891 7978770605016382525069337)
          ·
            refine ⟨5984077953762286893802003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7978770605016382525069337 5984077953762286893802003)
            ·
              refine ⟨8976116930643430340703005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5984077953762286893802003 8976116930643430340703005)
              ·
                refine ⟨3366043848991286377763627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8976116930643430340703005 3366043848991286377763627)
                ·
                  refine ⟨5049065773486929566645441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366043848991286377763627 5049065773486929566645441)
                  ·
                    refine ⟨3786799330115197174984081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5049065773486929566645441 3786799330115197174984081)
                    ·
                      refine ⟨2840099497586397881238061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3786799330115197174984081 2840099497586397881238061)
                      ·
                        rfl

theorem cell23_5531074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_5531074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531074 prefixEnd_5531074 := by exact prefixLift 5531074
  have htrace : WordTrace (prefixWord ++ tailWord_5531074) baseStart_5531074 baseEnd_5531074 := by
    simpa [prefixWord, tailWord_5531074, baseEnd_5531074] using wordTrace_append hprefix tailTrace_5531074
  have hstable : (prefixWord ++ tailWord_5531074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531074).length < 2 ^ (prefixWord ++ tailWord_5531074).sum := by decide
  have hdescent : baseEnd_5531074 < baseStart_5531074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531135 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 3, 6, 2]
def baseStart_5531135 : Nat := 118140960795 + 5531135 * 2 ^ 59
def prefixEnd_5531135 : Nat := 4983230072969 + 3 ^ 40 * 5531135 * 2
def baseEnd_5531135 : Nat := 2840130819906322142575279

theorem tailTrace_5531135 : CollatzResearch.WordTrace tailWord_5531135 prefixEnd_5531135 2840130819906322142575279 := by
  unfold tailWord_5531135
  simp only [CollatzResearch.WordTrace]
  refine ⟨201737066816650012496266859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134491377877766674997511239 201737066816650012496266859)
  ·
    refine ⟨302605600224975018744400289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201737066816650012496266859 302605600224975018744400289)
    ·
      refine ⟨226954200168731264058300217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302605600224975018744400289 226954200168731264058300217)
      ·
        refine ⟨170215650126548448043725163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226954200168731264058300217 170215650126548448043725163)
        ·
          refine ⟨255323475189822672065587745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170215650126548448043725163 255323475189822672065587745)
          ·
            refine ⟨191492606392367004049190809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255323475189822672065587745 191492606392367004049190809)
            ·
              refine ⟨143619454794275253036893107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191492606392367004049190809 143619454794275253036893107)
              ·
                refine ⟨215429182191412879555339661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143619454794275253036893107 215429182191412879555339661)
                ·
                  refine ⟨80785943321779829833252373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215429182191412879555339661 80785943321779829833252373)
                  ·
                    refine ⟨3786841093208429523433705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80785943321779829833252373 3786841093208429523433705)
                    ·
                      refine ⟨2840130819906322142575279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3786841093208429523433705 2840130819906322142575279)
                      ·
                        rfl

theorem cell23_5531135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 6, 2].length) (baseStart_5531135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531135 prefixEnd_5531135 := by exact prefixLift 5531135
  have htrace : WordTrace (prefixWord ++ tailWord_5531135) baseStart_5531135 baseEnd_5531135 := by
    simpa [prefixWord, tailWord_5531135, baseEnd_5531135] using wordTrace_append hprefix tailTrace_5531135
  have hstable : (prefixWord ++ tailWord_5531135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531135).length < 2 ^ (prefixWord ++ tailWord_5531135).sum := by decide
  have hdescent : baseEnd_5531135 < baseStart_5531135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531189 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_5531189 : Nat := 118140960795 + 5531189 * 2 ^ 59
def prefixEnd_5531189 : Nat := 4983230072969 + 3 ^ 40 * 5531189 * 2
def baseEnd_5531189 : Nat := 2840158547861664931300031

theorem tailTrace_5531189 : CollatzResearch.WordTrace tailWord_5531189 prefixEnd_5531189 2840158547861664931300031 := by
  unfold tailWord_5531189
  simp only [CollatzResearch.WordTrace]
  refine ⟨201739036358454379718732621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134492690905636253145821747 201739036358454379718732621)
  ·
    refine ⟨75652138634420392394524733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201739036358454379718732621 75652138634420392394524733)
    ·
      refine ⟨28369551987907647147946775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75652138634420392394524733 28369551987907647147946775)
      ·
        refine ⟨42554327981861470721920163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28369551987907647147946775 42554327981861470721920163)
        ·
          refine ⟨63831491972792206082880245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42554327981861470721920163 63831491972792206082880245)
          ·
            refine ⟨5984202372449269320270023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63831491972792206082880245 5984202372449269320270023)
            ·
              refine ⟨8976303558673903980405035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5984202372449269320270023 8976303558673903980405035)
              ·
                refine ⟨13464455338010855970607553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8976303558673903980405035 13464455338010855970607553)
                ·
                  refine ⟨10098341503508141977955665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13464455338010855970607553 10098341503508141977955665)
                  ·
                    refine ⟨7573756127631106483466749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10098341503508141977955665 7573756127631106483466749)
                    ·
                      refine ⟨2840158547861664931300031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7573756127631106483466749 2840158547861664931300031)
                      ·
                        rfl

theorem cell23_5531189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_5531189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531189 prefixEnd_5531189 := by exact prefixLift 5531189
  have htrace : WordTrace (prefixWord ++ tailWord_5531189) baseStart_5531189 baseEnd_5531189 := by
    simpa [prefixWord, tailWord_5531189, baseEnd_5531189] using wordTrace_append hprefix tailTrace_5531189
  have hstable : (prefixWord ++ tailWord_5531189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531189).length < 2 ^ (prefixWord ++ tailWord_5531189).sum := by decide
  have hdescent : baseEnd_5531189 < baseStart_5531189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531196 : List Nat := [2, 2, 2, 2, 4, 1, 2, 3, 1, 4]
def baseStart_5531196 : Nat := 118140960795 + 5531196 * 2 ^ 59
def prefixEnd_5531196 : Nat := 4983230072969 + 3 ^ 40 * 5531196 * 2
def baseEnd_5531196 : Nat := 946720714075415467970833

theorem tailTrace_5531196 : CollatzResearch.WordTrace tailWord_5531196 prefixEnd_5531196 946720714075415467970833 := by
  unfold tailWord_5531196
  simp only [CollatzResearch.WordTrace]
  refine ⟨100869645834714509957118721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134492861112952679942824961 100869645834714509957118721)
  ·
    refine ⟨75652234376035882467839041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100869645834714509957118721 75652234376035882467839041)
    ·
      refine ⟨56739175782026911850879281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75652234376035882467839041 56739175782026911850879281)
      ·
        refine ⟨42554381836520183888159461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56739175782026911850879281 42554381836520183888159461)
        ·
          refine ⟨7978946594347534479029899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42554381836520183888159461 7978946594347534479029899)
          ·
            refine ⟨11968419891521301718544849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7978946594347534479029899 11968419891521301718544849)
            ·
              refine ⟨8976314918640976288908637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11968419891521301718544849 8976314918640976288908637)
              ·
                refine ⟨3366118094490366108340739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8976314918640976288908637 3366118094490366108340739)
                ·
                  refine ⟨5049177141735549162511109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366118094490366108340739 5049177141735549162511109)
                  ·
                    refine ⟨946720714075415467970833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5049177141735549162511109 946720714075415467970833)
                    ·
                      rfl

theorem cell23_5531196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_5531196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531196 prefixEnd_5531196 := by exact prefixLift 5531196
  have htrace : WordTrace (prefixWord ++ tailWord_5531196) baseStart_5531196 baseEnd_5531196 := by
    simpa [prefixWord, tailWord_5531196, baseEnd_5531196] using wordTrace_append hprefix tailTrace_5531196
  have hstable : (prefixWord ++ tailWord_5531196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531196).length < 2 ^ (prefixWord ++ tailWord_5531196).sum := by decide
  have hdescent : baseEnd_5531196 < baseStart_5531196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531225 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 4]
def baseStart_5531225 : Nat := 118140960795 + 5531225 * 2 ^ 59
def prefixEnd_5531225 : Nat := 4983230072969 + 3 ^ 40 * 5531225 * 2
def baseEnd_5531225 : Nat := 2840177033165226790449865

theorem tailTrace_5531225 : CollatzResearch.WordTrace tailWord_5531225 prefixEnd_5531225 2840177033165226790449865 := by
  unfold tailWord_5531225
  simp only [CollatzResearch.WordTrace]
  refine ⟨201740349386323957867043129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134493566257549305244695419 201740349386323957867043129)
  ·
    refine ⟨151305262039742968400282347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201740349386323957867043129 151305262039742968400282347)
    ·
      refine ⟨226957893059614452600423521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151305262039742968400282347 226957893059614452600423521)
      ·
        refine ⟨170218419794710839450317641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226957893059614452600423521 170218419794710839450317641)
        ·
          refine ⟨127663814846033129587738231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170218419794710839450317641 127663814846033129587738231)
          ·
            refine ⟨191495722269049694381607347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127663814846033129587738231 191495722269049694381607347)
            ·
              refine ⟨287243583403574541572411021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191495722269049694381607347 287243583403574541572411021)
              ·
                refine ⟨107716343776340453089654133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287243583403574541572411021 107716343776340453089654133)
                ·
                  refine ⟨10098407229031917477155075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107716343776340453089654133 10098407229031917477155075)
                  ·
                    refine ⟨15147610843547876215732613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10098407229031917477155075 15147610843547876215732613)
                    ·
                      refine ⟨2840177033165226790449865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15147610843547876215732613 2840177033165226790449865)
                      ·
                        rfl

theorem cell23_5531225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_5531225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531225 prefixEnd_5531225 := by exact prefixLift 5531225
  have htrace : WordTrace (prefixWord ++ tailWord_5531225) baseStart_5531225 baseEnd_5531225 := by
    simpa [prefixWord, tailWord_5531225, baseEnd_5531225] using wordTrace_append hprefix tailTrace_5531225
  have hstable : (prefixWord ++ tailWord_5531225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531225).length < 2 ^ (prefixWord ++ tailWord_5531225).sum := by decide
  have hdescent : baseEnd_5531225 < baseStart_5531225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531253 : List Nat := [1, 3, 4, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5531253 : Nat := 118140960795 + 5531253 * 2 ^ 59
def prefixEnd_5531253 : Nat := 4983230072969 + 3 ^ 40 * 5531253 * 2
def baseEnd_5531253 : Nat := 2840191410623552680899737

theorem tailTrace_5531253 : CollatzResearch.WordTrace tailWord_5531253 prefixEnd_5531253 2840191410623552680899737 := by
  unfold tailWord_5531253
  simp only [CollatzResearch.WordTrace]
  refine ⟨201741370630222518649062413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134494247086815012432708275 201741370630222518649062413)
  ·
    refine ⟨75653013986333444493398405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201741370630222518649062413 75653013986333444493398405)
    ·
      refine ⟨14184940122437520842512201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75653013986333444493398405 14184940122437520842512201)
      ·
        refine ⟨10638705091828140631884151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14184940122437520842512201 10638705091828140631884151)
        ·
          refine ⟨15958057637742210947826227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10638705091828140631884151 15958057637742210947826227)
          ·
            refine ⟨23937086456613316421739341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15958057637742210947826227 23937086456613316421739341)
            ·
              refine ⟨8976407421229993658152253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23937086456613316421739341 8976407421229993658152253)
              ·
                refine ⟨3366152782961247621807095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8976407421229993658152253 3366152782961247621807095)
                ·
                  refine ⟨5049229174441871432710643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366152782961247621807095 5049229174441871432710643)
                  ·
                    refine ⟨7573843761662807149065965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5049229174441871432710643 7573843761662807149065965)
                    ·
                      refine ⟨2840191410623552680899737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7573843761662807149065965 2840191410623552680899737)
                      ·
                        rfl

theorem cell23_5531253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5531253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531253 prefixEnd_5531253 := by exact prefixLift 5531253
  have htrace : WordTrace (prefixWord ++ tailWord_5531253) baseStart_5531253 baseEnd_5531253 := by
    simpa [prefixWord, tailWord_5531253, baseEnd_5531253] using wordTrace_append hprefix tailTrace_5531253
  have hstable : (prefixWord ++ tailWord_5531253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531253).length < 2 ^ (prefixWord ++ tailWord_5531253).sum := by decide
  have hdescent : baseEnd_5531253 < baseStart_5531253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531255 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_5531255 : Nat := 118140960795 + 5531255 * 2 ^ 59
def prefixEnd_5531255 : Nat := 4983230072969 + 3 ^ 40 * 5531255 * 2
def baseEnd_5531255 : Nat := 2840192437584861673074727

theorem tailTrace_5531255 : CollatzResearch.WordTrace tailWord_5531255 prefixEnd_5531255 2840192437584861673074727 := by
  unfold tailWord_5531255
  simp only [CollatzResearch.WordTrace]
  refine ⟨201741443576215272990635219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134494295717476848660423479 201741443576215272990635219)
  ·
    refine ⟨302612165364322909485952829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201741443576215272990635219 302612165364322909485952829)
    ·
      refine ⟨113479562011621091057232311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302612165364322909485952829 113479562011621091057232311)
      ·
        refine ⟨170219343017431636585848467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113479562011621091057232311 170219343017431636585848467)
        ·
          refine ⟨255329014526147454878772701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170219343017431636585848467 255329014526147454878772701)
          ·
            refine ⟨95748380447305295579539763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255329014526147454878772701 95748380447305295579539763)
            ·
              refine ⟨143622570670957943369309645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95748380447305295579539763 143622570670957943369309645)
              ·
                refine ⟨53858464001609228763491117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143622570670957943369309645 53858464001609228763491117)
                ·
                  refine ⟨20196924000603460786309169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53858464001609228763491117 20196924000603460786309169)
                  ·
                    refine ⟨15147693000452595589731877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20196924000603460786309169 15147693000452595589731877)
                    ·
                      refine ⟨2840192437584861673074727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15147693000452595589731877 2840192437584861673074727)
                      ·
                        rfl

theorem cell23_5531255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_5531255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531255 prefixEnd_5531255 := by exact prefixLift 5531255
  have htrace : WordTrace (prefixWord ++ tailWord_5531255) baseStart_5531255 baseEnd_5531255 := by
    simpa [prefixWord, tailWord_5531255, baseEnd_5531255] using wordTrace_append hprefix tailTrace_5531255
  have hstable : (prefixWord ++ tailWord_5531255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531255).length < 2 ^ (prefixWord ++ tailWord_5531255).sum := by decide
  have hdescent : baseEnd_5531255 < baseStart_5531255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531265 : List Nat := [1, 2, 4, 2, 1, 2, 11]
def baseStart_5531265 : Nat := 118140960795 + 5531265 * 2 ^ 59
def prefixEnd_5531265 : Nat := 4983230072969 + 3 ^ 40 * 5531265 * 2
def baseEnd_5531265 : Nat := 35064167560387736221601

theorem tailTrace_5531265 : CollatzResearch.WordTrace tailWord_5531265 prefixEnd_5531265 35064167560387736221601 := by
  unfold tailWord_5531265
  simp only [CollatzResearch.WordTrace]
  refine ⟨201741808306179044698499249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134494538870786029798999499 201741808306179044698499249)
  ·
    refine ⟨151306356229634283523874437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201741808306179044698499249 151306356229634283523874437)
    ·
      refine ⟨28369941793056428160726457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151306356229634283523874437 28369941793056428160726457)
      ·
        refine ⟨21277456344792321120544843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28369941793056428160726457 21277456344792321120544843)
        ·
          refine ⟨31916184517188481680817265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21277456344792321120544843 31916184517188481680817265)
          ·
            refine ⟨23937138387891361260612949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31916184517188481680817265 23937138387891361260612949)
            ·
              refine ⟨35064167560387736221601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23937138387891361260612949 35064167560387736221601)
              ·
                rfl

theorem cell23_5531265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 11].length) (baseStart_5531265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531265 prefixEnd_5531265 := by exact prefixLift 5531265
  have htrace : WordTrace (prefixWord ++ tailWord_5531265) baseStart_5531265 baseEnd_5531265 := by
    simpa [prefixWord, tailWord_5531265, baseEnd_5531265] using wordTrace_append hprefix tailTrace_5531265
  have hstable : (prefixWord ++ tailWord_5531265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531265).length < 2 ^ (prefixWord ++ tailWord_5531265).sum := by decide
  have hdescent : baseEnd_5531265 < baseStart_5531265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531296 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 3]
def baseStart_5531296 : Nat := 118140960795 + 5531296 * 2 ^ 59
def prefixEnd_5531296 : Nat := 4983230072969 + 3 ^ 40 * 5531296 * 2
def baseEnd_5531296 : Nat := 2840213490291696012662039

theorem tailTrace_5531296 : CollatzResearch.WordTrace tailWord_5531296 prefixEnd_5531296 2840213490291696012662039 := by
  unfold tailWord_5531296
  simp only [CollatzResearch.WordTrace]
  refine ⟨100871469484533368496438871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134495292646044491328585161 100871469484533368496438871)
  ·
    refine ⟨151307204226800052744658307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100871469484533368496438871 151307204226800052744658307)
    ·
      refine ⟨226960806340200079116987461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151307204226800052744658307 226960806340200079116987461)
      ·
        refine ⟨42555151188787514834435149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226960806340200079116987461 42555151188787514834435149)
        ·
          refine ⟨15958181695795318062913181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42555151188787514834435149 15958181695795318062913181)
          ·
            refine ⟨5984318135923244273592443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15958181695795318062913181 5984318135923244273592443)
            ·
              refine ⟨8976477203884866410388665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5984318135923244273592443 8976477203884866410388665)
              ·
                refine ⟨6732357902913649807791499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8976477203884866410388665 6732357902913649807791499)
                ·
                  refine ⟨10098536854370474711687249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6732357902913649807791499 10098536854370474711687249)
                  ·
                    refine ⟨7573902640777856033765437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10098536854370474711687249 7573902640777856033765437)
                    ·
                      refine ⟨2840213490291696012662039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7573902640777856033765437 2840213490291696012662039)
                      ·
                        rfl

theorem cell23_5531296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_5531296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531296 prefixEnd_5531296 := by exact prefixLift 5531296
  have htrace : WordTrace (prefixWord ++ tailWord_5531296) baseStart_5531296 baseEnd_5531296 := by
    simpa [prefixWord, tailWord_5531296, baseEnd_5531296] using wordTrace_append hprefix tailTrace_5531296
  have hstable : (prefixWord ++ tailWord_5531296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531296).length < 2 ^ (prefixWord ++ tailWord_5531296).sum := by decide
  have hdescent : baseEnd_5531296 < baseStart_5531296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531309 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_5531309 : Nat := 118140960795 + 5531309 * 2 ^ 59
def prefixEnd_5531309 : Nat := 4983230072969 + 3 ^ 40 * 5531309 * 2
def baseEnd_5531309 : Nat := 2840220165540204461799479

theorem tailTrace_5531309 : CollatzResearch.WordTrace tailWord_5531309 prefixEnd_5531309 2840220165540204461799479 := by
  unfold tailWord_5531309
  simp only [CollatzResearch.WordTrace]
  refine ⟨201743413118019640213100981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134495608745346426808733987 201743413118019640213100981)
  ·
    refine ⟨18913444979814341269978217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201743413118019640213100981 18913444979814341269978217)
    ·
      refine ⟨14185083734860755952483663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18913444979814341269978217 14185083734860755952483663)
      ·
        refine ⟨21277625602291133928725495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14185083734860755952483663 21277625602291133928725495)
        ·
          refine ⟨31916438403436700893088243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21277625602291133928725495 31916438403436700893088243)
          ·
            refine ⟨47874657605155051339632365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31916438403436700893088243 47874657605155051339632365)
            ·
              refine ⟨17952996601933144252362137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47874657605155051339632365 17952996601933144252362137)
              ·
                refine ⟨13464747451449858189271603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17952996601933144252362137 13464747451449858189271603)
                ·
                  refine ⟨20197121177174787283907405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13464747451449858189271603 20197121177174787283907405)
                  ·
                    refine ⟨7573920441440545231465277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20197121177174787283907405 7573920441440545231465277)
                    ·
                      refine ⟨2840220165540204461799479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7573920441440545231465277 2840220165540204461799479)
                      ·
                        rfl

theorem cell23_5531309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_5531309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531309 prefixEnd_5531309 := by exact prefixLift 5531309
  have htrace : WordTrace (prefixWord ++ tailWord_5531309) baseStart_5531309 baseEnd_5531309 := by
    simpa [prefixWord, tailWord_5531309, baseEnd_5531309] using wordTrace_append hprefix tailTrace_5531309
  have hstable : (prefixWord ++ tailWord_5531309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531309).length < 2 ^ (prefixWord ++ tailWord_5531309).sum := by decide
  have hdescent : baseEnd_5531309 < baseStart_5531309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531326 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_5531326 : Nat := 118140960795 + 5531326 * 2 ^ 59
def prefixEnd_5531326 : Nat := 4983230072969 + 3 ^ 40 * 5531326 * 2
def baseEnd_5531326 : Nat := 2840228894711330895286901

theorem tailTrace_5531326 : CollatzResearch.WordTrace tailWord_5531326 prefixEnd_5531326 2840228894711330895286901 := by
  unfold tailWord_5531326
  simp only [CollatzResearch.WordTrace]
  refine ⟨25218004144869756514558729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134496022105972034744313221 25218004144869756514558729)
  ·
    refine ⟨18913503108652317385919047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25218004144869756514558729 18913503108652317385919047)
    ·
      refine ⟨28370254662978476078878571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18913503108652317385919047 28370254662978476078878571)
      ·
        refine ⟨42555381994467714118317857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28370254662978476078878571 42555381994467714118317857)
        ·
          refine ⟨31916536495850785588738393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42555381994467714118317857 31916536495850785588738393)
          ·
            refine ⟨23937402371888089191553795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31916536495850785588738393 23937402371888089191553795)
            ·
              refine ⟨35906103557832133787330693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23937402371888089191553795 35906103557832133787330693)
              ·
                refine ⟨6732394417093525085124505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35906103557832133787330693 6732394417093525085124505)
                ·
                  refine ⟨5049295812820143813843379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6732394417093525085124505 5049295812820143813843379)
                  ·
                    refine ⟨7573943719230215720765069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5049295812820143813843379 7573943719230215720765069)
                    ·
                      refine ⟨2840228894711330895286901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7573943719230215720765069 2840228894711330895286901)
                      ·
                        rfl

theorem cell23_5531326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_5531326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531326 prefixEnd_5531326 := by exact prefixLift 5531326
  have htrace : WordTrace (prefixWord ++ tailWord_5531326) baseStart_5531326 baseEnd_5531326 := by
    simpa [prefixWord, tailWord_5531326, baseEnd_5531326] using wordTrace_append hprefix tailTrace_5531326
  have hstable : (prefixWord ++ tailWord_5531326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531326).length < 2 ^ (prefixWord ++ tailWord_5531326).sum := by decide
  have hdescent : baseEnd_5531326 < baseStart_5531326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531332 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_5531332 : Nat := 118140960795 + 5531332 * 2 ^ 59
def prefixEnd_5531332 : Nat := 4983230072969 + 3 ^ 40 * 5531332 * 2
def baseEnd_5531332 : Nat := 2840231975595257871811873

theorem tailTrace_5531332 : CollatzResearch.WordTrace tailWord_5531332 prefixEnd_5531332 2840231975595257871811873 := by
  unfold tailWord_5531332
  simp only [CollatzResearch.WordTrace]
  refine ⟨100872125998468157570594125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134496167997957543427458833 100872125998468157570594125)
  ·
    refine ⟨37827047249425559088972797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100872125998468157570594125 37827047249425559088972797)
    ·
      refine ⟨14185142718534584658364799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37827047249425559088972797 14185142718534584658364799)
      ·
        refine ⟨21277714077801876987547199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14185142718534584658364799 21277714077801876987547199)
        ·
          refine ⟨31916571116702815481320799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21277714077801876987547199 31916571116702815481320799)
          ·
            refine ⟨47874856675054223221981199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31916571116702815481320799 47874856675054223221981199)
            ·
              refine ⟨71812285012581334832971799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47874856675054223221981199 71812285012581334832971799)
              ·
                refine ⟨107718427518872002249457699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71812285012581334832971799 107718427518872002249457699)
                ·
                  refine ⟨161577641278308003374186549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107718427518872002249457699 161577641278308003374186549)
                  ·
                    refine ⟨15147903869841375316329989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 161577641278308003374186549 15147903869841375316329989)
                    ·
                      refine ⟨2840231975595257871811873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15147903869841375316329989 2840231975595257871811873)
                      ·
                        rfl

theorem cell23_5531332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_5531332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531332 prefixEnd_5531332 := by exact prefixLift 5531332
  have htrace : WordTrace (prefixWord ++ tailWord_5531332) baseStart_5531332 baseEnd_5531332 := by
    simpa [prefixWord, tailWord_5531332, baseEnd_5531332] using wordTrace_append hprefix tailTrace_5531332
  have hstable : (prefixWord ++ tailWord_5531332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531332).length < 2 ^ (prefixWord ++ tailWord_5531332).sum := by decide
  have hdescent : baseEnd_5531332 < baseStart_5531332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531342 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_5531342 : Nat := 118140960795 + 5531342 * 2 ^ 59
def prefixEnd_5531342 : Nat := 4983230072969 + 3 ^ 40 * 5531342 * 2
def baseEnd_5531342 : Nat := 946745703467267610895609

theorem tailTrace_5531342 : CollatzResearch.WordTrace tailWord_5531342 prefixEnd_5531342 946745703467267610895609 := by
  unfold tailWord_5531342
  simp only [CollatzResearch.WordTrace]
  refine ⟨25218077090862510856131535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134496411151266724566034853 25218077090862510856131535)
  ·
    refine ⟨37827115636293766284197303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25218077090862510856131535 37827115636293766284197303)
    ·
      refine ⟨56740673454440649426295955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37827115636293766284197303 56740673454440649426295955)
      ·
        refine ⟨85111010181660974139443933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56740673454440649426295955 85111010181660974139443933)
        ·
          refine ⟨31916628818122865302291475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85111010181660974139443933 31916628818122865302291475)
          ·
            refine ⟨47874943227184297953437213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31916628818122865302291475 47874943227184297953437213)
            ·
              refine ⟨17953103710194111732538955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47874943227184297953437213 17953103710194111732538955)
              ·
                refine ⟨26929655565291167598808433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17953103710194111732538955 26929655565291167598808433)
                ·
                  refine ⟨20197241673968375699106325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26929655565291167598808433 20197241673968375699106325)
                  ·
                    refine ⟨946745703467267610895609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20197241673968375699106325 946745703467267610895609)
                    ·
                      rfl

theorem cell23_5531342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_5531342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531342 prefixEnd_5531342 := by exact prefixLift 5531342
  have htrace : WordTrace (prefixWord ++ tailWord_5531342) baseStart_5531342 baseEnd_5531342 := by
    simpa [prefixWord, tailWord_5531342, baseEnd_5531342] using wordTrace_append hprefix tailTrace_5531342
  have hstable : (prefixWord ++ tailWord_5531342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531342).length < 2 ^ (prefixWord ++ tailWord_5531342).sum := by decide
  have hdescent : baseEnd_5531342 < baseStart_5531342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531352 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 2, 4, 3]
def baseStart_5531352 : Nat := 118140960795 + 5531352 * 2 ^ 59
def prefixEnd_5531352 : Nat := 4983230072969 + 3 ^ 40 * 5531352 * 2
def baseEnd_5531352 : Nat := 2840242245208347793561781

theorem tailTrace_5531352 : CollatzResearch.WordTrace tailWord_5531352 prefixEnd_5531352 2840242245208347793561781 := by
  unfold tailWord_5531352
  simp only [CollatzResearch.WordTrace]
  refine ⟨100872490728431929278458155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134496654304575905704610873 100872490728431929278458155)
  ·
    refine ⟨151308736092647893917687233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100872490728431929278458155 151308736092647893917687233)
    ·
      refine ⟨113481552069485920438265425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151308736092647893917687233 113481552069485920438265425)
      ·
        refine ⟨85111164052114440328699069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113481552069485920438265425 85111164052114440328699069)
        ·
          refine ⟨31916686519542915123262151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85111164052114440328699069 31916686519542915123262151)
          ·
            refine ⟨47875029779314372684893227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31916686519542915123262151 47875029779314372684893227)
            ·
              refine ⟨71812544668971559027339841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47875029779314372684893227 71812544668971559027339841)
              ·
                refine ⟨53859408501728669270504881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71812544668971559027339841 53859408501728669270504881)
                ·
                  refine ⟨40394556376296501952878661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53859408501728669270504881 40394556376296501952878661)
                  ·
                    refine ⟨7573979320555594116164749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40394556376296501952878661 7573979320555594116164749)
                    ·
                      refine ⟨2840242245208347793561781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7573979320555594116164749 2840242245208347793561781)
                      ·
                        rfl

theorem cell23_5531352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_5531352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531352 prefixEnd_5531352 := by exact prefixLift 5531352
  have htrace : WordTrace (prefixWord ++ tailWord_5531352) baseStart_5531352 baseEnd_5531352 := by
    simpa [prefixWord, tailWord_5531352, baseEnd_5531352] using wordTrace_append hprefix tailTrace_5531352
  have hstable : (prefixWord ++ tailWord_5531352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531352).length < 2 ^ (prefixWord ++ tailWord_5531352).sum := by decide
  have hdescent : baseEnd_5531352 < baseStart_5531352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531402 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_5531402 : Nat := 118140960795 + 5531402 * 2 ^ 59
def prefixEnd_5531402 : Nat := 4983230072969 + 3 ^ 40 * 5531402 * 2
def baseEnd_5531402 : Nat := 946755973080357532645517

theorem tailTrace_5531402 : CollatzResearch.WordTrace tailWord_5531402 prefixEnd_5531402 946755973080357532645517 := by
  unfold tailWord_5531402
  simp only [CollatzResearch.WordTrace]
  refine ⟨50436701276670679274059115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134497870071121811397490973 50436701276670679274059115)
  ·
    refine ⟨75655051915006018911088673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50436701276670679274059115 75655051915006018911088673)
    ·
      refine ⟨56741288936254514183316505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75655051915006018911088673 56741288936254514183316505)
      ·
        refine ⟨42555966702190885637487379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56741288936254514183316505 42555966702190885637487379)
        ·
          refine ⟨63833950053286328456231069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42555966702190885637487379 63833950053286328456231069)
          ·
            refine ⟨23937731269982373171086651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63833950053286328456231069 23937731269982373171086651)
            ·
              refine ⟨35906596904973559756629977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23937731269982373171086651 35906596904973559756629977)
              ·
                refine ⟨26929947678730169817472483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35906596904973559756629977 26929947678730169817472483)
                ·
                  refine ⟨40394921518095254726208725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26929947678730169817472483 40394921518095254726208725)
                  ·
                    refine ⟨946755973080357532645517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40394921518095254726208725 946755973080357532645517)
                    ·
                      rfl

theorem cell23_5531402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_5531402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531402 prefixEnd_5531402 := by exact prefixLift 5531402
  have htrace : WordTrace (prefixWord ++ tailWord_5531402) baseStart_5531402 baseEnd_5531402 := by
    simpa [prefixWord, tailWord_5531402, baseEnd_5531402] using wordTrace_append hprefix tailTrace_5531402
  have hstable : (prefixWord ++ tailWord_5531402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531402).length < 2 ^ (prefixWord ++ tailWord_5531402).sum := by decide
  have hdescent : baseEnd_5531402 < baseStart_5531402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531446 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5531446 : Nat := 118140960795 + 5531446 * 2 ^ 59
def prefixEnd_5531446 : Nat := 4983230072969 + 3 ^ 40 * 5531446 * 2
def baseEnd_5531446 : Nat := 2840290512389870425786349

theorem tailTrace_5531446 : CollatzResearch.WordTrace tailWord_5531446 prefixEnd_5531446 2840290512389870425786349 := by
  unfold tailWord_5531446
  simp only [CollatzResearch.WordTrace]
  refine ⟨12609275619907707038177387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134498939945682208407225461 12609275619907707038177387)
  ·
    refine ⟨18913913429861560557266081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12609275619907707038177387 18913913429861560557266081)
    ·
      refine ⟨14185435072396170417949561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18913913429861560557266081 14185435072396170417949561)
      ·
        refine ⟨10639076304297127813462171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14185435072396170417949561 10639076304297127813462171)
        ·
          refine ⟨15958614456445691720193257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10639076304297127813462171 15958614456445691720193257)
          ·
            refine ⟨11968960842334268790144943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15958614456445691720193257 11968960842334268790144943)
            ·
              refine ⟨17953441263501403185217415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11968960842334268790144943 17953441263501403185217415)
              ·
                refine ⟨26930161895252104777826123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17953441263501403185217415 26930161895252104777826123)
                ·
                  refine ⟨40395242842878157166739185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26930161895252104777826123 40395242842878157166739185)
                  ·
                    refine ⟨30296432132158617875054389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40395242842878157166739185 30296432132158617875054389)
                    ·
                      refine ⟨2840290512389870425786349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30296432132158617875054389 2840290512389870425786349)
                      ·
                        rfl

theorem cell23_5531446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5531446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531446 prefixEnd_5531446 := by exact prefixLift 5531446
  have htrace : WordTrace (prefixWord ++ tailWord_5531446) baseStart_5531446 baseEnd_5531446 := by
    simpa [prefixWord, tailWord_5531446, baseEnd_5531446] using wordTrace_append hprefix tailTrace_5531446
  have hstable : (prefixWord ++ tailWord_5531446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531446).length < 2 ^ (prefixWord ++ tailWord_5531446).sum := by decide
  have hdescent : baseEnd_5531446 < baseStart_5531446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531452 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_5531452 : Nat := 118140960795 + 5531452 * 2 ^ 59
def prefixEnd_5531452 : Nat := 4983230072969 + 3 ^ 40 * 5531452 * 2
def baseEnd_5531452 : Nat := 2840293593273797402311321

theorem tailTrace_5531452 : CollatzResearch.WordTrace tailWord_5531452 prefixEnd_5531452 2840293593273797402311321 := by
  unfold tailWord_5531452
  simp only [CollatzResearch.WordTrace]
  refine ⟨100874314378250787817778305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134499085837667717090371073 100874314378250787817778305)
  ·
    refine ⟨75655735783688090863333729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100874314378250787817778305 75655735783688090863333729)
    ·
      refine ⟨56741801837766068147500297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75655735783688090863333729 56741801837766068147500297)
      ·
        refine ⟨42556351378324551110625223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56741801837766068147500297 42556351378324551110625223)
        ·
          refine ⟨63834527067486826665937835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42556351378324551110625223 63834527067486826665937835)
          ·
            refine ⟨95751790601230239998906753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63834527067486826665937835 95751790601230239998906753)
            ·
              refine ⟨71813842950922679999180065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95751790601230239998906753 71813842950922679999180065)
              ·
                refine ⟨53860382213192009999385049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71813842950922679999180065 53860382213192009999385049)
                ·
                  refine ⟨40395286659894007499538787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53860382213192009999385049 40395286659894007499538787)
                  ·
                    refine ⟨60592929989841011249308181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40395286659894007499538787 60592929989841011249308181)
                    ·
                      refine ⟨2840293593273797402311321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60592929989841011249308181 2840293593273797402311321)
                      ·
                        rfl

theorem cell23_5531452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_5531452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531452 prefixEnd_5531452 := by exact prefixLift 5531452
  have htrace : WordTrace (prefixWord ++ tailWord_5531452) baseStart_5531452 baseEnd_5531452 := by
    simpa [prefixWord, tailWord_5531452, baseEnd_5531452] using wordTrace_append hprefix tailTrace_5531452
  have hstable : (prefixWord ++ tailWord_5531452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531452).length < 2 ^ (prefixWord ++ tailWord_5531452).sum := by decide
  have hdescent : baseEnd_5531452 < baseStart_5531452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531476 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_5531476 : Nat := 118140960795 + 5531476 * 2 ^ 59
def prefixEnd_5531476 : Nat := 4983230072969 + 3 ^ 40 * 5531476 * 2
def baseEnd_5531476 : Nat := 2840305916809505308411211

theorem tailTrace_5531476 : CollatzResearch.WordTrace tailWord_5531476 prefixEnd_5531476 2840305916809505308411211 := by
  unfold tailWord_5531476
  simp only [CollatzResearch.WordTrace]
  refine ⟨100874752054207313867215141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134499669405609751822953521 100874752054207313867215141)
  ·
    refine ⟨18914016010163871350102839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100874752054207313867215141 18914016010163871350102839)
    ·
      refine ⟨28371024015245807025154259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18914016010163871350102839 28371024015245807025154259)
      ·
        refine ⟨42556536022868710537731389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28371024015245807025154259 42556536022868710537731389)
        ·
          refine ⟨15958701008575766451649271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42556536022868710537731389 15958701008575766451649271)
          ·
            refine ⟨23938051512863649677473907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15958701008575766451649271 23938051512863649677473907)
            ·
              refine ⟨35907077269295474516210861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23938051512863649677473907 35907077269295474516210861)
              ·
                refine ⟨13465153975985802943579073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35907077269295474516210861 13465153975985802943579073)
                ·
                  refine ⟨10098865481989352207684305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13465153975985802943579073 10098865481989352207684305)
                  ·
                    refine ⟨7574149111492014155763229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10098865481989352207684305 7574149111492014155763229)
                    ·
                      refine ⟨2840305916809505308411211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7574149111492014155763229 2840305916809505308411211)
                      ·
                        rfl

theorem cell23_5531476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_5531476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531476 prefixEnd_5531476 := by exact prefixLift 5531476
  have htrace : WordTrace (prefixWord ++ tailWord_5531476) baseStart_5531476 baseEnd_5531476 := by
    simpa [prefixWord, tailWord_5531476, baseEnd_5531476] using wordTrace_append hprefix tailTrace_5531476
  have hstable : (prefixWord ++ tailWord_5531476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531476).length < 2 ^ (prefixWord ++ tailWord_5531476).sum := by decide
  have hdescent : baseEnd_5531476 < baseStart_5531476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531499 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 3, 5, 2]
def baseStart_5531499 : Nat := 118140960795 + 5531499 * 2 ^ 59
def prefixEnd_5531499 : Nat := 4983230072969 + 3 ^ 40 * 5531499 * 2
def baseEnd_5531499 : Nat := 2840317726864558718423605

theorem tailTrace_5531499 : CollatzResearch.WordTrace tailWord_5531499 prefixEnd_5531499 2840317726864558718423605 := by
  unfold tailWord_5531499
  simp only [CollatzResearch.WordTrace]
  refine ⟨201750342987331302662517551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134500228658220868441678367 201750342987331302662517551)
  ·
    refine ⟨302625514480996953993776327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201750342987331302662517551 302625514480996953993776327)
    ·
      refine ⟨453938271721495430990664491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302625514480996953993776327 453938271721495430990664491)
      ·
        refine ⟨680907407582243146485996737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453938271721495430990664491 680907407582243146485996737)
        ·
          refine ⟨510680555686682359864497553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680907407582243146485996737 510680555686682359864497553)
          ·
            refine ⟨383010416765011769898373165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510680555686682359864497553 383010416765011769898373165)
            ·
              refine ⟨143628906286879413711889937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383010416765011769898373165 143628906286879413711889937)
              ·
                refine ⟨107721679715159560283917453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143628906286879413711889937 107721679715159560283917453)
                ·
                  refine ⟨40395629893184835106469045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107721679715159560283917453 40395629893184835106469045)
                  ·
                    refine ⟨3787090302486078291231473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40395629893184835106469045 3787090302486078291231473)
                    ·
                      refine ⟨2840317726864558718423605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787090302486078291231473 2840317726864558718423605)
                      ·
                        rfl

theorem cell23_5531499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 5, 2].length) (baseStart_5531499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531499 prefixEnd_5531499 := by exact prefixLift 5531499
  have htrace : WordTrace (prefixWord ++ tailWord_5531499) baseStart_5531499 baseEnd_5531499 := by
    simpa [prefixWord, tailWord_5531499, baseEnd_5531499] using wordTrace_append hprefix tailTrace_5531499
  have hstable : (prefixWord ++ tailWord_5531499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531499).length < 2 ^ (prefixWord ++ tailWord_5531499).sum := by decide
  have hdescent : baseEnd_5531499 < baseStart_5531499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531500 : List Nat := [2, 2, 1, 1, 4, 4, 2, 2, 1, 4]
def baseStart_5531500 : Nat := 118140960795 + 5531500 * 2 ^ 59
def prefixEnd_5531500 : Nat := 4983230072969 + 3 ^ 40 * 5531500 * 2
def baseEnd_5531500 : Nat := 946772746781737738170367

theorem tailTrace_5531500 : CollatzResearch.WordTrace tailWord_5531500 prefixEnd_5531500 946772746781737738170367 := by
  unfold tailWord_5531500
  simp only [CollatzResearch.WordTrace]
  refine ⟨100875189730163839916651977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134500252973551786555535969 100875189730163839916651977)
  ·
    refine ⟨75656392297622879937488983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100875189730163839916651977 75656392297622879937488983)
    ·
      refine ⟨113484588446434319906233475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75656392297622879937488983 113484588446434319906233475)
      ·
        refine ⟨170226882669651479859350213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113484588446434319906233475 170226882669651479859350213)
        ·
          refine ⟨31917540500559652473628165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170226882669651479859350213 31917540500559652473628165)
          ·
            refine ⟨5984538843854934838805281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31917540500559652473628165 5984538843854934838805281)
            ·
              refine ⟨4488404132891201129103961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5984538843854934838805281 4488404132891201129103961)
              ·
                refine ⟨3366303099668400846827971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4488404132891201129103961 3366303099668400846827971)
                ·
                  refine ⟨5049454649502601270241957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366303099668400846827971 5049454649502601270241957)
                  ·
                    refine ⟨946772746781737738170367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5049454649502601270241957 946772746781737738170367)
                    ·
                      rfl

theorem cell23_5531500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_5531500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531500 prefixEnd_5531500 := by exact prefixLift 5531500
  have htrace : WordTrace (prefixWord ++ tailWord_5531500) baseStart_5531500 baseEnd_5531500 := by
    simpa [prefixWord, tailWord_5531500, baseEnd_5531500] using wordTrace_append hprefix tailTrace_5531500
  have hstable : (prefixWord ++ tailWord_5531500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531500).length < 2 ^ (prefixWord ++ tailWord_5531500).sum := by decide
  have hdescent : baseEnd_5531500 < baseStart_5531500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531506 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_5531506 : Nat := 118140960795 + 5531506 * 2 ^ 59
def prefixEnd_5531506 : Nat := 4983230072969 + 3 ^ 40 * 5531506 * 2
def baseEnd_5531506 : Nat := 2840321321229140191036073

theorem tailTrace_5531506 : CollatzResearch.WordTrace tailWord_5531506 prefixEnd_5531506 2840321321229140191036073 := by
  unfold tailWord_5531506
  simp only [CollatzResearch.WordTrace]
  refine ⟨50437649574576485714505593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134500398865537295238681581 50437649574576485714505593)
  ·
    refine ⟨37828237180932364285879195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50437649574576485714505593 37828237180932364285879195)
    ·
      refine ⟨56742355771398546428818793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37828237180932364285879195 56742355771398546428818793)
      ·
        refine ⟨42556766828548909821614095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56742355771398546428818793 42556766828548909821614095)
        ·
          refine ⟨63835150242823364732421143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42556766828548909821614095 63835150242823364732421143)
          ·
            refine ⟨95752725364235047098631715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63835150242823364732421143 95752725364235047098631715)
            ·
              refine ⟨143629088046352570647947573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95752725364235047098631715 143629088046352570647947573)
              ·
                refine ⟨13465227004345553498245085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143629088046352570647947573 13465227004345553498245085)
                ·
                  refine ⟨5049460126629582561841907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13465227004345553498245085 5049460126629582561841907)
                  ·
                    refine ⟨7574190189944373842762861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5049460126629582561841907 7574190189944373842762861)
                    ·
                      refine ⟨2840321321229140191036073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7574190189944373842762861 2840321321229140191036073)
                      ·
                        rfl

theorem cell23_5531506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_5531506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531506 prefixEnd_5531506 := by exact prefixLift 5531506
  have htrace : WordTrace (prefixWord ++ tailWord_5531506) baseStart_5531506 baseEnd_5531506 := by
    simpa [prefixWord, tailWord_5531506, baseEnd_5531506] using wordTrace_append hprefix tailTrace_5531506
  have hstable : (prefixWord ++ tailWord_5531506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531506).length < 2 ^ (prefixWord ++ tailWord_5531506).sum := by decide
  have hdescent : baseEnd_5531506 < baseStart_5531506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531509 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_5531509 : Nat := 118140960795 + 5531509 * 2 ^ 59
def prefixEnd_5531509 : Nat := 4983230072969 + 3 ^ 40 * 5531509 * 2
def baseEnd_5531509 : Nat := 946774287223701226432853

theorem tailTrace_5531509 : CollatzResearch.WordTrace tailWord_5531509 prefixEnd_5531509 946774287223701226432853 := by
  unfold tailWord_5531509
  simp only [CollatzResearch.WordTrace]
  refine ⟨201750707717295074370381581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134500471811530049580254387 201750707717295074370381581)
  ·
    refine ⟨75656515393985652888893093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201750707717295074370381581 75656515393985652888893093)
    ·
      refine ⟨14185596636372309916667455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75656515393985652888893093 14185596636372309916667455)
      ·
        refine ⟨21278394954558464875001183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14185596636372309916667455 21278394954558464875001183)
        ·
          refine ⟨31917592431837697312501775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21278394954558464875001183 31917592431837697312501775)
          ·
            refine ⟨47876388647756545968752663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31917592431837697312501775 47876388647756545968752663)
            ·
              refine ⟨71814582971634818953128995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47876388647756545968752663 71814582971634818953128995)
              ·
                refine ⟨107721874457452228429693493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71814582971634818953128995 107721874457452228429693493)
                ·
                  refine ⟨10098925730386146415283765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107721874457452228429693493 10098925730386146415283765)
                  ·
                    refine ⟨946774287223701226432853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10098925730386146415283765 946774287223701226432853)
                    ·
                      rfl

theorem cell23_5531509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_5531509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531509 prefixEnd_5531509 := by exact prefixLift 5531509
  have htrace : WordTrace (prefixWord ++ tailWord_5531509) baseStart_5531509 baseEnd_5531509 := by
    simpa [prefixWord, tailWord_5531509, baseEnd_5531509] using wordTrace_append hprefix tailTrace_5531509
  have hstable : (prefixWord ++ tailWord_5531509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531509).length < 2 ^ (prefixWord ++ tailWord_5531509).sum := by decide
  have hdescent : baseEnd_5531509 < baseStart_5531509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531529 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 4]
def baseStart_5531529 : Nat := 118140960795 + 5531529 * 2 ^ 59
def prefixEnd_5531529 : Nat := 4983230072969 + 3 ^ 40 * 5531529 * 2
def baseEnd_5531529 : Nat := 2840333131284193601048467

theorem tailTrace_5531529 : CollatzResearch.WordTrace tailWord_5531529 prefixEnd_5531529 2840333131284193601048467 := by
  unfold tailWord_5531529
  simp only [CollatzResearch.WordTrace]
  refine ⟨201751437177222617786109641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134500958118148411857406427 201751437177222617786109641)
  ·
    refine ⟨151313577882916963339582231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201751437177222617786109641 151313577882916963339582231)
    ·
      refine ⟨226970366824375445009373347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151313577882916963339582231 226970366824375445009373347)
      ·
        refine ⟨340455550236563167514060021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226970366824375445009373347 340455550236563167514060021)
        ·
          refine ⟨31917707834677796954443127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 340455550236563167514060021 31917707834677796954443127)
          ·
            refine ⟨47876561752016695431664691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31917707834677796954443127 47876561752016695431664691)
            ·
              refine ⟨71814842628025043147497037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47876561752016695431664691 71814842628025043147497037)
              ·
                refine ⟨26930565985509391180311389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71814842628025043147497037 26930565985509391180311389)
                ·
                  refine ⟨10098962244566021692616771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26930565985509391180311389 10098962244566021692616771)
                  ·
                    refine ⟨15148443366849032538925157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10098962244566021692616771 15148443366849032538925157)
                    ·
                      refine ⟨2840333131284193601048467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15148443366849032538925157 2840333131284193601048467)
                      ·
                        rfl

theorem cell23_5531529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_5531529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531529 prefixEnd_5531529 := by exact prefixLift 5531529
  have htrace : WordTrace (prefixWord ++ tailWord_5531529) baseStart_5531529 baseEnd_5531529 := by
    simpa [prefixWord, tailWord_5531529, baseEnd_5531529] using wordTrace_append hprefix tailTrace_5531529
  have hstable : (prefixWord ++ tailWord_5531529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531529).length < 2 ^ (prefixWord ++ tailWord_5531529).sum := by decide
  have hdescent : baseEnd_5531529 < baseStart_5531529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531540 : List Nat := [2, 4, 2, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_5531540 : Nat := 118140960795 + 5531540 * 2 ^ 59
def prefixEnd_5531540 : Nat := 4983230072969 + 3 ^ 40 * 5531540 * 2
def baseEnd_5531540 : Nat := 2840338779571393058010917

theorem tailTrace_5531540 : CollatzResearch.WordTrace tailWord_5531540 prefixEnd_5531540 2840338779571393058010917 := by
  unfold tailWord_5531540
  simp only [CollatzResearch.WordTrace]
  refine ⟨100875919190091383332380037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134501225586788511109840049 100875919190091383332380037)
  ·
    refine ⟨18914234848142134374821257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100875919190091383332380037 18914234848142134374821257)
    ·
      refine ⟨14185676136106600781115943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18914234848142134374821257 14185676136106600781115943)
      ·
        refine ⟨21278514204159901171673915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14185676136106600781115943 21278514204159901171673915)
        ·
          refine ⟨31917771306239851757510873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21278514204159901171673915 31917771306239851757510873)
          ·
            refine ⟨23938328479679888818133155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31917771306239851757510873 23938328479679888818133155)
            ·
              refine ⟨35907492719519833227199733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23938328479679888818133155 35907492719519833227199733)
              ·
                refine ⟨3366327442454984365049975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35907492719519833227199733 3366327442454984365049975)
                ·
                  refine ⟨5049491163682476547574963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366327442454984365049975 5049491163682476547574963)
                  ·
                    refine ⟨7574236745523714821362445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5049491163682476547574963 7574236745523714821362445)
                    ·
                      refine ⟨2840338779571393058010917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7574236745523714821362445 2840338779571393058010917)
                      ·
                        rfl

theorem cell23_5531540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_5531540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531540 prefixEnd_5531540 := by exact prefixLift 5531540
  have htrace : WordTrace (prefixWord ++ tailWord_5531540) baseStart_5531540 baseEnd_5531540 := by
    simpa [prefixWord, tailWord_5531540, baseEnd_5531540] using wordTrace_append hprefix tailTrace_5531540
  have hstable : (prefixWord ++ tailWord_5531540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531540).length < 2 ^ (prefixWord ++ tailWord_5531540).sum := by decide
  have hdescent : baseEnd_5531540 < baseStart_5531540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531543 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 1, 5]
def baseStart_5531543 : Nat := 118140960795 + 5531543 * 2 ^ 59
def prefixEnd_5531543 : Nat := 4983230072969 + 3 ^ 40 * 5531543 * 2
def baseEnd_5531543 : Nat := 946780106671118848757801

theorem tailTrace_5531543 : CollatzResearch.WordTrace tailWord_5531543 prefixEnd_5531543 946780106671118848757801 := by
  unfold tailWord_5531543
  simp only [CollatzResearch.WordTrace]
  refine ⟨201751947799171898177119283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134501298532781265451412855 201751947799171898177119283)
  ·
    refine ⟨302627921698757847265678925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201751947799171898177119283 302627921698757847265678925)
    ·
      refine ⟨113485470637034192724629597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302627921698757847265678925 113485470637034192724629597)
      ·
        refine ⟨42557051488887822271736099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113485470637034192724629597 42557051488887822271736099)
        ·
          refine ⟨63835577233331733407604149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42557051488887822271736099 63835577233331733407604149)
          ·
            refine ⟨5984585365624850006962889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63835577233331733407604149 5984585365624850006962889)
            ·
              refine ⟨4488439024218637505222167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5984585365624850006962889 4488439024218637505222167)
              ·
                refine ⟨6732658536327956257833251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4488439024218637505222167 6732658536327956257833251)
                ·
                  refine ⟨10098987804491934386749877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6732658536327956257833251 10098987804491934386749877)
                  ·
                    refine ⟨946780106671118848757801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10098987804491934386749877 946780106671118848757801)
                    ·
                      rfl

theorem cell23_5531543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_5531543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531543 prefixEnd_5531543 := by exact prefixLift 5531543
  have htrace : WordTrace (prefixWord ++ tailWord_5531543) baseStart_5531543 baseEnd_5531543 := by
    simpa [prefixWord, tailWord_5531543, baseEnd_5531543] using wordTrace_append hprefix tailTrace_5531543
  have hstable : (prefixWord ++ tailWord_5531543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531543).length < 2 ^ (prefixWord ++ tailWord_5531543).sum := by decide
  have hdescent : baseEnd_5531543 < baseStart_5531543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531556 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_5531556 : Nat := 118140960795 + 5531556 * 2 ^ 59
def prefixEnd_5531556 : Nat := 4983230072969 + 3 ^ 40 * 5531556 * 2
def baseEnd_5531556 : Nat := 946782331753954998470281

theorem tailTrace_5531556 : CollatzResearch.WordTrace tailWord_5531556 prefixEnd_5531556 946782331753954998470281 := by
  unfold tailWord_5531556
  simp only [CollatzResearch.WordTrace]
  refine ⟨100876210974062400698671261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134501614632083200931561681 100876210974062400698671261)
  ·
    refine ⟨37828579115273400262001723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100876210974062400698671261 37828579115273400262001723)
    ·
      refine ⟨56742868672910100393002585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37828579115273400262001723 56742868672910100393002585)
      ·
        refine ⟨42557151504682575294751939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56742868672910100393002585 42557151504682575294751939)
        ·
          refine ⟨63835727257023862942127909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42557151504682575294751939 63835727257023862942127909)
          ·
            refine ⟨11969198860691974301648983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63835727257023862942127909 11969198860691974301648983)
            ·
              refine ⟨17953798291037961452473475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11969198860691974301648983 17953798291037961452473475)
              ·
                refine ⟨26930697436556942178710213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17953798291037961452473475 26930697436556942178710213)
                ·
                  refine ⟨5049505769354426658508165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26930697436556942178710213 5049505769354426658508165)
                  ·
                    refine ⟨946782331753954998470281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5049505769354426658508165 946782331753954998470281)
                    ·
                      rfl

theorem cell23_5531556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_5531556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531556 prefixEnd_5531556 := by exact prefixLift 5531556
  have htrace : WordTrace (prefixWord ++ tailWord_5531556) baseStart_5531556 baseEnd_5531556 := by
    simpa [prefixWord, tailWord_5531556, baseEnd_5531556] using wordTrace_append hprefix tailTrace_5531556
  have hstable : (prefixWord ++ tailWord_5531556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531556).length < 2 ^ (prefixWord ++ tailWord_5531556).sum := by decide
  have hdescent : baseEnd_5531556 < baseStart_5531556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531580 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5531580 : Nat := 118140960795 + 5531580 * 2 ^ 59
def prefixEnd_5531580 : Nat := 4983230072969 + 3 ^ 40 * 5531580 * 2
def baseEnd_5531580 : Nat := 2840359318797572901510733

theorem tailTrace_5531580 : CollatzResearch.WordTrace tailWord_5531580 prefixEnd_5531580 2840359318797572901510733 := by
  unfold tailWord_5531580
  simp only [CollatzResearch.WordTrace]
  refine ⟨100876648650018926748108097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134502198200025235664144129 100876648650018926748108097)
  ·
    refine ⟨75657486487514195061081073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100876648650018926748108097 75657486487514195061081073)
    ·
      refine ⟨56743114865635646295810805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75657486487514195061081073 56743114865635646295810805)
      ·
        refine ⟨5319667018653341840232263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56743114865635646295810805 5319667018653341840232263)
        ·
          refine ⟨7979500527980012760348395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5319667018653341840232263 7979500527980012760348395)
          ·
            refine ⟨11969250791970019140522593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7979500527980012760348395 11969250791970019140522593)
            ·
              refine ⟨8976938093977514355391945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11969250791970019140522593 8976938093977514355391945)
              ·
                refine ⟨6732703570483135766543959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8976938093977514355391945 6732703570483135766543959)
                ·
                  refine ⟨10099055355724703649815939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6732703570483135766543959 10099055355724703649815939)
                  ·
                    refine ⟨15148583033587055474723909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10099055355724703649815939 15148583033587055474723909)
                    ·
                      refine ⟨2840359318797572901510733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15148583033587055474723909 2840359318797572901510733)
                      ·
                        rfl

theorem cell23_5531580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5531580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531580 prefixEnd_5531580 := by exact prefixLift 5531580
  have htrace : WordTrace (prefixWord ++ tailWord_5531580) baseStart_5531580 baseEnd_5531580 := by
    simpa [prefixWord, tailWord_5531580, baseEnd_5531580] using wordTrace_append hprefix tailTrace_5531580
  have hstable : (prefixWord ++ tailWord_5531580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531580).length < 2 ^ (prefixWord ++ tailWord_5531580).sum := by decide
  have hdescent : baseEnd_5531580 < baseStart_5531580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531630 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_5531630 : Nat := 118140960795 + 5531630 * 2 ^ 59
def prefixEnd_5531630 : Nat := 4983230072969 + 3 ^ 40 * 5531630 * 2
def baseEnd_5531630 : Nat := 2840384992830297705885503

theorem tailTrace_5531630 : CollatzResearch.WordTrace tailWord_5531630 prefixEnd_5531630 2840384992830297705885503 := by
  unfold tailWord_5531630
  simp only [CollatzResearch.WordTrace]
  refine ⟨25219390118732089004442043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134503413966571141357024229 25219390118732089004442043)
  ·
    refine ⟨37829085178098133506663065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25219390118732089004442043 37829085178098133506663065)
    ·
      refine ⟨28371813883573600129997299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37829085178098133506663065 28371813883573600129997299)
      ·
        refine ⟨42557720825360400194995949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28371813883573600129997299 42557720825360400194995949)
        ·
          refine ⟨15959145309510150073123481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42557720825360400194995949 15959145309510150073123481)
          ·
            refine ⟨11969358982132612554842611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15959145309510150073123481 11969358982132612554842611)
            ·
              refine ⟨17954038473198918832263917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11969358982132612554842611 17954038473198918832263917)
              ·
                refine ⟨6732764427449594562098969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17954038473198918832263917 6732764427449594562098969)
                ·
                  refine ⟨5049573320587195921574227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6732764427449594562098969 5049573320587195921574227)
                  ·
                    refine ⟨7574359980880793882361341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5049573320587195921574227 7574359980880793882361341)
                    ·
                      refine ⟨2840384992830297705885503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7574359980880793882361341 2840384992830297705885503)
                      ·
                        rfl

theorem cell23_5531630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_5531630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531630 prefixEnd_5531630 := by exact prefixLift 5531630
  have htrace : WordTrace (prefixWord ++ tailWord_5531630) baseStart_5531630 baseEnd_5531630 := by
    simpa [prefixWord, tailWord_5531630, baseEnd_5531630] using wordTrace_append hprefix tailTrace_5531630
  have hstable : (prefixWord ++ tailWord_5531630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531630).length < 2 ^ (prefixWord ++ tailWord_5531630).sum := by decide
  have hdescent : baseEnd_5531630 < baseStart_5531630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531653 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 1, 4, 2]
def baseStart_5531653 : Nat := 118140960795 + 5531653 * 2 ^ 59
def prefixEnd_5531653 : Nat := 4983230072969 + 3 ^ 40 * 5531653 * 2
def baseEnd_5531653 : Nat := 2840396802885351115897897

theorem tailTrace_5531653 : CollatzResearch.WordTrace tailWord_5531653 prefixEnd_5531653 2840396802885351115897897 := by
  unfold tailWord_5531653
  simp only [CollatzResearch.WordTrace]
  refine ⟨201755959828773386963623613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134503973219182257975749075 201755959828773386963623613)
  ·
    refine ⟨75658484935790020111358855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201755959828773386963623613 75658484935790020111358855)
    ·
      refine ⟨113487727403685030167038283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75658484935790020111358855 113487727403685030167038283)
      ·
        refine ⟨170231591105527545250557425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113487727403685030167038283 170231591105527545250557425)
        ·
          refine ⟨127673693329145658937918069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170231591105527545250557425 127673693329145658937918069)
          ·
            refine ⟨11969408749607405525429819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127673693329145658937918069 11969408749607405525429819)
            ·
              refine ⟨17954113124411108288144729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11969408749607405525429819 17954113124411108288144729)
              ·
                refine ⟨13465584843308331216108547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17954113124411108288144729 13465584843308331216108547)
                ·
                  refine ⟨20198377264962496824162821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13465584843308331216108547 20198377264962496824162821)
                  ·
                    refine ⟨3787195737180468154530529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20198377264962496824162821 3787195737180468154530529)
                    ·
                      refine ⟨2840396802885351115897897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787195737180468154530529 2840396802885351115897897)
                      ·
                        rfl

theorem cell23_5531653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 4, 2].length) (baseStart_5531653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531653 prefixEnd_5531653 := by exact prefixLift 5531653
  have htrace : WordTrace (prefixWord ++ tailWord_5531653) baseStart_5531653 baseEnd_5531653 := by
    simpa [prefixWord, tailWord_5531653, baseEnd_5531653] using wordTrace_append hprefix tailTrace_5531653
  have hstable : (prefixWord ++ tailWord_5531653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531653).length < 2 ^ (prefixWord ++ tailWord_5531653).sum := by decide
  have hdescent : baseEnd_5531653 < baseStart_5531653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531687 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_5531687 : Nat := 118140960795 + 5531687 * 2 ^ 59
def prefixEnd_5531687 : Nat := 4983230072969 + 3 ^ 40 * 5531687 * 2
def baseEnd_5531687 : Nat := 2840414261227603982872741

theorem tailTrace_5531687 : CollatzResearch.WordTrace tailWord_5531687 prefixEnd_5531687 2840414261227603982872741 := by
  unfold tailWord_5531687
  simp only [CollatzResearch.WordTrace]
  refine ⟨201757199910650210770361315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134504799940433473846907543 201757199910650210770361315)
  ·
    refine ⟨302635799865975316155541973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201757199910650210770361315 302635799865975316155541973)
    ·
      refine ⟨7093026559358796472395515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 302635799865975316155541973 7093026559358796472395515)
      ·
        refine ⟨10639539839038194708593273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7093026559358796472395515 10639539839038194708593273)
        ·
          refine ⟨7979654879278646031444955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10639539839038194708593273 7979654879278646031444955)
          ·
            refine ⟨11969482318917969047167433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7979654879278646031444955 11969482318917969047167433)
            ·
              refine ⟨8977111739188476785375575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11969482318917969047167433 8977111739188476785375575)
              ·
                refine ⟨13465667608782715178063363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8977111739188476785375575 13465667608782715178063363)
                ·
                  refine ⟨20198501413174072767095045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13465667608782715178063363 20198501413174072767095045)
                  ·
                    refine ⟨3787219014970138643830321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20198501413174072767095045 3787219014970138643830321)
                    ·
                      refine ⟨2840414261227603982872741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787219014970138643830321 2840414261227603982872741)
                      ·
                        rfl

theorem cell23_5531687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_5531687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531687 prefixEnd_5531687 := by exact prefixLift 5531687
  have htrace : WordTrace (prefixWord ++ tailWord_5531687) baseStart_5531687 baseEnd_5531687 := by
    simpa [prefixWord, tailWord_5531687, baseEnd_5531687] using wordTrace_append hprefix tailTrace_5531687
  have hstable : (prefixWord ++ tailWord_5531687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531687).length < 2 ^ (prefixWord ++ tailWord_5531687).sum := by decide
  have hdescent : baseEnd_5531687 < baseStart_5531687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531699 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 7]
def baseStart_5531699 : Nat := 118140960795 + 5531699 * 2 ^ 59
def prefixEnd_5531699 : Nat := 4983230072969 + 3 ^ 40 * 5531699 * 2
def baseEnd_5531699 : Nat := 2840420422995457935922685

theorem tailTrace_5531699 : CollatzResearch.WordTrace tailWord_5531699 prefixEnd_5531699 2840420422995457935922685 := by
  unfold tailWord_5531699
  simp only [CollatzResearch.WordTrace]
  refine ⟨201757637586606736819798151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134505091724404491213198767 201757637586606736819798151)
  ·
    refine ⟨302636456379910105229697227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201757637586606736819798151 302636456379910105229697227)
    ·
      refine ⟨453954684569865157844545841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302636456379910105229697227 453954684569865157844545841)
      ·
        refine ⟨340466013427398868383409381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453954684569865157844545841 340466013427398868383409381)
        ·
          refine ⟨63837377517637287821889259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340466013427398868383409381 63837377517637287821889259)
          ·
            refine ⟨95756066276455931732833889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63837377517637287821889259 95756066276455931732833889)
            ·
              refine ⟨71817049707341948799625417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95756066276455931732833889 71817049707341948799625417)
              ·
                refine ⟨53862787280506461599719063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71817049707341948799625417 53862787280506461599719063)
                ·
                  refine ⟨80794180920759692399578595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53862787280506461599719063 80794180920759692399578595)
                  ·
                    refine ⟨121191271381139538599367893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80794180920759692399578595 121191271381139538599367893)
                    ·
                      refine ⟨2840420422995457935922685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121191271381139538599367893 2840420422995457935922685)
                      ·
                        rfl

theorem cell23_5531699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_5531699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531699 prefixEnd_5531699 := by exact prefixLift 5531699
  have htrace : WordTrace (prefixWord ++ tailWord_5531699) baseStart_5531699 baseEnd_5531699 := by
    simpa [prefixWord, tailWord_5531699, baseEnd_5531699] using wordTrace_append hprefix tailTrace_5531699
  have hstable : (prefixWord ++ tailWord_5531699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531699).length < 2 ^ (prefixWord ++ tailWord_5531699).sum := by decide
  have hdescent : baseEnd_5531699 < baseStart_5531699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531803 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 4, 3, 2]
def baseStart_5531803 : Nat := 118140960795 + 5531803 * 2 ^ 59
def prefixEnd_5531803 : Nat := 4983230072969 + 3 ^ 40 * 5531803 * 2
def baseEnd_5531803 : Nat := 2840473824983525529022207

theorem tailTrace_5531803 : CollatzResearch.WordTrace tailWord_5531803 prefixEnd_5531803 2840473824983525529022207 := by
  unfold tailWord_5531803
  simp only [CollatzResearch.WordTrace]
  refine ⟨201761430778229962581584063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134507620518819975054389375 201761430778229962581584063)
  ·
    refine ⟨302642146167344943872376095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201761430778229962581584063 302642146167344943872376095)
    ·
      refine ⟨453963219251017415808564143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302642146167344943872376095 453963219251017415808564143)
      ·
        refine ⟨680944828876526123712846215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453963219251017415808564143 680944828876526123712846215)
        ·
          refine ⟨1021417243314789185569269323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680944828876526123712846215 1021417243314789185569269323)
          ·
            refine ⟨1532125864972183778353903985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021417243314789185569269323 1532125864972183778353903985)
            ·
              refine ⟨1149094398729137833765427989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532125864972183778353903985 1149094398729137833765427989)
              ·
                refine ⟨53863799940428335957754437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1149094398729137833765427989 53863799940428335957754437)
                ·
                  refine ⟨10099462488830312992078957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53863799940428335957754437 10099462488830312992078957)
                  ·
                    refine ⟨3787298433311367372029609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10099462488830312992078957 3787298433311367372029609)
                    ·
                      refine ⟨2840473824983525529022207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787298433311367372029609 2840473824983525529022207)
                      ·
                        rfl

theorem cell23_5531803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 3, 2].length) (baseStart_5531803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531803 prefixEnd_5531803 := by exact prefixLift 5531803
  have htrace : WordTrace (prefixWord ++ tailWord_5531803) baseStart_5531803 baseEnd_5531803 := by
    simpa [prefixWord, tailWord_5531803, baseEnd_5531803] using wordTrace_append hprefix tailTrace_5531803
  have hstable : (prefixWord ++ tailWord_5531803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531803).length < 2 ^ (prefixWord ++ tailWord_5531803).sum := by decide
  have hdescent : baseEnd_5531803 < baseStart_5531803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531844 : List Nat := [2, 3, 3, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_5531844 : Nat := 118140960795 + 5531844 * 2 ^ 59
def prefixEnd_5531844 : Nat := 4983230072969 + 3 ^ 40 * 5531844 * 2
def baseEnd_5531844 : Nat := 2840494877690359868609519

theorem tailTrace_5531844 : CollatzResearch.WordTrace tailWord_5531844 prefixEnd_5531844 2840494877690359868609519 := by
  unfold tailWord_5531844
  simp only [CollatzResearch.WordTrace]
  refine ⟨100881463085540713291913293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134508617447387617722551057 100881463085540713291913293)
  ·
    refine ⟨37830548657077767484467485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100881463085540713291913293 37830548657077767484467485)
    ·
      refine ⟨14186455746404162806675307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37830548657077767484467485 14186455746404162806675307)
      ·
        refine ⟨21279683619606244210012961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14186455746404162806675307 21279683619606244210012961)
        ·
          refine ⟨15959762714704683157509721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21279683619606244210012961 15959762714704683157509721)
          ·
            refine ⟨11969822036028512368132291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15959762714704683157509721 11969822036028512368132291)
            ·
              refine ⟨17954733054042768552198437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11969822036028512368132291 17954733054042768552198437)
              ·
                refine ⟨3366512447633019103537207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17954733054042768552198437 3366512447633019103537207)
                ·
                  refine ⟨5049768671449528655305811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366512447633019103537207 5049768671449528655305811)
                  ·
                    refine ⟨7574653007174292982958717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5049768671449528655305811 7574653007174292982958717)
                    ·
                      refine ⟨2840494877690359868609519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7574653007174292982958717 2840494877690359868609519)
                      ·
                        rfl

theorem cell23_5531844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_5531844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531844 prefixEnd_5531844 := by exact prefixLift 5531844
  have htrace : WordTrace (prefixWord ++ tailWord_5531844) baseStart_5531844 baseEnd_5531844 := by
    simpa [prefixWord, tailWord_5531844, baseEnd_5531844] using wordTrace_append hprefix tailTrace_5531844
  have hstable : (prefixWord ++ tailWord_5531844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531844).length < 2 ^ (prefixWord ++ tailWord_5531844).sum := by decide
  have hdescent : baseEnd_5531844 < baseStart_5531844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531873 : List Nat := [1, 2, 3, 1, 3, 1, 5, 7]
def baseStart_5531873 : Nat := 118140960795 + 5531873 * 2 ^ 59
def prefixEnd_5531873 : Nat := 4983230072969 + 3 ^ 40 * 5531873 * 2
def baseEnd_5531873 : Nat := 105204065504790379820255

theorem tailTrace_5531873 : CollatzResearch.WordTrace tailWord_5531873 prefixEnd_5531873 105204065504790379820255 := by
  unfold tailWord_5531873
  simp only [CollatzResearch.WordTrace]
  refine ⟨201763983887976364536632273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134509322591984243024421515 201763983887976364536632273)
  ·
    refine ⟨151322987915982273402474205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201763983887976364536632273 151322987915982273402474205)
    ·
      refine ⟨56746120468493352525927827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151322987915982273402474205 56746120468493352525927827)
      ·
        refine ⟨85119180702740028788891741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56746120468493352525927827 85119180702740028788891741)
        ·
          refine ⟨31919692763527510795834403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85119180702740028788891741 31919692763527510795834403)
          ·
            refine ⟨47879539145291266193751605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31919692763527510795834403 47879539145291266193751605)
            ·
              refine ⟨4488706794871056205664213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47879539145291266193751605 4488706794871056205664213)
              ·
                refine ⟨105204065504790379820255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4488706794871056205664213 105204065504790379820255)
                ·
                  rfl

theorem cell23_5531873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 7].length) (baseStart_5531873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531873 prefixEnd_5531873 := by exact prefixLift 5531873
  have htrace : WordTrace (prefixWord ++ tailWord_5531873) baseStart_5531873 baseEnd_5531873 := by
    simpa [prefixWord, tailWord_5531873, baseEnd_5531873] using wordTrace_append hprefix tailTrace_5531873
  have hstable : (prefixWord ++ tailWord_5531873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531873).length < 2 ^ (prefixWord ++ tailWord_5531873).sum := by decide
  have hdescent : baseEnd_5531873 < baseStart_5531873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531883 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 3]
def baseStart_5531883 : Nat := 118140960795 + 5531883 * 2 ^ 59
def prefixEnd_5531883 : Nat := 4983230072969 + 3 ^ 40 * 5531883 * 2
def baseEnd_5531883 : Nat := 2840514903435885216021839

theorem tailTrace_5531883 : CollatzResearch.WordTrace tailWord_5531883 prefixEnd_5531883 2840514903435885216021839 := by
  unfold tailWord_5531883
  simp only [CollatzResearch.WordTrace]
  refine ⟨201764348617940136244496303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134509565745293424162997535 201764348617940136244496303)
  ·
    refine ⟨302646522926910204366744455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201764348617940136244496303 302646522926910204366744455)
    ·
      refine ⟨453969784390365306550116683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302646522926910204366744455 453969784390365306550116683)
      ·
        refine ⟨680954676585547959825175025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453969784390365306550116683 680954676585547959825175025)
        ·
          refine ⟨510716007439160969868881269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680954676585547959825175025 510716007439160969868881269)
          ·
            refine ⟨47879625697421340925207619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 510716007439160969868881269 47879625697421340925207619)
            ·
              refine ⟨71819438546132011387811429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47879625697421340925207619 71819438546132011387811429)
              ·
                refine ⟨13466144727399752135214643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71819438546132011387811429 13466144727399752135214643)
                ·
                  refine ⟨20199217091099628202821965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13466144727399752135214643 20199217091099628202821965)
                  ·
                    refine ⟨7574706409162360576058237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20199217091099628202821965 7574706409162360576058237)
                    ·
                      refine ⟨2840514903435885216021839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7574706409162360576058237 2840514903435885216021839)
                      ·
                        rfl

theorem cell23_5531883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 3].length) (baseStart_5531883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531883 prefixEnd_5531883 := by exact prefixLift 5531883
  have htrace : WordTrace (prefixWord ++ tailWord_5531883) baseStart_5531883 baseEnd_5531883 := by
    simpa [prefixWord, tailWord_5531883, baseEnd_5531883] using wordTrace_append hprefix tailTrace_5531883
  have hstable : (prefixWord ++ tailWord_5531883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531883).length < 2 ^ (prefixWord ++ tailWord_5531883).sum := by decide
  have hdescent : baseEnd_5531883 < baseStart_5531883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531884 : List Nat := [2, 2, 1, 1, 2, 3, 4, 3, 1, 2, 2]
def baseStart_5531884 : Nat := 118140960795 + 5531884 * 2 ^ 59
def prefixEnd_5531884 : Nat := 4983230072969 + 3 ^ 40 * 5531884 * 2
def baseEnd_5531884 : Nat := 2840515416916539712109335

theorem tailTrace_5531884 : CollatzResearch.WordTrace tailWord_5531884 prefixEnd_5531884 2840515416916539712109335 := by
  unfold tailWord_5531884
  simp only [CollatzResearch.WordTrace]
  refine ⟨100882192545468256707641353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134509590060624342276855137 100882192545468256707641353)
  ·
    refine ⟨75661644409101192530731015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100882192545468256707641353 75661644409101192530731015)
    ·
      refine ⟨113492466613651788796096523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75661644409101192530731015 113492466613651788796096523)
      ·
        refine ⟨170238699920477683194144785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113492466613651788796096523 170238699920477683194144785)
        ·
          refine ⟨127679024940358262395608589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170238699920477683194144785 127679024940358262395608589)
          ·
            refine ⟨47879634352634348398353221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127679024940358262395608589 47879634352634348398353221)
            ·
              refine ⟨8977431441118940324691229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47879634352634348398353221 8977431441118940324691229)
              ·
                refine ⟨3366536790419602621759211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8977431441118940324691229 3366536790419602621759211)
                ·
                  refine ⟨5049805185629403932638817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366536790419602621759211 5049805185629403932638817)
                  ·
                    refine ⟨3787353889222052949479113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5049805185629403932638817 3787353889222052949479113)
                    ·
                      refine ⟨2840515416916539712109335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787353889222052949479113 2840515416916539712109335)
                      ·
                        rfl

theorem cell23_5531884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 1, 2, 2].length) (baseStart_5531884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531884 prefixEnd_5531884 := by exact prefixLift 5531884
  have htrace : WordTrace (prefixWord ++ tailWord_5531884) baseStart_5531884 baseEnd_5531884 := by
    simpa [prefixWord, tailWord_5531884, baseEnd_5531884] using wordTrace_append hprefix tailTrace_5531884
  have hstable : (prefixWord ++ tailWord_5531884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531884).length < 2 ^ (prefixWord ++ tailWord_5531884).sum := by decide
  have hdescent : baseEnd_5531884 < baseStart_5531884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531887 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 1, 2, 3]
def baseStart_5531887 : Nat := 118140960795 + 5531887 * 2 ^ 59
def prefixEnd_5531887 : Nat := 4983230072969 + 3 ^ 40 * 5531887 * 2
def baseEnd_5531887 : Nat := 2840516957358503200371821

theorem tailTrace_5531887 : CollatzResearch.WordTrace tailWord_5531887 prefixEnd_5531887 2840516957358503200371821 := by
  unfold tailWord_5531887
  simp only [CollatzResearch.WordTrace]
  refine ⟨201764494509925644927641915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134509663006617096618427943 201764494509925644927641915)
  ·
    refine ⟨302646741764888467391462873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201764494509925644927641915 302646741764888467391462873)
    ·
      refine ⟨226985056323666350543597155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302646741764888467391462873 226985056323666350543597155)
      ·
        refine ⟨340477584485499525815395733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226985056323666350543597155 340477584485499525815395733)
        ·
          refine ⟨15959886772757790272596675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 340477584485499525815395733 15959886772757790272596675)
          ·
            refine ⟨23939830159136685408895013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15959886772757790272596675 23939830159136685408895013)
            ·
              refine ⟨4488718154838128514167815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23939830159136685408895013 4488718154838128514167815)
              ·
                refine ⟨6733077232257192771251723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4488718154838128514167815 6733077232257192771251723)
                ·
                  refine ⟨10099615848385789156877585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6733077232257192771251723 10099615848385789156877585)
                  ·
                    refine ⟨7574711886289341867658189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10099615848385789156877585 7574711886289341867658189)
                    ·
                      refine ⟨2840516957358503200371821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7574711886289341867658189 2840516957358503200371821)
                      ·
                        rfl

theorem cell23_5531887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 2, 3].length) (baseStart_5531887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531887 prefixEnd_5531887 := by exact prefixLift 5531887
  have htrace : WordTrace (prefixWord ++ tailWord_5531887) baseStart_5531887 baseEnd_5531887 := by
    simpa [prefixWord, tailWord_5531887, baseEnd_5531887] using wordTrace_append hprefix tailTrace_5531887
  have hstable : (prefixWord ++ tailWord_5531887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531887).length < 2 ^ (prefixWord ++ tailWord_5531887).sum := by decide
  have hdescent : baseEnd_5531887 < baseStart_5531887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531927 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 1, 3, 2]
def baseStart_5531927 : Nat := 118140960795 + 5531927 * 2 ^ 59
def prefixEnd_5531927 : Nat := 4983230072969 + 3 ^ 40 * 5531927 * 2
def baseEnd_5531927 : Nat := 2840537496584683043871637

theorem tailTrace_5531927 : CollatzResearch.WordTrace tailWord_5531927 prefixEnd_5531927 2840537496584683043871637 := by
  unfold tailWord_5531927
  simp only [CollatzResearch.WordTrace]
  refine ⟨201765953429780731759098035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134510635619853821172732023 201765953429780731759098035)
  ·
    refine ⟨302648930144671097638647053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201765953429780731759098035 302648930144671097638647053)
    ·
      refine ⟨113493348804251661614492645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302648930144671097638647053 113493348804251661614492645)
      ·
        refine ⟨21280002900797186552717371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113493348804251661614492645 21280002900797186552717371)
        ·
          refine ⟨31920004351195779829076057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21280002900797186552717371 31920004351195779829076057)
          ·
            refine ⟨23940003263396834871807043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31920004351195779829076057 23940003263396834871807043)
            ·
              refine ⟨35910004895095252307710565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23940003263396834871807043 35910004895095252307710565)
              ·
                refine ⟨6733125917830359807695731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35910004895095252307710565 6733125917830359807695731)
                ·
                  refine ⟨10099688876745539711543597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6733125917830359807695731 10099688876745539711543597)
                  ·
                    refine ⟨3787383328779577391828849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10099688876745539711543597 3787383328779577391828849)
                    ·
                      refine ⟨2840537496584683043871637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787383328779577391828849 2840537496584683043871637)
                      ·
                        rfl

theorem cell23_5531927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_5531927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531927 prefixEnd_5531927 := by exact prefixLift 5531927
  have htrace : WordTrace (prefixWord ++ tailWord_5531927) baseStart_5531927 baseEnd_5531927 := by
    simpa [prefixWord, tailWord_5531927, baseEnd_5531927] using wordTrace_append hprefix tailTrace_5531927
  have hstable : (prefixWord ++ tailWord_5531927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531927).length < 2 ^ (prefixWord ++ tailWord_5531927).sum := by decide
  have hdescent : baseEnd_5531927 < baseStart_5531927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531934 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_5531934 : Nat := 118140960795 + 5531934 * 2 ^ 59
def prefixEnd_5531934 : Nat := 4983230072969 + 3 ^ 40 * 5531934 * 2
def baseEnd_5531934 : Nat := 2840541090949264516484105

theorem tailTrace_5531934 : CollatzResearch.WordTrace tailWord_5531934 prefixEnd_5531934 2840541090949264516484105 := by
  unfold tailWord_5531934
  simp only [CollatzResearch.WordTrace]
  refine ⟨25220776092594421494325357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134510805827170247969735237 25220776092594421494325357)
  ·
    refine ⟨9457791034722908060372009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25220776092594421494325357 9457791034722908060372009)
    ·
      refine ⟨7093343276042181045279007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9457791034722908060372009 7093343276042181045279007)
      ·
        refine ⟨10640014914063271567918511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7093343276042181045279007 10640014914063271567918511)
        ·
          refine ⟨15960022371094907351877767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10640014914063271567918511 15960022371094907351877767)
          ·
            refine ⟨23940033556642361027816651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15960022371094907351877767 23940033556642361027816651)
            ·
              refine ⟨35910050334963541541724977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23940033556642361027816651 35910050334963541541724977)
              ·
                refine ⟨26932537751222656156293733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35910050334963541541724977 26932537751222656156293733)
                ·
                  refine ⟨5049850828354248029305075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26932537751222656156293733 5049850828354248029305075)
                  ·
                    refine ⟨7574776242531372043957613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5049850828354248029305075 7574776242531372043957613)
                    ·
                      refine ⟨2840541090949264516484105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7574776242531372043957613 2840541090949264516484105)
                      ·
                        rfl

theorem cell23_5531934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_5531934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531934 prefixEnd_5531934 := by exact prefixLift 5531934
  have htrace : WordTrace (prefixWord ++ tailWord_5531934) baseStart_5531934 baseEnd_5531934 := by
    simpa [prefixWord, tailWord_5531934, baseEnd_5531934] using wordTrace_append hprefix tailTrace_5531934
  have hstable : (prefixWord ++ tailWord_5531934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531934).length < 2 ^ (prefixWord ++ tailWord_5531934).sum := by decide
  have hdescent : baseEnd_5531934 < baseStart_5531934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5531957 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_5531957 : Nat := 118140960795 + 5531957 * 2 ^ 59
def prefixEnd_5531957 : Nat := 4983230072969 + 3 ^ 40 * 5531957 * 2
def baseEnd_5531957 : Nat := 2840552901004317926496499

theorem tailTrace_5531957 : CollatzResearch.WordTrace tailWord_5531957 prefixEnd_5531957 2840552901004317926496499 := by
  unfold tailWord_5531957
  simp only [CollatzResearch.WordTrace]
  refine ⟨201767047619672046882690125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134511365079781364588460083 201767047619672046882690125)
  ·
    refine ⟨75662642857377017581008797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201767047619672046882690125 75662642857377017581008797)
    ·
      refine ⟨28373491071516381592878299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75662642857377017581008797 28373491071516381592878299)
      ·
        refine ⟨42560236607274572389317449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28373491071516381592878299 42560236607274572389317449)
        ·
          refine ⟨31920177455455929291988087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42560236607274572389317449 31920177455455929291988087)
          ·
            refine ⟨47880266183183893937982131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31920177455455929291988087 47880266183183893937982131)
            ·
              refine ⟨71820399274775840906973197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47880266183183893937982131 71820399274775840906973197)
              ·
                refine ⟨26932649728040940340114949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71820399274775840906973197 26932649728040940340114949)
                ·
                  refine ⟨5049871824007676313771553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26932649728040940340114949 5049871824007676313771553)
                  ·
                    refine ⟨3787403868005757235328665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5049871824007676313771553 3787403868005757235328665)
                    ·
                      refine ⟨2840552901004317926496499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787403868005757235328665 2840552901004317926496499)
                      ·
                        rfl

theorem cell23_5531957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_5531957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5531957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5531957 prefixEnd_5531957 := by exact prefixLift 5531957
  have htrace : WordTrace (prefixWord ++ tailWord_5531957) baseStart_5531957 baseEnd_5531957 := by
    simpa [prefixWord, tailWord_5531957, baseEnd_5531957] using wordTrace_append hprefix tailTrace_5531957
  have hstable : (prefixWord ++ tailWord_5531957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5531957).length < 2 ^ (prefixWord ++ tailWord_5531957).sum := by decide
  have hdescent : baseEnd_5531957 < baseStart_5531957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5531957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532003 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 5]
def baseStart_5532003 : Nat := 118140960795 + 5532003 * 2 ^ 59
def prefixEnd_5532003 : Nat := 4983230072969 + 3 ^ 40 * 5532003 * 2
def baseEnd_5532003 : Nat := 2840576521114424746521287

theorem tailTrace_5532003 : CollatzResearch.WordTrace tailWord_5532003 prefixEnd_5532003 2840576521114424746521287 := by
  unfold tailWord_5532003
  simp only [CollatzResearch.WordTrace]
  refine ⟨201768725377505396738864663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134512483585003597825909775 201768725377505396738864663)
  ·
    refine ⟨302653088066258095108296995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201768725377505396738864663 302653088066258095108296995)
    ·
      refine ⟨453979632099387142662445493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302653088066258095108296995 453979632099387142662445493)
      ·
        refine ⟨42560590509317544624604265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 453979632099387142662445493 42560590509317544624604265)
        ·
          refine ⟨31920442881988158468453199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42560590509317544624604265 31920442881988158468453199)
          ·
            refine ⟨47880664322982237702679799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31920442881988158468453199 47880664322982237702679799)
            ·
              refine ⟨71820996484473356554019699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47880664322982237702679799 71820996484473356554019699)
              ·
                refine ⟨107731494726710034831029549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71820996484473356554019699 107731494726710034831029549)
                ·
                  refine ⟨40399310522516263061636081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107731494726710034831029549 40399310522516263061636081)
                  ·
                    refine ⟨30299482891887197296227061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40399310522516263061636081 30299482891887197296227061)
                    ·
                      refine ⟨2840576521114424746521287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30299482891887197296227061 2840576521114424746521287)
                      ·
                        rfl

theorem cell23_5532003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_5532003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532003 prefixEnd_5532003 := by exact prefixLift 5532003
  have htrace : WordTrace (prefixWord ++ tailWord_5532003) baseStart_5532003 baseEnd_5532003 := by
    simpa [prefixWord, tailWord_5532003, baseEnd_5532003] using wordTrace_append hprefix tailTrace_5532003
  have hstable : (prefixWord ++ tailWord_5532003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532003).length < 2 ^ (prefixWord ++ tailWord_5532003).sum := by decide
  have hdescent : baseEnd_5532003 < baseStart_5532003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532053 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 8]
def baseStart_5532053 : Nat := 118140960795 + 5532053 * 2 ^ 59
def prefixEnd_5532053 : Nat := 4983230072969 + 3 ^ 40 * 5532053 * 2
def baseEnd_5532053 : Nat := 315622466127461061210673

theorem tailTrace_5532053 : CollatzResearch.WordTrace tailWord_5532053 prefixEnd_5532053 315622466127461061210673 := by
  unfold tailWord_5532053
  simp only [CollatzResearch.WordTrace]
  refine ⟨201770549027324255278184813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134513699351549503518789875 201770549027324255278184813)
  ·
    refine ⟨75663955885246595729319305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201770549027324255278184813 75663955885246595729319305)
    ·
      refine ⟨56747966913934946796989479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75663955885246595729319305 56747966913934946796989479)
      ·
        refine ⟨85121950370902420195484219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56747966913934946796989479 85121950370902420195484219)
        ·
          refine ⟨127682925556353630293226329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85121950370902420195484219 127682925556353630293226329)
          ·
            refine ⟨95762194167265222719919747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127682925556353630293226329 95762194167265222719919747)
            ·
              refine ⟨143643291250897834079879621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95762194167265222719919747 143643291250897834079879621)
              ·
                refine ⟨26933117109543343889977429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143643291250897834079879621 26933117109543343889977429)
                ·
                  refine ⟨315622466127461061210673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26933117109543343889977429 315622466127461061210673)
                  ·
                    rfl

theorem cell23_5532053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_5532053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532053 prefixEnd_5532053 := by exact prefixLift 5532053
  have htrace : WordTrace (prefixWord ++ tailWord_5532053) baseStart_5532053 baseEnd_5532053 := by
    simpa [prefixWord, tailWord_5532053, baseEnd_5532053] using wordTrace_append hprefix tailTrace_5532053
  have hstable : (prefixWord ++ tailWord_5532053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532053).length < 2 ^ (prefixWord ++ tailWord_5532053).sum := by decide
  have hdescent : baseEnd_5532053 < baseStart_5532053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532087 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 6]
def baseStart_5532087 : Nat := 118140960795 + 5532087 * 2 ^ 59
def prefixEnd_5532087 : Nat := 4983230072969 + 3 ^ 40 * 5532087 * 2
def baseEnd_5532087 : Nat := 315624405943266935318989

theorem tailTrace_5532087 : CollatzResearch.WordTrace tailWord_5532087 prefixEnd_5532087 315624405943266935318989 := by
  unfold tailWord_5532087
  simp only [CollatzResearch.WordTrace]
  refine ⟨201771789109201079084922515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134514526072800719389948343 201771789109201079084922515)
  ·
    refine ⟨302657683663801618627383773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201771789109201079084922515 302657683663801618627383773)
    ·
      refine ⟨113496631373925606985268915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302657683663801618627383773 113496631373925606985268915)
      ·
        refine ⟨170244947060888410477903373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113496631373925606985268915 170244947060888410477903373)
        ·
          refine ⟨63841855147833153929213765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170244947060888410477903373 63841855147833153929213765)
          ·
            refine ⟨11970347840218716361727581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63841855147833153929213765 11970347840218716361727581)
            ·
              refine ⟨4488880440082018635647843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11970347840218716361727581 4488880440082018635647843)
              ·
                refine ⟨6733320660123027953471765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4488880440082018635647843 6733320660123027953471765)
                ·
                  refine ⟨315624405943266935318989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6733320660123027953471765 315624405943266935318989)
                  ·
                    rfl

theorem cell23_5532087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 6].length) (baseStart_5532087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532087 prefixEnd_5532087 := by exact prefixLift 5532087
  have htrace : WordTrace (prefixWord ++ tailWord_5532087) baseStart_5532087 baseEnd_5532087 := by
    simpa [prefixWord, tailWord_5532087, baseEnd_5532087] using wordTrace_append hprefix tailTrace_5532087
  have hstable : (prefixWord ++ tailWord_5532087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532087).length < 2 ^ (prefixWord ++ tailWord_5532087).sum := by decide
  have hdescent : baseEnd_5532087 < baseStart_5532087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532107 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 2, 3, 2]
def baseStart_5532107 : Nat := 118140960795 + 5532107 * 2 ^ 59
def prefixEnd_5532107 : Nat := 4983230072969 + 3 ^ 40 * 5532107 * 2
def baseEnd_5532107 : Nat := 2840629923102492339620809

theorem tailTrace_5532107 : CollatzResearch.WordTrace tailWord_5532107 prefixEnd_5532107 2840629923102492339620809 := by
  unfold tailWord_5532107
  simp only [CollatzResearch.WordTrace]
  refine ⟨201772518569128622500650575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134515012379419081667100383 201772518569128622500650575)
  ·
    refine ⟨302658777853692933750975863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201772518569128622500650575 302658777853692933750975863)
    ·
      refine ⟨453988166780539400626463795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302658777853692933750975863 453988166780539400626463795)
      ·
        refine ⟨680982250170809100939695693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453988166780539400626463795 680982250170809100939695693)
        ·
          refine ⟨255368343814053412852385885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 680982250170809100939695693 255368343814053412852385885)
          ·
            refine ⟨95763128930270029819644707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255368343814053412852385885 95763128930270029819644707)
            ·
              refine ⟨143644693395405044729467061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95763128930270029819644707 143644693395405044729467061)
              ·
                refine ⟨13466690005819222943387537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143644693395405044729467061 13466690005819222943387537)
                ·
                  refine ⟨10100017504364417207540653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13466690005819222943387537 10100017504364417207540653)
                  ·
                    refine ⟨3787506564136656452827745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10100017504364417207540653 3787506564136656452827745)
                    ·
                      refine ⟨2840629923102492339620809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787506564136656452827745 2840629923102492339620809)
                      ·
                        rfl

theorem cell23_5532107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 3, 2].length) (baseStart_5532107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532107 prefixEnd_5532107 := by exact prefixLift 5532107
  have htrace : WordTrace (prefixWord ++ tailWord_5532107) baseStart_5532107 baseEnd_5532107 := by
    simpa [prefixWord, tailWord_5532107, baseEnd_5532107] using wordTrace_append hprefix tailTrace_5532107
  have hstable : (prefixWord ++ tailWord_5532107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532107).length < 2 ^ (prefixWord ++ tailWord_5532107).sum := by decide
  have hdescent : baseEnd_5532107 < baseStart_5532107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532108 : List Nat := [2, 2, 1, 4, 4, 1, 1, 3, 1, 4]
def baseStart_5532108 : Nat := 118140960795 + 5532108 * 2 ^ 59
def prefixEnd_5532108 : Nat := 4983230072969 + 3 ^ 40 * 5532108 * 2
def baseEnd_5532108 : Nat := 946876812194382278569435

theorem tailTrace_5532108 : CollatzResearch.WordTrace tailWord_5532108 prefixEnd_5532108 946876812194382278569435 := by
  unfold tailWord_5532108
  simp only [CollatzResearch.WordTrace]
  refine ⟨100886277521062499835718489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134515036694749999780957985 100886277521062499835718489)
  ·
    refine ⟨75664708140796874876788867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100886277521062499835718489 75664708140796874876788867)
    ·
      refine ⟨113497062211195312315183301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75664708140796874876788867 113497062211195312315183301)
      ·
        refine ⟨21280699164599121059096869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113497062211195312315183301 21280699164599121059096869)
        ·
          refine ⟨3990131093362335198580663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21280699164599121059096869 3990131093362335198580663)
          ·
            refine ⟨5985196640043502797870995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990131093362335198580663 5985196640043502797870995)
            ·
              refine ⟨8977794960065254196806493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5985196640043502797870995 8977794960065254196806493)
              ·
                refine ⟨3366673110024470323802435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8977794960065254196806493 3366673110024470323802435)
                ·
                  refine ⟨5050009665036705485703653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366673110024470323802435 5050009665036705485703653)
                  ·
                    refine ⟨946876812194382278569435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5050009665036705485703653 946876812194382278569435)
                    ·
                      rfl

theorem cell23_5532108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_5532108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532108 prefixEnd_5532108 := by exact prefixLift 5532108
  have htrace : WordTrace (prefixWord ++ tailWord_5532108) baseStart_5532108 baseEnd_5532108 := by
    simpa [prefixWord, tailWord_5532108, baseEnd_5532108] using wordTrace_append hprefix tailTrace_5532108
  have hstable : (prefixWord ++ tailWord_5532108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532108).length < 2 ^ (prefixWord ++ tailWord_5532108).sum := by decide
  have hdescent : baseEnd_5532108 < baseStart_5532108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532117 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 1, 5]
def baseStart_5532117 : Nat := 118140960795 + 5532117 * 2 ^ 59
def prefixEnd_5532117 : Nat := 4983230072969 + 3 ^ 40 * 5532117 * 2
def baseEnd_5532117 : Nat := 946878352636345766831921

theorem tailTrace_5532117 : CollatzResearch.WordTrace tailWord_5532117 prefixEnd_5532117 946878352636345766831921 := by
  unfold tailWord_5532117
  simp only [CollatzResearch.WordTrace]
  refine ⟨201772883299092394208514605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134515255532728262805676403 201772883299092394208514605)
  ·
    refine ⟨75664831237159647828192977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201772883299092394208514605 75664831237159647828192977)
    ·
      refine ⟨56748623427869735871144733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75664831237159647828192977 56748623427869735871144733)
      ·
        refine ⟨21280733785451150951679275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56748623427869735871144733 21280733785451150951679275)
        ·
          refine ⟨31921100678176726427518913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21280733785451150951679275 31921100678176726427518913)
          ·
            refine ⟨23940825508632544820639185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31921100678176726427518913 23940825508632544820639185)
            ·
              refine ⟨17955619131474408615479389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23940825508632544820639185 17955619131474408615479389)
              ·
                refine ⟨6733357174302903230804771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17955619131474408615479389 6733357174302903230804771)
                ·
                  refine ⟨10100035761454354846207157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6733357174302903230804771 10100035761454354846207157)
                  ·
                    refine ⟨946878352636345766831921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10100035761454354846207157 946878352636345766831921)
                    ·
                      rfl

theorem cell23_5532117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_5532117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532117 prefixEnd_5532117 := by exact prefixLift 5532117
  have htrace : WordTrace (prefixWord ++ tailWord_5532117) baseStart_5532117 baseEnd_5532117 := by
    simpa [prefixWord, tailWord_5532117, baseEnd_5532117] using wordTrace_append hprefix tailTrace_5532117
  have hstable : (prefixWord ++ tailWord_5532117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532117).length < 2 ^ (prefixWord ++ tailWord_5532117).sum := by decide
  have hdescent : baseEnd_5532117 < baseStart_5532117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532120 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_5532120 : Nat := 118140960795 + 5532120 * 2 ^ 59
def prefixEnd_5532120 : Nat := 4983230072969 + 3 ^ 40 * 5532120 * 2
def baseEnd_5532120 : Nat := 2840636598351000788758249

theorem tailTrace_5532120 : CollatzResearch.WordTrace tailWord_5532120 prefixEnd_5532120 2840636598351000788758249 := by
  unfold tailWord_5532120
  simp only [CollatzResearch.WordTrace]
  refine ⟨100886496359040762860436907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134515328478721017147249209 100886496359040762860436907)
  ·
    refine ⟨151329744538561144290655361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100886496359040762860436907 151329744538561144290655361)
    ·
      refine ⟨113497308403920858217991521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151329744538561144290655361 113497308403920858217991521)
      ·
        refine ⟨85122981302940643663493641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113497308403920858217991521 85122981302940643663493641)
        ·
          refine ⟨63842235977205482747620231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85122981302940643663493641 63842235977205482747620231)
          ·
            refine ⟨95763353965808224121430347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63842235977205482747620231 95763353965808224121430347)
            ·
              refine ⟨143645030948712336182145521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95763353965808224121430347 143645030948712336182145521)
              ·
                refine ⟨107733773211534252136609141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143645030948712336182145521 107733773211534252136609141)
                ·
                  refine ⟨10100041238581336137807107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107733773211534252136609141 10100041238581336137807107)
                  ·
                    refine ⟨15150061857872004206710661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10100041238581336137807107 15150061857872004206710661)
                    ·
                      refine ⟨2840636598351000788758249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15150061857872004206710661 2840636598351000788758249)
                      ·
                        rfl

theorem cell23_5532120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_5532120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532120 prefixEnd_5532120 := by exact prefixLift 5532120
  have htrace : WordTrace (prefixWord ++ tailWord_5532120) baseStart_5532120 baseEnd_5532120 := by
    simpa [prefixWord, tailWord_5532120, baseEnd_5532120] using wordTrace_append hprefix tailTrace_5532120
  have hstable : (prefixWord ++ tailWord_5532120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532120).length < 2 ^ (prefixWord ++ tailWord_5532120).sum := by decide
  have hdescent : baseEnd_5532120 < baseStart_5532120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532131 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 3, 1, 3]
def baseStart_5532131 : Nat := 118140960795 + 5532131 * 2 ^ 59
def prefixEnd_5532131 : Nat := 4983230072969 + 3 ^ 40 * 5532131 * 2
def baseEnd_5532131 : Nat := 2840642246638200245720699

theorem tailTrace_5532131 : CollatzResearch.WordTrace tailWord_5532131 prefixEnd_5532131 2840642246638200245720699 := by
  unfold tailWord_5532131
  simp only [CollatzResearch.WordTrace]
  refine ⟨201773393921041674599524247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134515595947361116399682831 201773393921041674599524247)
  ·
    refine ⟨302660090881562511899286371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201773393921041674599524247 302660090881562511899286371)
    ·
      refine ⟨453990136322343767848929557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302660090881562511899286371 453990136322343767848929557)
      ·
        refine ⟨21280787640109864117918573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 453990136322343767848929557 21280787640109864117918573)
        ·
          refine ⟨7980295365041199044219465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21280787640109864117918573 7980295365041199044219465)
          ·
            refine ⟨5985221523780899283164599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7980295365041199044219465 5985221523780899283164599)
            ·
              refine ⟨8977832285671348924746899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5985221523780899283164599 8977832285671348924746899)
              ·
                refine ⟨13466748428507023387120349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8977832285671348924746899 13466748428507023387120349)
                ·
                  refine ⟨5050030660690133770170131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13466748428507023387120349 5050030660690133770170131)
                  ·
                    refine ⟨7575045991035200655255197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5050030660690133770170131 7575045991035200655255197)
                    ·
                      refine ⟨2840642246638200245720699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7575045991035200655255197 2840642246638200245720699)
                      ·
                        rfl

theorem cell23_5532131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_5532131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532131 prefixEnd_5532131 := by exact prefixLift 5532131
  have htrace : WordTrace (prefixWord ++ tailWord_5532131) baseStart_5532131 baseEnd_5532131 := by
    simpa [prefixWord, tailWord_5532131, baseEnd_5532131] using wordTrace_append hprefix tailTrace_5532131
  have hstable : (prefixWord ++ tailWord_5532131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532131).length < 2 ^ (prefixWord ++ tailWord_5532131).sum := by decide
  have hdescent : baseEnd_5532131 < baseStart_5532131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532140 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_5532140 : Nat := 118140960795 + 5532140 * 2 ^ 59
def prefixEnd_5532140 : Nat := 4983230072969 + 3 ^ 40 * 5532140 * 2
def baseEnd_5532140 : Nat := 2840646867964090710508157

theorem tailTrace_5532140 : CollatzResearch.WordTrace tailWord_5532140 prefixEnd_5532140 2840646867964090710508157 := by
  unfold tailWord_5532140
  simp only [CollatzResearch.WordTrace]
  refine ⟨100886861089004534568300937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134515814785339379424401249 100886861089004534568300937)
  ·
    refine ⟨75665145816753400926225703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100886861089004534568300937 75665145816753400926225703)
    ·
      refine ⟨113497718725130101389338555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75665145816753400926225703 113497718725130101389338555)
      ·
        refine ⟨170246578087695152084007833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113497718725130101389338555 170246578087695152084007833)
        ·
          refine ⟨127684933565771364063005875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170246578087695152084007833 127684933565771364063005875)
          ·
            refine ⟨191527400348657046094508813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127684933565771364063005875 191527400348657046094508813)
            ·
              refine ⟨71822775130746392285440805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191527400348657046094508813 71822775130746392285440805)
              ·
                refine ⟨13466770337014948553520151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71822775130746392285440805 13466770337014948553520151)
                ·
                  refine ⟨20200155505522422830280227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13466770337014948553520151 20200155505522422830280227)
                  ·
                    refine ⟨30300233258283634245420341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20200155505522422830280227 30300233258283634245420341)
                    ·
                      refine ⟨2840646867964090710508157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30300233258283634245420341 2840646867964090710508157)
                      ·
                        rfl

theorem cell23_5532140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_5532140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532140 prefixEnd_5532140 := by exact prefixLift 5532140
  have htrace : WordTrace (prefixWord ++ tailWord_5532140) baseStart_5532140 baseEnd_5532140 := by
    simpa [prefixWord, tailWord_5532140, baseEnd_5532140] using wordTrace_append hprefix tailTrace_5532140
  have hstable : (prefixWord ++ tailWord_5532140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532140).length < 2 ^ (prefixWord ++ tailWord_5532140).sum := by decide
  have hdescent : baseEnd_5532140 < baseStart_5532140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532147 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 2, 4]
def baseStart_5532147 : Nat := 118140960795 + 5532147 * 2 ^ 59
def prefixEnd_5532147 : Nat := 4983230072969 + 3 ^ 40 * 5532147 * 2
def baseEnd_5532147 : Nat := 946883487442890727706875

theorem tailTrace_5532147 : CollatzResearch.WordTrace tailWord_5532147 prefixEnd_5532147 946883487442890727706875 := by
  unfold tailWord_5532147
  simp only [CollatzResearch.WordTrace]
  refine ⟨201773977488983709332106695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134515984992655806221404463 201773977488983709332106695)
  ·
    refine ⟨302660966233475563998160043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201773977488983709332106695 302660966233475563998160043)
    ·
      refine ⟨453991449350213345997240065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302660966233475563998160043 453991449350213345997240065)
      ·
        refine ⟨340493587012660009497930049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453991449350213345997240065 340493587012660009497930049)
        ·
          refine ⟨255370190259495007123447537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340493587012660009497930049 255370190259495007123447537)
          ·
            refine ⟨191527642694621255342585653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255370190259495007123447537 191527642694621255342585653)
            ·
              refine ⟨17955716502620742688367405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191527642694621255342585653 17955716502620742688367405)
              ·
                refine ⟨6733393688482778508137777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17955716502620742688367405 6733393688482778508137777)
                ·
                  refine ⟨5050045266362083881103333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6733393688482778508137777 5050045266362083881103333)
                  ·
                    refine ⟨946883487442890727706875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5050045266362083881103333 946883487442890727706875)
                    ·
                      rfl

theorem cell23_5532147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 4].length) (baseStart_5532147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532147 prefixEnd_5532147 := by exact prefixLift 5532147
  have htrace : WordTrace (prefixWord ++ tailWord_5532147) baseStart_5532147 baseEnd_5532147 := by
    simpa [prefixWord, tailWord_5532147, baseEnd_5532147] using wordTrace_append hprefix tailTrace_5532147
  have hstable : (prefixWord ++ tailWord_5532147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532147).length < 2 ^ (prefixWord ++ tailWord_5532147).sum := by decide
  have hdescent : baseEnd_5532147 < baseStart_5532147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532157 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_5532157 : Nat := 118140960795 + 5532157 * 2 ^ 59
def prefixEnd_5532157 : Nat := 4983230072969 + 3 ^ 40 * 5532157 * 2
def baseEnd_5532157 : Nat := 2840655597135217143995579

theorem tailTrace_5532157 : CollatzResearch.WordTrace tailWord_5532157 prefixEnd_5532157 2840655597135217143995579 := by
  unfold tailWord_5532157
  simp only [CollatzResearch.WordTrace]
  refine ⟨201774342218947481039970725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134516228145964987359980483 201774342218947481039970725)
  ·
    refine ⟨37832689166052652694994511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201774342218947481039970725 37832689166052652694994511)
    ·
      refine ⟨56749033749078979042491767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37832689166052652694994511 56749033749078979042491767)
      ·
        refine ⟨85123550623618468563737651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56749033749078979042491767 85123550623618468563737651)
        ·
          refine ⟨127685325935427702845606477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85123550623618468563737651 127685325935427702845606477)
          ·
            refine ⟨47881997225785388567102429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127685325935427702845606477 47881997225785388567102429)
            ·
              refine ⟨17955748959669520712663411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47881997225785388567102429 17955748959669520712663411)
              ·
                refine ⟨26933623439504281068995117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17955748959669520712663411 26933623439504281068995117)
                ·
                  refine ⟨10100108789814105400873169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26933623439504281068995117 10100108789814105400873169)
                  ·
                    refine ⟨7575081592360579050654877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10100108789814105400873169 7575081592360579050654877)
                    ·
                      refine ⟨2840655597135217143995579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7575081592360579050654877 2840655597135217143995579)
                      ·
                        rfl

theorem cell23_5532157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_5532157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532157 prefixEnd_5532157 := by exact prefixLift 5532157
  have htrace : WordTrace (prefixWord ++ tailWord_5532157) baseStart_5532157 baseEnd_5532157 := by
    simpa [prefixWord, tailWord_5532157, baseEnd_5532157] using wordTrace_append hprefix tailTrace_5532157
  have hstable : (prefixWord ++ tailWord_5532157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532157).length < 2 ^ (prefixWord ++ tailWord_5532157).sum := by decide
  have hdescent : baseEnd_5532157 < baseStart_5532157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532174 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_5532174 : Nat := 118140960795 + 5532174 * 2 ^ 59
def prefixEnd_5532174 : Nat := 4983230072969 + 3 ^ 40 * 5532174 * 2
def baseEnd_5532174 : Nat := 2840664326306343577483001

theorem tailTrace_5532174 : CollatzResearch.WordTrace tailWord_5532174 prefixEnd_5532174 2840664326306343577483001 := by
  unfold tailWord_5532174
  simp only [CollatzResearch.WordTrace]
  refine ⟨25221870282485736617917447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134516641506590595295559717 25221870282485736617917447)
  ·
    refine ⟨37832805423728604926876171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25221870282485736617917447 37832805423728604926876171)
    ·
      refine ⟨56749208135592907390314257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37832805423728604926876171 56749208135592907390314257)
      ·
        refine ⟨42561906101694680542735693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56749208135592907390314257 42561906101694680542735693)
        ·
          refine ⟨15960714788135505203525885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42561906101694680542735693 15960714788135505203525885)
          ·
            refine ⟨5985268045550814451322207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15960714788135505203525885 5985268045550814451322207)
            ·
              refine ⟨8977902068326221676983311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5985268045550814451322207 8977902068326221676983311)
              ·
                refine ⟨13466853102489332515474967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8977902068326221676983311 13466853102489332515474967)
                ·
                  refine ⟨20200279653733998773212451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13466853102489332515474967 20200279653733998773212451)
                  ·
                    refine ⟨30300419480600998159818677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20200279653733998773212451 30300419480600998159818677)
                    ·
                      refine ⟨2840664326306343577483001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30300419480600998159818677 2840664326306343577483001)
                      ·
                        rfl

theorem cell23_5532174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_5532174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532174 prefixEnd_5532174 := by exact prefixLift 5532174
  have htrace : WordTrace (prefixWord ++ tailWord_5532174) baseStart_5532174 baseEnd_5532174 := by
    simpa [prefixWord, tailWord_5532174, baseEnd_5532174] using wordTrace_append hprefix tailTrace_5532174
  have hstable : (prefixWord ++ tailWord_5532174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532174).length < 2 ^ (prefixWord ++ tailWord_5532174).sum := by decide
  have hdescent : baseEnd_5532174 < baseStart_5532174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532188 : List Nat := [2, 2, 3, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_5532188 : Nat := 118140960795 + 5532188 * 2 ^ 59
def prefixEnd_5532188 : Nat := 4983230072969 + 3 ^ 40 * 5532188 * 2
def baseEnd_5532188 : Nat := 2840671515035506522707937

theorem tailTrace_5532188 : CollatzResearch.WordTrace tailWord_5532188 prefixEnd_5532188 2840671515035506522707937 := by
  unfold tailWord_5532188
  simp only [CollatzResearch.WordTrace]
  refine ⟨100887736440917586667174609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134516981921223448889566145 100887736440917586667174609)
  ·
    refine ⟨75665802330688190000380957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100887736440917586667174609 75665802330688190000380957)
    ·
      refine ⟨28374675874008071250142859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75665802330688190000380957 28374675874008071250142859)
      ·
        refine ⟨42562013811012106875214289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28374675874008071250142859 42562013811012106875214289)
        ·
          refine ⟨31921510358259080156410717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42562013811012106875214289 31921510358259080156410717)
          ·
            refine ⟨11970566384347155058654019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31921510358259080156410717 11970566384347155058654019)
            ·
              refine ⟨17955849576520732587981029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11970566384347155058654019 17955849576520732587981029)
              ·
                refine ⟨3366721795597637360246443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17955849576520732587981029 3366721795597637360246443)
                ·
                  refine ⟨5050082693396456040369665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366721795597637360246443 5050082693396456040369665)
                  ·
                    refine ⟨3787562020047342030277249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5050082693396456040369665 3787562020047342030277249)
                    ·
                      refine ⟨2840671515035506522707937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787562020047342030277249 2840671515035506522707937)
                      ·
                        rfl

theorem cell23_5532188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_5532188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532188 prefixEnd_5532188 := by exact prefixLift 5532188
  have htrace : WordTrace (prefixWord ++ tailWord_5532188) baseStart_5532188 baseEnd_5532188 := by
    simpa [prefixWord, tailWord_5532188, baseEnd_5532188] using wordTrace_append hprefix tailTrace_5532188
  have hstable : (prefixWord ++ tailWord_5532188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532188).length < 2 ^ (prefixWord ++ tailWord_5532188).sum := by decide
  have hdescent : baseEnd_5532188 < baseStart_5532188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532222 : List Nat := [4, 2, 1, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_5532222 : Nat := 118140960795 + 5532222 * 2 ^ 59
def prefixEnd_5532222 : Nat := 4983230072969 + 3 ^ 40 * 5532222 * 2
def baseEnd_5532222 : Nat := 2840688973377759389682781

theorem tailTrace_5532222 : CollatzResearch.WordTrace tailWord_5532222 prefixEnd_5532222 2840688973377759389682781 := by
  unfold tailWord_5532222
  simp only [CollatzResearch.WordTrace]
  refine ⟨25222089120463999642635865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134517808642474664760724613 25222089120463999642635865)
  ·
    refine ⟨18916566840347999731976899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25222089120463999642635865 18916566840347999731976899)
    ·
      refine ⟨28374850260521999597965349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18916566840347999731976899 28374850260521999597965349)
      ·
        refine ⟨5320284423847874924618503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28374850260521999597965349 5320284423847874924618503)
        ·
          refine ⟨7980426635771812386927755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320284423847874924618503 7980426635771812386927755)
          ·
            refine ⟨11970639953657718580391633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7980426635771812386927755 11970639953657718580391633)
            ·
              refine ⟨8977979965243288935293725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11970639953657718580391633 8977979965243288935293725)
              ·
                refine ⟨3366742486966233350735147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8977979965243288935293725 3366742486966233350735147)
                ·
                  refine ⟨5050113730449350026102721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366742486966233350735147 5050113730449350026102721)
                  ·
                    refine ⟨3787585297837012519577041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5050113730449350026102721 3787585297837012519577041)
                    ·
                      refine ⟨2840688973377759389682781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787585297837012519577041 2840688973377759389682781)
                      ·
                        rfl

theorem cell23_5532222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_5532222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532222 prefixEnd_5532222 := by exact prefixLift 5532222
  have htrace : WordTrace (prefixWord ++ tailWord_5532222) baseStart_5532222 baseEnd_5532222 := by
    simpa [prefixWord, tailWord_5532222, baseEnd_5532222] using wordTrace_append hprefix tailTrace_5532222
  have hstable : (prefixWord ++ tailWord_5532222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532222).length < 2 ^ (prefixWord ++ tailWord_5532222).sum := by decide
  have hdescent : baseEnd_5532222 < baseStart_5532222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532231 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 1, 3, 2]
def baseStart_5532231 : Nat := 118140960795 + 5532231 * 2 ^ 59
def prefixEnd_5532231 : Nat := 4983230072969 + 3 ^ 40 * 5532231 * 2
def baseEnd_5532231 : Nat := 2840693594703649854470239

theorem tailTrace_5532231 : CollatzResearch.WordTrace tailWord_5532231 prefixEnd_5532231 2840693594703649854470239 := by
  unfold tailWord_5532231
  simp only [CollatzResearch.WordTrace]
  refine ⟨201777041220679391678164547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134518027480452927785443031 201777041220679391678164547)
  ·
    refine ⟨302665561831019087517246821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201777041220679391678164547 302665561831019087517246821)
    ·
      refine ⟨56749792843316078909483779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302665561831019087517246821 56749792843316078909483779)
      ·
        refine ⟨85124689264974118364225669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56749792843316078909483779 85124689264974118364225669)
        ·
          refine ⟨15960879237182647193292313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85124689264974118364225669 15960879237182647193292313)
          ·
            refine ⟨11970659427886985394969235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15960879237182647193292313 11970659427886985394969235)
            ·
              refine ⟨17955989141830478092453853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11970659427886985394969235 17955989141830478092453853)
              ·
                refine ⟨6733495928186429284670195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17955989141830478092453853 6733495928186429284670195)
                ·
                  refine ⟨10100243892279643927005293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6733495928186429284670195 10100243892279643927005293)
                  ·
                    refine ⟨3787591459604866472626985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10100243892279643927005293 3787591459604866472626985)
                    ·
                      refine ⟨2840693594703649854470239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787591459604866472626985 2840693594703649854470239)
                      ·
                        rfl

theorem cell23_5532231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_5532231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532231 prefixEnd_5532231 := by exact prefixLift 5532231
  have htrace : WordTrace (prefixWord ++ tailWord_5532231) baseStart_5532231 baseEnd_5532231 := by
    simpa [prefixWord, tailWord_5532231, baseEnd_5532231] using wordTrace_append hprefix tailTrace_5532231
  have hstable : (prefixWord ++ tailWord_5532231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532231).length < 2 ^ (prefixWord ++ tailWord_5532231).sum := by decide
  have hdescent : baseEnd_5532231 < baseStart_5532231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532257 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_5532257 : Nat := 118140960795 + 5532257 * 2 ^ 59
def prefixEnd_5532257 : Nat := 4983230072969 + 3 ^ 40 * 5532257 * 2
def baseEnd_5532257 : Nat := 2840706945200666752745119

theorem tailTrace_5532257 : CollatzResearch.WordTrace tailWord_5532257 prefixEnd_5532257 2840706945200666752745119 := by
  unfold tailWord_5532257
  simp only [CollatzResearch.WordTrace]
  refine ⟨201777989518585198118611025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134518659679056798745740683 201777989518585198118611025)
  ·
    refine ⟨151333492138938898588958269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201777989518585198118611025 151333492138938898588958269)
    ·
      refine ⟨56750059552102086970859351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151333492138938898588958269 56750059552102086970859351)
      ·
        refine ⟨85125089328153130456289027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56750059552102086970859351 85125089328153130456289027)
        ·
          refine ⟨127687633992229695684433541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85125089328153130456289027 127687633992229695684433541)
          ·
            refine ⟨23941431373543067940831289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127687633992229695684433541 23941431373543067940831289)
            ·
              refine ⟨17956073530157300955623467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23941431373543067940831289 17956073530157300955623467)
              ·
                refine ⟨26934110295235951433435201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17956073530157300955623467 26934110295235951433435201)
                ·
                  refine ⟨20200582721426963575076401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26934110295235951433435201 20200582721426963575076401)
                  ·
                    refine ⟨15150437041070222681307301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20200582721426963575076401 15150437041070222681307301)
                    ·
                      refine ⟨2840706945200666752745119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15150437041070222681307301 2840706945200666752745119)
                      ·
                        rfl

theorem cell23_5532257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_5532257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532257 prefixEnd_5532257 := by exact prefixLift 5532257
  have htrace : WordTrace (prefixWord ++ tailWord_5532257) baseStart_5532257 baseEnd_5532257 := by
    simpa [prefixWord, tailWord_5532257, baseEnd_5532257] using wordTrace_append hprefix tailTrace_5532257
  have hstable : (prefixWord ++ tailWord_5532257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532257).length < 2 ^ (prefixWord ++ tailWord_5532257).sum := by decide
  have hdescent : baseEnd_5532257 < baseStart_5532257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532284 : List Nat := [2, 2, 2, 1, 1, 2, 5, 3, 5]
def baseStart_5532284 : Nat := 118140960795 + 5532284 * 2 ^ 59
def prefixEnd_5532284 : Nat := 4983230072969 + 3 ^ 40 * 5532284 * 2
def baseEnd_5532284 : Nat := 315635645464259794123055

theorem tailTrace_5532284 : CollatzResearch.WordTrace tailWord_5532284 prefixEnd_5532284 315635645464259794123055 := by
  unfold tailWord_5532284
  simp only [CollatzResearch.WordTrace]
  refine ⟨100889487144743690864921953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134519316192991587819895937 100889487144743690864921953)
  ·
    refine ⟨75667115358557768148691465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100889487144743690864921953 75667115358557768148691465)
    ·
      refine ⟨56750336518918326111518599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75667115358557768148691465 56750336518918326111518599)
      ·
        refine ⟨85125504778377489167277899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56750336518918326111518599 85125504778377489167277899)
        ·
          refine ⟨127688257167566233750916849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85125504778377489167277899 127688257167566233750916849)
          ·
            refine ⟨95766192875674675313187637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127688257167566233750916849 95766192875674675313187637)
            ·
              refine ⟨8978080582094500810611341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95766192875674675313187637 8978080582094500810611341)
              ·
                refine ⟨3366780218285437803979253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8978080582094500810611341 3366780218285437803979253)
                ·
                  refine ⟨315635645464259794123055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3366780218285437803979253 315635645464259794123055)
                  ·
                    rfl

theorem cell23_5532284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_5532284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532284 prefixEnd_5532284 := by exact prefixLift 5532284
  have htrace : WordTrace (prefixWord ++ tailWord_5532284) baseStart_5532284 baseEnd_5532284 := by
    simpa [prefixWord, tailWord_5532284, baseEnd_5532284] using wordTrace_append hprefix tailTrace_5532284
  have hstable : (prefixWord ++ tailWord_5532284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532284).length < 2 ^ (prefixWord ++ tailWord_5532284).sum := by decide
  have hdescent : baseEnd_5532284 < baseStart_5532284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532317 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_5532317 : Nat := 118140960795 + 5532317 * 2 ^ 59
def prefixEnd_5532317 : Nat := 4983230072969 + 3 ^ 40 * 5532317 * 2
def baseEnd_5532317 : Nat := 2840737754039936517994843

theorem tailTrace_5532317 : CollatzResearch.WordTrace tailWord_5532317 prefixEnd_5532317 2840737754039936517994843 := by
  unfold tailWord_5532317
  simp only [CollatzResearch.WordTrace]
  refine ⟨201780177898367828365795205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134520118598911885577196803 201780177898367828365795205)
  ·
    refine ⟨37833783355943967818586601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201780177898367828365795205 37833783355943967818586601)
    ·
      refine ⟨28375337516957975863939951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37833783355943967818586601 28375337516957975863939951)
      ·
        refine ⟨42563006275436963795909927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28375337516957975863939951 42563006275436963795909927)
        ·
          refine ⟨63844509413155445693864891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42563006275436963795909927 63844509413155445693864891)
          ·
            refine ⟨95766764119733168540797337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63844509413155445693864891 95766764119733168540797337)
            ·
              refine ⟨71825073089799876405598003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95766764119733168540797337 71825073089799876405598003)
              ·
                refine ⟨107737609634699814608397005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71825073089799876405598003 107737609634699814608397005)
                ·
                  refine ⟨40401603613012430478148877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107737609634699814608397005 40401603613012430478148877)
                  ·
                    refine ⟨15150601354879661429305829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40401603613012430478148877 15150601354879661429305829)
                    ·
                      refine ⟨2840737754039936517994843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15150601354879661429305829 2840737754039936517994843)
                      ·
                        rfl

theorem cell23_5532317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_5532317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532317 prefixEnd_5532317 := by exact prefixLift 5532317
  have htrace : WordTrace (prefixWord ++ tailWord_5532317) baseStart_5532317 baseEnd_5532317 := by
    simpa [prefixWord, tailWord_5532317, baseEnd_5532317] using wordTrace_append hprefix tailTrace_5532317
  have hstable : (prefixWord ++ tailWord_5532317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532317).length < 2 ^ (prefixWord ++ tailWord_5532317).sum := by decide
  have hdescent : baseEnd_5532317 < baseStart_5532317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532367 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 3]
def baseStart_5532367 : Nat := 118140960795 + 5532367 * 2 ^ 59
def prefixEnd_5532367 : Nat := 4983230072969 + 3 ^ 40 * 5532367 * 2
def baseEnd_5532367 : Nat := 2840763428072661322369613

theorem tailTrace_5532367 : CollatzResearch.WordTrace tailWord_5532367 prefixEnd_5532367 2840763428072661322369613 := by
  unfold tailWord_5532367
  simp only [CollatzResearch.WordTrace]
  refine ⟨201782001548186686905115355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134521334365457791270076903 201782001548186686905115355)
  ·
    refine ⟨302673002322280030357673033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201782001548186686905115355 302673002322280030357673033)
    ·
      refine ⟨227004751741710022768254775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302673002322280030357673033 227004751741710022768254775)
      ·
        refine ⟨340507127612565034152382163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227004751741710022768254775 340507127612565034152382163)
        ·
          refine ⟨510760691418847551228573245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340507127612565034152382163 510760691418847551228573245)
          ·
            refine ⟨191535259282067831710714967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 510760691418847551228573245 191535259282067831710714967)
            ·
              refine ⟨287302888923101747566072451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191535259282067831710714967 287302888923101747566072451)
              ·
                refine ⟨430954333384652621349108677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287302888923101747566072451 430954333384652621349108677)
                ·
                  refine ⟨80803937509622366502957877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430954333384652621349108677 80803937509622366502957877)
                  ·
                    refine ⟨7575369141527096859652301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80803937509622366502957877 7575369141527096859652301)
                    ·
                      refine ⟨2840763428072661322369613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7575369141527096859652301 2840763428072661322369613)
                      ·
                        rfl

theorem cell23_5532367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 3].length) (baseStart_5532367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532367 prefixEnd_5532367 := by exact prefixLift 5532367
  have htrace : WordTrace (prefixWord ++ tailWord_5532367) baseStart_5532367 baseEnd_5532367 := by
    simpa [prefixWord, tailWord_5532367, baseEnd_5532367] using wordTrace_append hprefix tailTrace_5532367
  have hstable : (prefixWord ++ tailWord_5532367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532367).length < 2 ^ (prefixWord ++ tailWord_5532367).sum := by decide
  have hdescent : baseEnd_5532367 < baseStart_5532367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532418 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_5532418 : Nat := 118140960795 + 5532418 * 2 ^ 59
def prefixEnd_5532418 : Nat := 4983230072969 + 3 ^ 40 * 5532418 * 2
def baseEnd_5532418 : Nat := 2840789615586040622831879

theorem tailTrace_5532418 : CollatzResearch.WordTrace tailWord_5532418 prefixEnd_5532418 2840789615586040622831879 := by
  unfold tailWord_5532418
  simp only [CollatzResearch.WordTrace]
  refine ⟨50445965417750480653805477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134522574447334615076814605 50445965417750480653805477)
  ·
    refine ⟨9458618515828215122588527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50445965417750480653805477 9458618515828215122588527)
    ·
      refine ⟨14187927773742322683882791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9458618515828215122588527 14187927773742322683882791)
      ·
        refine ⟨21281891660613484025824187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14187927773742322683882791 21281891660613484025824187)
        ·
          refine ⟨31922837490920226038736281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21281891660613484025824187 31922837490920226038736281)
          ·
            refine ⟨23942128118190169529052211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31922837490920226038736281 23942128118190169529052211)
            ·
              refine ⟨35913192177285254293578317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23942128118190169529052211 35913192177285254293578317)
              ·
                refine ⟨13467447066481970360091869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35913192177285254293578317 13467447066481970360091869)
                ·
                  refine ⟨5050292649930738885034451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13467447066481970360091869 5050292649930738885034451)
                  ·
                    refine ⟨7575438974896108327551677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5050292649930738885034451 7575438974896108327551677)
                    ·
                      refine ⟨2840789615586040622831879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7575438974896108327551677 2840789615586040622831879)
                      ·
                        rfl

theorem cell23_5532418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_5532418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532418 prefixEnd_5532418 := by exact prefixLift 5532418
  have htrace : WordTrace (prefixWord ++ tailWord_5532418) baseStart_5532418 baseEnd_5532418 := by
    simpa [prefixWord, tailWord_5532418, baseEnd_5532418] using wordTrace_append hprefix tailTrace_5532418
  have hstable : (prefixWord ++ tailWord_5532418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532418).length < 2 ^ (prefixWord ++ tailWord_5532418).sum := by decide
  have hdescent : baseEnd_5532418 < baseStart_5532418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532441 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 5, 2, 2]
def baseStart_5532441 : Nat := 118140960795 + 5532441 * 2 ^ 59
def prefixEnd_5532441 : Nat := 4983230072969 + 3 ^ 40 * 5532441 * 2
def baseEnd_5532441 : Nat := 2840801425641094032844273

theorem tailTrace_5532441 : CollatzResearch.WordTrace tailWord_5532441 prefixEnd_5532441 2840801425641094032844273 := by
  unfold tailWord_5532441
  simp only [CollatzResearch.WordTrace]
  refine ⟨201784700549918597543309177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134523133699945731695539451 201784700549918597543309177)
  ·
    refine ⟨151338525412438948157481883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201784700549918597543309177 151338525412438948157481883)
    ·
      refine ⟨227007788118658422236222825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151338525412438948157481883 227007788118658422236222825)
      ·
        refine ⟨170255841088993816677167119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227007788118658422236222825 170255841088993816677167119)
        ·
          refine ⟨255383761633490725015750679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170255841088993816677167119 255383761633490725015750679)
          ·
            refine ⟨383075642450236087523626019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255383761633490725015750679 383075642450236087523626019)
            ·
              refine ⟨574613463675354131285439029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383075642450236087523626019 574613463675354131285439029)
              ·
                refine ⟨53870012219564449808009909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 574613463675354131285439029 53870012219564449808009909)
                ·
                  refine ⟨5050313645584167169500929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53870012219564449808009909 5050313645584167169500929)
                  ·
                    refine ⟨3787735234188125377125697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5050313645584167169500929 3787735234188125377125697)
                    ·
                      refine ⟨2840801425641094032844273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787735234188125377125697 2840801425641094032844273)
                      ·
                        rfl

theorem cell23_5532441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 2, 2].length) (baseStart_5532441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532441 prefixEnd_5532441 := by exact prefixLift 5532441
  have htrace : WordTrace (prefixWord ++ tailWord_5532441) baseStart_5532441 baseEnd_5532441 := by
    simpa [prefixWord, tailWord_5532441, baseEnd_5532441] using wordTrace_append hprefix tailTrace_5532441
  have hstable : (prefixWord ++ tailWord_5532441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532441).length < 2 ^ (prefixWord ++ tailWord_5532441).sum := by decide
  have hdescent : baseEnd_5532441 < baseStart_5532441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532452 : List Nat := [2, 3, 1, 3, 3, 2, 1, 3, 1, 1, 3]
def baseStart_5532452 : Nat := 118140960795 + 5532452 * 2 ^ 59
def prefixEnd_5532452 : Nat := 4983230072969 + 3 ^ 40 * 5532452 * 2
def baseEnd_5532452 : Nat := 2840807073928293489806723

theorem tailTrace_5532452 : CollatzResearch.WordTrace tailWord_5532452 prefixEnd_5532452 2840807073928293489806723 := by
  unfold tailWord_5532452
  simp only [CollatzResearch.WordTrace]
  refine ⟨100892550876439373210979805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134523401168585830947973073 100892550876439373210979805)
  ·
    refine ⟨37834706578664764954117427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100892550876439373210979805 37834706578664764954117427)
    ·
      refine ⟨56752059867997147431176141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37834706578664764954117427 56752059867997147431176141)
      ·
        refine ⟨21282022450498930286691053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56752059867997147431176141 21282022450498930286691053)
        ·
          refine ⟨7980758418937098857509145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21282022450498930286691053 7980758418937098857509145)
          ·
            refine ⟨5985568814202824143131859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7980758418937098857509145 5985568814202824143131859)
            ·
              refine ⟨8978353221304236214697789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5985568814202824143131859 8978353221304236214697789)
              ·
                refine ⟨3366882457989088580511671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8978353221304236214697789 3366882457989088580511671)
                ·
                  refine ⟨5050323686983632870767507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366882457989088580511671 5050323686983632870767507)
                  ·
                    refine ⟨7575485530475449306151261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5050323686983632870767507 7575485530475449306151261)
                    ·
                      refine ⟨2840807073928293489806723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7575485530475449306151261 2840807073928293489806723)
                      ·
                        rfl

theorem cell23_5532452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_5532452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532452 prefixEnd_5532452 := by exact prefixLift 5532452
  have htrace : WordTrace (prefixWord ++ tailWord_5532452) baseStart_5532452 baseEnd_5532452 := by
    simpa [prefixWord, tailWord_5532452, baseEnd_5532452] using wordTrace_append hprefix tailTrace_5532452
  have hstable : (prefixWord ++ tailWord_5532452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532452).length < 2 ^ (prefixWord ++ tailWord_5532452).sum := by decide
  have hdescent : baseEnd_5532452 < baseStart_5532452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532508 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_5532508 : Nat := 118140960795 + 5532508 * 2 ^ 59
def prefixEnd_5532508 : Nat := 4983230072969 + 3 ^ 40 * 5532508 * 2
def baseEnd_5532508 : Nat := 2840835828844945270706465

theorem tailTrace_5532508 : CollatzResearch.WordTrace tailWord_5532508 prefixEnd_5532508 2840835828844945270706465 := by
  unfold tailWord_5532508
  simp only [CollatzResearch.WordTrace]
  refine ⟨100893572120337933992999089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134524762827117245323998785 100893572120337933992999089)
  ·
    refine ⟨75670179090253450494749317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100893572120337933992999089 75670179090253450494749317)
    ·
      refine ⟨14188158579422521967765497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75670179090253450494749317 14188158579422521967765497)
      ·
        refine ⟨10641118934566891475824123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14188158579422521967765497 10641118934566891475824123)
        ·
          refine ⟨15961678401850337213736185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10641118934566891475824123 15961678401850337213736185)
          ·
            refine ⟨11971258801387752910302139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15961678401850337213736185 11971258801387752910302139)
            ·
              refine ⟨17956888202081629365453209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11971258801387752910302139 17956888202081629365453209)
              ·
                refine ⟨13467666151561222024089907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17956888202081629365453209 13467666151561222024089907)
                ·
                  refine ⟨20201499227341833036134861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13467666151561222024089907 20201499227341833036134861)
                  ·
                    refine ⟨7575562210253187388550573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20201499227341833036134861 7575562210253187388550573)
                    ·
                      refine ⟨2840835828844945270706465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7575562210253187388550573 2840835828844945270706465)
                      ·
                        rfl

theorem cell23_5532508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_5532508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532508 prefixEnd_5532508 := by exact prefixLift 5532508
  have htrace : WordTrace (prefixWord ++ tailWord_5532508) baseStart_5532508 baseEnd_5532508 := by
    simpa [prefixWord, tailWord_5532508, baseEnd_5532508] using wordTrace_append hprefix tailTrace_5532508
  have hstable : (prefixWord ++ tailWord_5532508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532508).length < 2 ^ (prefixWord ++ tailWord_5532508).sum := by decide
  have hdescent : baseEnd_5532508 < baseStart_5532508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532524 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_5532524 : Nat := 118140960795 + 5532524 * 2 ^ 59
def prefixEnd_5532524 : Nat := 4983230072969 + 3 ^ 40 * 5532524 * 2
def baseEnd_5532524 : Nat := 946948014845139069368797

theorem tailTrace_5532524 : CollatzResearch.WordTrace tailWord_5532524 prefixEnd_5532524 946948014845139069368797 := by
  unfold tailWord_5532524
  simp only [CollatzResearch.WordTrace]
  refine ⟨100893863904308951359290313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134525151872411935145720417 100893863904308951359290313)
  ·
    refine ⟨75670397928231713519467735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100893863904308951359290313 75670397928231713519467735)
    ·
      refine ⟨113505596892347570279201603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75670397928231713519467735 113505596892347570279201603)
      ·
        refine ⟨170258395338521355418802405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113505596892347570279201603 170258395338521355418802405)
        ·
          refine ⟨31923449125972754141025451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170258395338521355418802405 31923449125972754141025451)
          ·
            refine ⟨47885173688959131211538177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31923449125972754141025451 47885173688959131211538177)
            ·
              refine ⟨35913880266719348408653633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47885173688959131211538177 35913880266719348408653633)
              ·
                refine ⟨26935410200039511306490225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35913880266719348408653633 26935410200039511306490225)
                ·
                  refine ⟨20201557650029633479867669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26935410200039511306490225 20201557650029633479867669)
                  ·
                    refine ⟨946948014845139069368797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20201557650029633479867669 946948014845139069368797)
                    ·
                      rfl

theorem cell23_5532524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_5532524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532524 prefixEnd_5532524 := by exact prefixLift 5532524
  have htrace : WordTrace (prefixWord ++ tailWord_5532524) baseStart_5532524 baseEnd_5532524 := by
    simpa [prefixWord, tailWord_5532524, baseEnd_5532524] using wordTrace_append hprefix tailTrace_5532524
  have hstable : (prefixWord ++ tailWord_5532524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532524).length < 2 ^ (prefixWord ++ tailWord_5532524).sum := by decide
  have hdescent : baseEnd_5532524 < baseStart_5532524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532526 : List Nat := [4, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_5532526 : Nat := 118140960795 + 5532526 * 2 ^ 59
def prefixEnd_5532526 : Nat := 4983230072969 + 3 ^ 40 * 5532526 * 2
def baseEnd_5532526 : Nat := 2840845071496726200281383

theorem tailTrace_5532526 : CollatzResearch.WordTrace tailWord_5532526 prefixEnd_5532526 2840845071496726200281383 := by
  unfold tailWord_5532526
  simp only [CollatzResearch.WordTrace]
  refine ⟨25223475094326332132519179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134525200503073771373435621 25223475094326332132519179)
  ·
    refine ⟨37835212641489498198778769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25223475094326332132519179 37835212641489498198778769)
    ·
      refine ⟨28376409481117123649084077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37835212641489498198778769 28376409481117123649084077)
      ·
        refine ⟨10641153555418921368406529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28376409481117123649084077 10641153555418921368406529)
        ·
          refine ⟨7980865166564191026304897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10641153555418921368406529 7980865166564191026304897)
          ·
            refine ⟨5985648874923143269728673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7980865166564191026304897 5985648874923143269728673)
            ·
              refine ⟨4489236656192357452296505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5985648874923143269728673 4489236656192357452296505)
              ·
                refine ⟨3366927492144268089222379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4489236656192357452296505 3366927492144268089222379)
                ·
                  refine ⟨5050391238216402133833569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366927492144268089222379 5050391238216402133833569)
                  ·
                    refine ⟨3787793428662301600375177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5050391238216402133833569 3787793428662301600375177)
                    ·
                      refine ⟨2840845071496726200281383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787793428662301600375177 2840845071496726200281383)
                      ·
                        rfl

theorem cell23_5532526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_5532526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532526 prefixEnd_5532526 := by exact prefixLift 5532526
  have htrace : WordTrace (prefixWord ++ tailWord_5532526) baseStart_5532526 baseEnd_5532526 := by
    simpa [prefixWord, tailWord_5532526, baseEnd_5532526] using wordTrace_append hprefix tailTrace_5532526
  have hstable : (prefixWord ++ tailWord_5532526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532526).length < 2 ^ (prefixWord ++ tailWord_5532526).sum := by decide
  have hdescent : baseEnd_5532526 < baseStart_5532526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532548 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_5532548 : Nat := 118140960795 + 5532548 * 2 ^ 59
def prefixEnd_5532548 : Nat := 4983230072969 + 3 ^ 40 * 5532548 * 2
def baseEnd_5532548 : Nat := 2840856368071125114206281

theorem tailTrace_5532548 : CollatzResearch.WordTrace tailWord_5532548 prefixEnd_5532548 2840856368071125114206281 := by
  unfold tailWord_5532548
  simp only [CollatzResearch.WordTrace]
  refine ⟨100894301580265477408727149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134525735440353969878302865 100894301580265477408727149)
  ·
    refine ⟨37835363092599554028272681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100894301580265477408727149 37835363092599554028272681)
    ·
      refine ⟨28376522319449665521204511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37835363092599554028272681 28376522319449665521204511)
      ·
        refine ⟨42564783479174498281806767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28376522319449665521204511 42564783479174498281806767)
        ·
          refine ⟨63847175218761747422710151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42564783479174498281806767 63847175218761747422710151)
          ·
            refine ⟨95770762828142621134065227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63847175218761747422710151 95770762828142621134065227)
            ·
              refine ⟨143656144242213931701097841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95770762828142621134065227 143656144242213931701097841)
              ·
                refine ⟨107742108181660448775823381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143656144242213931701097841 107742108181660448775823381)
                ·
                  refine ⟨5050411321015333536366721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107742108181660448775823381 5050411321015333536366721)
                  ·
                    refine ⟨3787808490761500152275041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5050411321015333536366721 3787808490761500152275041)
                    ·
                      refine ⟨2840856368071125114206281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787808490761500152275041 2840856368071125114206281)
                      ·
                        rfl

theorem cell23_5532548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_5532548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532548 prefixEnd_5532548 := by exact prefixLift 5532548
  have htrace : WordTrace (prefixWord ++ tailWord_5532548) baseStart_5532548 baseEnd_5532548 := by
    simpa [prefixWord, tailWord_5532548, baseEnd_5532548] using wordTrace_append hprefix tailTrace_5532548
  have hstable : (prefixWord ++ tailWord_5532548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532548).length < 2 ^ (prefixWord ++ tailWord_5532548).sum := by decide
  have hdescent : baseEnd_5532548 < baseStart_5532548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532591 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 2, 5, 2]
def baseStart_5532591 : Nat := 118140960795 + 5532591 * 2 ^ 59
def prefixEnd_5532591 : Nat := 4983230072969 + 3 ^ 40 * 5532591 * 2
def baseEnd_5532591 : Nat := 2840878447739268445968583

theorem tailTrace_5532591 : CollatzResearch.WordTrace tailWord_5532591 prefixEnd_5532591 2840878447739268445968583 := by
  unfold tailWord_5532591
  simp only [CollatzResearch.WordTrace]
  refine ⟨201790171499375173161269627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134526780999583448774179751 201790171499375173161269627)
  ·
    refine ⟨302685257249062759741904441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201790171499375173161269627 302685257249062759741904441)
    ·
      refine ⟨227013942936797069806428331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302685257249062759741904441 227013942936797069806428331)
      ·
        refine ⟨340520914405195604709642497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227013942936797069806428331 340520914405195604709642497)
        ·
          refine ⟨255390685803896703532231873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340520914405195604709642497 255390685803896703532231873)
          ·
            refine ⟨191543014352922527649173905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255390685803896703532231873 191543014352922527649173905)
            ·
              refine ⟨143657260764691895736880429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191543014352922527649173905 143657260764691895736880429)
              ·
                refine ⟨53871472786759460901330161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143657260764691895736880429 53871472786759460901330161)
                ·
                  refine ⟨40403604590069595675997621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53871472786759460901330161 40403604590069595675997621)
                  ·
                    refine ⟨3787837930319024594624777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40403604590069595675997621 3787837930319024594624777)
                    ·
                      refine ⟨2840878447739268445968583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787837930319024594624777 2840878447739268445968583)
                      ·
                        rfl

theorem cell23_5532591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 5, 2].length) (baseStart_5532591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532591 prefixEnd_5532591 := by exact prefixLift 5532591
  have htrace : WordTrace (prefixWord ++ tailWord_5532591) baseStart_5532591 baseEnd_5532591 := by
    simpa [prefixWord, tailWord_5532591, baseEnd_5532591] using wordTrace_append hprefix tailTrace_5532591
  have hstable : (prefixWord ++ tailWord_5532591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532591).length < 2 ^ (prefixWord ++ tailWord_5532591).sum := by decide
  have hdescent : baseEnd_5532591 < baseStart_5532591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532624 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_5532624 : Nat := 118140960795 + 5532624 * 2 ^ 59
def prefixEnd_5532624 : Nat := 4983230072969 + 3 ^ 40 * 5532624 * 2
def baseEnd_5532624 : Nat := 2840895392600866816855931

theorem tailTrace_5532624 : CollatzResearch.WordTrace tailWord_5532624 prefixEnd_5532624 2840895392600866816855931 := by
  unfold tailWord_5532624
  simp only [CollatzResearch.WordTrace]
  refine ⟨100895687554127809898610463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134527583405503746531480617 100895687554127809898610463)
  ·
    refine ⟨151343531331191714847915695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100895687554127809898610463 151343531331191714847915695)
    ·
      refine ⟨227015296996787572271873543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151343531331191714847915695 227015296996787572271873543)
      ·
        refine ⟨340522945495181358407810315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227015296996787572271873543 340522945495181358407810315)
        ·
          refine ⟨510784418242772037611715473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340522945495181358407810315 510784418242772037611715473)
          ·
            refine ⟨383088313682079028208786605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510784418242772037611715473 383088313682079028208786605)
            ·
              refine ⟨143658117630779635578294977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383088313682079028208786605 143658117630779635578294977)
              ·
                refine ⟨107743588223084726683721233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143658117630779635578294977 107743588223084726683721233)
                ·
                  refine ⟨80807691167313545012790925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107743588223084726683721233 80807691167313545012790925)
                  ·
                    refine ⟨30302884187742579379796597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80807691167313545012790925 30302884187742579379796597)
                    ·
                      refine ⟨2840895392600866816855931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30302884187742579379796597 2840895392600866816855931)
                      ·
                        rfl

theorem cell23_5532624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_5532624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532624 prefixEnd_5532624 := by exact prefixLift 5532624
  have htrace : WordTrace (prefixWord ++ tailWord_5532624) baseStart_5532624 baseEnd_5532624 := by
    simpa [prefixWord, tailWord_5532624, baseEnd_5532624] using wordTrace_append hprefix tailTrace_5532624
  have hstable : (prefixWord ++ tailWord_5532624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532624).length < 2 ^ (prefixWord ++ tailWord_5532624).sum := by decide
  have hdescent : baseEnd_5532624 < baseStart_5532624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532648 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 3, 4]
def baseStart_5532648 : Nat := 118140960795 + 5532648 * 2 ^ 59
def prefixEnd_5532648 : Nat := 4983230072969 + 3 ^ 40 * 5532648 * 2
def baseEnd_5532648 : Nat := 946969238712191574318607

theorem tailTrace_5532648 : CollatzResearch.WordTrace tailWord_5532648 prefixEnd_5532648 946969238712191574318607 := by
  unfold tailWord_5532648
  simp only [CollatzResearch.WordTrace]
  refine ⟨100896125230084335948047299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134528166973445781264063065 100896125230084335948047299)
  ·
    refine ⟨151344187845126503922070949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100896125230084335948047299 151344187845126503922070949)
    ·
      refine ⟨28377035220961219485388303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151344187845126503922070949 28377035220961219485388303)
      ·
        refine ⟨42565552831441829228082455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28377035220961219485388303 42565552831441829228082455)
        ·
          refine ⟨63848329247162743842123683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42565552831441829228082455 63848329247162743842123683)
          ·
            refine ⟨95772493870744115763185525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63848329247162743842123683 95772493870744115763185525)
            ·
              refine ⟨8978671300382260852798643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95772493870744115763185525 8978671300382260852798643)
              ·
                refine ⟨13468006950573391279197965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8978671300382260852798643 13468006950573391279197965)
                ·
                  refine ⟨5050502606465021729699237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13468006950573391279197965 5050502606465021729699237)
                  ·
                    refine ⟨946969238712191574318607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5050502606465021729699237 946969238712191574318607)
                    ·
                      rfl

theorem cell23_5532648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_5532648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532648 prefixEnd_5532648 := by exact prefixLift 5532648
  have htrace : WordTrace (prefixWord ++ tailWord_5532648) baseStart_5532648 baseEnd_5532648 := by
    simpa [prefixWord, tailWord_5532648, baseEnd_5532648] using wordTrace_append hprefix tailTrace_5532648
  have hstable : (prefixWord ++ tailWord_5532648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532648).length < 2 ^ (prefixWord ++ tailWord_5532648).sum := by decide
  have hdescent : baseEnd_5532648 < baseStart_5532648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532708 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_5532708 : Nat := 118140960795 + 5532708 * 2 ^ 59
def prefixEnd_5532708 : Nat := 4983230072969 + 3 ^ 40 * 5532708 * 2
def baseEnd_5532708 : Nat := 946979508325281496068515

theorem tailTrace_5532708 : CollatzResearch.WordTrace tailWord_5532708 prefixEnd_5532708 946979508325281496068515 := by
  unfold tailWord_5532708
  simp only [CollatzResearch.WordTrace]
  refine ⟨100897219419975651071639389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134529625893300868095519185 100897219419975651071639389)
  ·
    refine ⟨37836457282490869151864771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100897219419975651071639389 37836457282490869151864771)
    ·
      refine ⟨56754685923736303727797157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37836457282490869151864771 56754685923736303727797157)
      ·
        refine ⟨10641503610700556948961967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56754685923736303727797157 10641503610700556948961967)
        ·
          refine ⟨15962255416050835423442951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10641503610700556948961967 15962255416050835423442951)
          ·
            refine ⟨23943383124076253135164427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15962255416050835423442951 23943383124076253135164427)
            ·
              refine ⟨35915074686114379702746641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23943383124076253135164427 35915074686114379702746641)
              ·
                refine ⟨26936306014585784777059981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35915074686114379702746641 26936306014585784777059981)
                ·
                  refine ⟨10101114755469669291397493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26936306014585784777059981 10101114755469669291397493)
                  ·
                    refine ⟨946979508325281496068515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10101114755469669291397493 946979508325281496068515)
                    ·
                      rfl

theorem cell23_5532708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_5532708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532708 prefixEnd_5532708 := by exact prefixLift 5532708
  have htrace : WordTrace (prefixWord ++ tailWord_5532708) baseStart_5532708 baseEnd_5532708 := by
    simpa [prefixWord, tailWord_5532708, baseEnd_5532708] using wordTrace_append hprefix tailTrace_5532708
  have hstable : (prefixWord ++ tailWord_5532708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532708).length < 2 ^ (prefixWord ++ tailWord_5532708).sum := by decide
  have hdescent : baseEnd_5532708 < baseStart_5532708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532728 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_5532728 : Nat := 118140960795 + 5532728 * 2 ^ 59
def prefixEnd_5532728 : Nat := 4983230072969 + 3 ^ 40 * 5532728 * 2
def baseEnd_5532728 : Nat := 2840948794588934409955453

theorem tailTrace_5532728 : CollatzResearch.WordTrace tailWord_5532728 prefixEnd_5532728 2840948794588934409955453 := by
  unfold tailWord_5532728
  simp only [CollatzResearch.WordTrace]
  refine ⟨100897584149939422779503419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134530112199919230372671225 100897584149939422779503419)
  ·
    refine ⟨151346376224909134169255129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100897584149939422779503419 151346376224909134169255129)
    ·
      refine ⟨113509782168681850626941347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151346376224909134169255129 113509782168681850626941347)
      ·
        refine ⟨170264673253022775940412021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113509782168681850626941347 170264673253022775940412021)
        ·
          refine ⟨15962313117470885244413627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170264673253022775940412021 15962313117470885244413627)
          ·
            refine ⟨23943469676206327866620441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15962313117470885244413627 23943469676206327866620441)
            ·
              refine ⟨17957602257154745899965331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23943469676206327866620441 17957602257154745899965331)
              ·
                refine ⟨26936403385732118849947997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17957602257154745899965331 26936403385732118849947997)
                ·
                  refine ⟨10101151269649544568730499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26936403385732118849947997 10101151269649544568730499)
                  ·
                    refine ⟨15151726904474316853095749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10101151269649544568730499 15151726904474316853095749)
                    ·
                      refine ⟨2840948794588934409955453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15151726904474316853095749 2840948794588934409955453)
                      ·
                        rfl

theorem cell23_5532728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_5532728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532728 prefixEnd_5532728 := by exact prefixLift 5532728
  have htrace : WordTrace (prefixWord ++ tailWord_5532728) baseStart_5532728 baseEnd_5532728 := by
    simpa [prefixWord, tailWord_5532728, baseEnd_5532728] using wordTrace_append hprefix tailTrace_5532728
  have hstable : (prefixWord ++ tailWord_5532728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532728).length < 2 ^ (prefixWord ++ tailWord_5532728).sum := by decide
  have hdescent : baseEnd_5532728 < baseStart_5532728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532732 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 2, 3, 2]
def baseStart_5532732 : Nat := 118140960795 + 5532732 * 2 ^ 59
def prefixEnd_5532732 : Nat := 4983230072969 + 3 ^ 40 * 5532732 * 2
def baseEnd_5532732 : Nat := 2840950848511552394305435

theorem tailTrace_5532732 : CollatzResearch.WordTrace tailWord_5532732 prefixEnd_5532732 2840950848511552394305435 := by
  unfold tailWord_5532732
  simp only [CollatzResearch.WordTrace]
  refine ⟨100897657095932177121076225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134530209461242902828101633 100897657095932177121076225)
  ·
    refine ⟨75673242821949132840807169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100897657095932177121076225 75673242821949132840807169)
    ·
      refine ⟨56754932116461849630605377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75673242821949132840807169 56754932116461849630605377)
      ·
        refine ⟨42566199087346387222954033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56754932116461849630605377 42566199087346387222954033)
        ·
          refine ⟨31924649315509790417215525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42566199087346387222954033 31924649315509790417215525)
          ·
            refine ⟨5985871746658085703227911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31924649315509790417215525 5985871746658085703227911)
            ·
              refine ⟨8978807619987128554841867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5985871746658085703227911 8978807619987128554841867)
              ·
                refine ⟨13468211429980692832262801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8978807619987128554841867 13468211429980692832262801)
                ·
                  refine ⟨10101158572485519624197101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13468211429980692832262801 10101158572485519624197101)
                  ·
                    refine ⟨3787934464682069859073913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10101158572485519624197101 3787934464682069859073913)
                    ·
                      refine ⟨2840950848511552394305435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3787934464682069859073913 2840950848511552394305435)
                      ·
                        rfl

theorem cell23_5532732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_5532732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532732 prefixEnd_5532732 := by exact prefixLift 5532732
  have htrace : WordTrace (prefixWord ++ tailWord_5532732) baseStart_5532732 baseEnd_5532732 := by
    simpa [prefixWord, tailWord_5532732, baseEnd_5532732] using wordTrace_append hprefix tailTrace_5532732
  have hstable : (prefixWord ++ tailWord_5532732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532732).length < 2 ^ (prefixWord ++ tailWord_5532732).sum := by decide
  have hdescent : baseEnd_5532732 < baseStart_5532732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532742 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_5532742 : Nat := 118140960795 + 5532742 * 2 ^ 59
def prefixEnd_5532742 : Nat := 4983230072969 + 3 ^ 40 * 5532742 * 2
def baseEnd_5532742 : Nat := 946985327772699118393463

theorem tailTrace_5532742 : CollatzResearch.WordTrace tailWord_5532742 prefixEnd_5532742 946985327772699118393463 := by
  unfold tailWord_5532742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6306114966307128935938015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134530452614552083966677653 6306114966307128935938015)
  ·
    refine ⟨9459172449460693403907023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6306114966307128935938015 9459172449460693403907023)
    ·
      refine ⟨14188758674191040105860535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9459172449460693403907023 14188758674191040105860535)
      ·
        refine ⟨21283138011286560158790803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14188758674191040105860535 21283138011286560158790803)
        ·
          refine ⟨31924707016929840238186205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21283138011286560158790803 31924707016929840238186205)
          ·
            refine ⟨11971765131348690089319827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31924707016929840238186205 11971765131348690089319827)
            ·
              refine ⟨17957647697023035133979741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11971765131348690089319827 17957647697023035133979741)
              ·
                refine ⟨6734117886383638175242403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17957647697023035133979741 6734117886383638175242403)
                ·
                  refine ⟨10101176829575457262863605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6734117886383638175242403 10101176829575457262863605)
                  ·
                    refine ⟨946985327772699118393463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10101176829575457262863605 946985327772699118393463)
                    ·
                      rfl

theorem cell23_5532742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_5532742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532742 prefixEnd_5532742 := by exact prefixLift 5532742
  have htrace : WordTrace (prefixWord ++ tailWord_5532742) baseStart_5532742 baseEnd_5532742 := by
    simpa [prefixWord, tailWord_5532742, baseEnd_5532742] using wordTrace_append hprefix tailTrace_5532742
  have hstable : (prefixWord ++ tailWord_5532742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532742).length < 2 ^ (prefixWord ++ tailWord_5532742).sum := by decide
  have hdescent : baseEnd_5532742 < baseStart_5532742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532775 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_5532775 : Nat := 118140960795 + 5532775 * 2 ^ 59
def prefixEnd_5532775 : Nat := 4983230072969 + 3 ^ 40 * 5532775 * 2
def baseEnd_5532775 : Nat := 2840972928179695726067737

theorem tailTrace_5532775 : CollatzResearch.WordTrace tailWord_5532775 prefixEnd_5532775 2840972928179695726067737 := by
  unfold tailWord_5532775
  simp only [CollatzResearch.WordTrace]
  refine ⟨201796882530708572585967779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134531255020472381723978519 201796882530708572585967779)
  ·
    refine ⟨302695323796062858878951669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201796882530708572585967779 302695323796062858878951669)
    ·
      refine ⟨28377686605880893019901719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 302695323796062858878951669 28377686605880893019901719)
      ·
        refine ⟨42566529908821339529852579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28377686605880893019901719 42566529908821339529852579)
        ·
          refine ⟨63849794863232009294778869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42566529908821339529852579 63849794863232009294778869)
          ·
            refine ⟨5985918268428000871385519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63849794863232009294778869 5985918268428000871385519)
            ·
              refine ⟨8978877402642001307078279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5985918268428000871385519 8978877402642001307078279)
              ·
                refine ⟨13468316103963001960617419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8978877402642001307078279 13468316103963001960617419)
                ·
                  refine ⟨20202474155944502940926129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13468316103963001960617419 20202474155944502940926129)
                  ·
                    refine ⟨15151855616958377205694597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20202474155944502940926129 15151855616958377205694597)
                    ·
                      refine ⟨2840972928179695726067737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15151855616958377205694597 2840972928179695726067737)
                      ·
                        rfl

theorem cell23_5532775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_5532775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532775 prefixEnd_5532775 := by exact prefixLift 5532775
  have htrace : WordTrace (prefixWord ++ tailWord_5532775) baseStart_5532775 baseEnd_5532775 := by
    simpa [prefixWord, tailWord_5532775, baseEnd_5532775] using wordTrace_append hprefix tailTrace_5532775
  have hstable : (prefixWord ++ tailWord_5532775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532775).length < 2 ^ (prefixWord ++ tailWord_5532775).sum := by decide
  have hdescent : baseEnd_5532775 < baseStart_5532775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532782 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_5532782 : Nat := 118140960795 + 5532782 * 2 ^ 59
def prefixEnd_5532782 : Nat := 4983230072969 + 3 ^ 40 * 5532782 * 2
def baseEnd_5532782 : Nat := 2840976522544277198680205

theorem tailTrace_5532782 : CollatzResearch.WordTrace tailWord_5532782 prefixEnd_5532782 2840976522544277198680205 := by
  unfold tailWord_5532782
  simp only [CollatzResearch.WordTrace]
  refine ⟨25224642230210401597684075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134531425227788808520981733 25224642230210401597684075)
  ·
    refine ⟨37836963345315602396526113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25224642230210401597684075 37836963345315602396526113)
    ·
      refine ⟨28377722508986701797394585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37836963345315602396526113 28377722508986701797394585)
      ·
        refine ⟨21283291881740026348045939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28377722508986701797394585 21283291881740026348045939)
        ·
          refine ⟨31924937822610039522068909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21283291881740026348045939 31924937822610039522068909)
          ·
            refine ⟨11971851683478764820775841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31924937822610039522068909 11971851683478764820775841)
            ·
              refine ⟨8978888762609073615581881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11971851683478764820775841 8978888762609073615581881)
              ·
                refine ⟨6734166571956805211686411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8978888762609073615581881 6734166571956805211686411)
                ·
                  refine ⟨10101249857935207817529617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6734166571956805211686411 10101249857935207817529617)
                  ·
                    refine ⟨7575937393451405863147213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10101249857935207817529617 7575937393451405863147213)
                    ·
                      refine ⟨2840976522544277198680205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7575937393451405863147213 2840976522544277198680205)
                      ·
                        rfl

theorem cell23_5532782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_5532782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532782 prefixEnd_5532782 := by exact prefixLift 5532782
  have htrace : WordTrace (prefixWord ++ tailWord_5532782) baseStart_5532782 baseEnd_5532782 := by
    simpa [prefixWord, tailWord_5532782, baseEnd_5532782] using wordTrace_append hprefix tailTrace_5532782
  have hstable : (prefixWord ++ tailWord_5532782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532782).length < 2 ^ (prefixWord ++ tailWord_5532782).sum := by decide
  have hdescent : baseEnd_5532782 < baseStart_5532782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532791 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_5532791 : Nat := 118140960795 + 5532791 * 2 ^ 59
def prefixEnd_5532791 : Nat := 4983230072969 + 3 ^ 40 * 5532791 * 2
def baseEnd_5532791 : Nat := 2840981143870167663467663

theorem tailTrace_5532791 : CollatzResearch.WordTrace tailWord_5532791 prefixEnd_5532791 2840981143870167663467663 := by
  unfold tailWord_5532791
  simp only [CollatzResearch.WordTrace]
  refine ⟨201797466098650607318550227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134531644065767071545700151 201797466098650607318550227)
  ·
    refine ⟨302696199147975910977825341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201797466098650607318550227 302696199147975910977825341)
    ·
      refine ⟨113511074680490966616684503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302696199147975910977825341 113511074680490966616684503)
      ·
        refine ⟨170266612020736449925026755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113511074680490966616684503 170266612020736449925026755)
        ·
          refine ⟨255399918031104674887540133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170266612020736449925026755 255399918031104674887540133)
          ·
            refine ⟨47887484630832126541413775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255399918031104674887540133 47887484630832126541413775)
            ·
              refine ⟨71831226946248189812120663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47887484630832126541413775 71831226946248189812120663)
              ·
                refine ⟨107746840419372284718180995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71831226946248189812120663 107746840419372284718180995)
                ·
                  refine ⟨161620260629058427077271493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107746840419372284718180995 161620260629058427077271493)
                  ·
                    refine ⟨30303798867948455076988405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161620260629058427077271493 30303798867948455076988405)
                    ·
                      refine ⟨2840981143870167663467663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30303798867948455076988405 2840981143870167663467663)
                      ·
                        rfl

theorem cell23_5532791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_5532791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532791 prefixEnd_5532791 := by exact prefixLift 5532791
  have htrace : WordTrace (prefixWord ++ tailWord_5532791) baseStart_5532791 baseEnd_5532791 := by
    simpa [prefixWord, tailWord_5532791, baseEnd_5532791] using wordTrace_append hprefix tailTrace_5532791
  have hstable : (prefixWord ++ tailWord_5532791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532791).length < 2 ^ (prefixWord ++ tailWord_5532791).sum := by decide
  have hdescent : baseEnd_5532791 < baseStart_5532791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532811 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 4, 6]
def baseStart_5532811 : Nat := 118140960795 + 5532811 * 2 ^ 59
def prefixEnd_5532811 : Nat := 4983230072969 + 3 ^ 40 * 5532811 * 2
def baseEnd_5532811 : Nat := 946997137827752528405857

theorem tailTrace_5532811 : CollatzResearch.WordTrace tailWord_5532811 prefixEnd_5532811 946997137827752528405857 := by
  unfold tailWord_5532811
  simp only [CollatzResearch.WordTrace]
  refine ⟨201798195558578150734278287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134532130372385433822852191 201798195558578150734278287)
  ·
    refine ⟨302697293337867226101417431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201798195558578150734278287 302697293337867226101417431)
    ·
      refine ⟨454045940006800839152126147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302697293337867226101417431 454045940006800839152126147)
      ·
        refine ⟨681068910010201258728189221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454045940006800839152126147 681068910010201258728189221)
        ·
          refine ⟨127700420626912736011535479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 681068910010201258728189221 127700420626912736011535479)
          ·
            refine ⟨191550630940369104017303219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127700420626912736011535479 191550630940369104017303219)
            ·
              refine ⟨287325946410553656025954829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191550630940369104017303219 287325946410553656025954829)
              ·
                refine ⟨107747229903957621009733061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287325946410553656025954829 107747229903957621009733061)
                ·
                  refine ⟨20202605606992053939324949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107747229903957621009733061 20202605606992053939324949)
                  ·
                    refine ⟨946997137827752528405857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20202605606992053939324949 946997137827752528405857)
                    ·
                      rfl

theorem cell23_5532811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 6].length) (baseStart_5532811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532811 prefixEnd_5532811 := by exact prefixLift 5532811
  have htrace : WordTrace (prefixWord ++ tailWord_5532811) baseStart_5532811 baseEnd_5532811 := by
    simpa [prefixWord, tailWord_5532811, baseEnd_5532811] using wordTrace_append hprefix tailTrace_5532811
  have hstable : (prefixWord ++ tailWord_5532811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532811).length < 2 ^ (prefixWord ++ tailWord_5532811).sum := by decide
  have hdescent : baseEnd_5532811 < baseStart_5532811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532839 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_5532839 : Nat := 118140960795 + 5532839 * 2 ^ 59
def prefixEnd_5532839 : Nat := 4983230072969 + 3 ^ 40 * 5532839 * 2
def baseEnd_5532839 : Nat := 2841005790941583475667443

theorem tailTrace_5532839 : CollatzResearch.WordTrace tailWord_5532839 prefixEnd_5532839 2841005790941583475667443 := by
  unfold tailWord_5532839
  simp only [CollatzResearch.WordTrace]
  refine ⟨201799216802476711516297571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134532811201651141010865047 201799216802476711516297571)
  ·
    refine ⟨302698825203715067274446357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201799216802476711516297571 302698825203715067274446357)
    ·
      refine ⟨14189007431424143778489673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 302698825203715067274446357 14189007431424143778489673)
      ·
        refine ⟨10641755573568107833867255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14189007431424143778489673 10641755573568107833867255)
        ·
          refine ⟨15962633360352161750800883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10641755573568107833867255 15962633360352161750800883)
          ·
            refine ⟨23943950040528242626201325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15962633360352161750800883 23943950040528242626201325)
            ·
              refine ⟨8978981265198090984825497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23943950040528242626201325 8978981265198090984825497)
              ·
                refine ⟨6734235948898568238619123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8978981265198090984825497 6734235948898568238619123)
                ·
                  refine ⟨10101353923347852357928685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6734235948898568238619123 10101353923347852357928685)
                  ·
                    refine ⟨3788007721255444634223257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10101353923347852357928685 3788007721255444634223257)
                    ·
                      refine ⟨2841005790941583475667443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3788007721255444634223257 2841005790941583475667443)
                      ·
                        rfl

theorem cell23_5532839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_5532839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532839 prefixEnd_5532839 := by exact prefixLift 5532839
  have htrace : WordTrace (prefixWord ++ tailWord_5532839) baseStart_5532839 baseEnd_5532839 := by
    simpa [prefixWord, tailWord_5532839, baseEnd_5532839] using wordTrace_append hprefix tailTrace_5532839
  have hstable : (prefixWord ++ tailWord_5532839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532839).length < 2 ^ (prefixWord ++ tailWord_5532839).sum := by decide
  have hdescent : baseEnd_5532839 < baseStart_5532839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532885 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_5532885 : Nat := 118140960795 + 5532885 * 2 ^ 59
def prefixEnd_5532885 : Nat := 4983230072969 + 3 ^ 40 * 5532885 * 2
def baseEnd_5532885 : Nat := 2841029411051690295692231

theorem tailTrace_5532885 : CollatzResearch.WordTrace tailWord_5532885 prefixEnd_5532885 2841029411051690295692231 := by
  unfold tailWord_5532885
  simp only [CollatzResearch.WordTrace]
  refine ⟨201800894560310061372472109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134533929706873374248314739 201800894560310061372472109)
  ·
    refine ⟨75675335460116273014677041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201800894560310061372472109 75675335460116273014677041)
    ·
      refine ⟨56756501595087204761007781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75675335460116273014677041 56756501595087204761007781)
      ·
        refine ⟨10641844049078850892688959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56756501595087204761007781 10641844049078850892688959)
        ·
          refine ⟨15962766073618276339033439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10641844049078850892688959 15962766073618276339033439)
          ·
            refine ⟨23944149110427414508550159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15962766073618276339033439 23944149110427414508550159)
            ·
              refine ⟨35916223665641121762825239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23944149110427414508550159 35916223665641121762825239)
              ·
                refine ⟨53874335498461682644237859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35916223665641121762825239 53874335498461682644237859)
                ·
                  refine ⟨80811503247692523966356789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53874335498461682644237859 80811503247692523966356789)
                  ·
                    refine ⟨7576078429471174121845949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80811503247692523966356789 7576078429471174121845949)
                    ·
                      refine ⟨2841029411051690295692231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7576078429471174121845949 2841029411051690295692231)
                      ·
                        rfl

theorem cell23_5532885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_5532885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532885 prefixEnd_5532885 := by exact prefixLift 5532885
  have htrace : WordTrace (prefixWord ++ tailWord_5532885) baseStart_5532885 baseEnd_5532885 := by
    simpa [prefixWord, tailWord_5532885, baseEnd_5532885] using wordTrace_append hprefix tailTrace_5532885
  have hstable : (prefixWord ++ tailWord_5532885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532885).length < 2 ^ (prefixWord ++ tailWord_5532885).sum := by decide
  have hdescent : baseEnd_5532885 < baseStart_5532885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532886 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_5532886 : Nat := 118140960795 + 5532886 * 2 ^ 59
def prefixEnd_5532886 : Nat := 4983230072969 + 3 ^ 40 * 5532886 * 2
def baseEnd_5532886 : Nat := 2841029924532344791779727

theorem tailTrace_5532886 : CollatzResearch.WordTrace tailWord_5532886 prefixEnd_5532886 2841029924532344791779727 := by
  unfold tailWord_5532886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12612558189581652408953657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134533954022204292362172341 12612558189581652408953657)
  ·
    refine ⟨9459418642186239306715243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12612558189581652408953657 9459418642186239306715243)
    ·
      refine ⟨14189127963279358960072865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9459418642186239306715243 14189127963279358960072865)
      ·
        refine ⟨10641845972459519220054649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14189127963279358960072865 10641845972459519220054649)
        ·
          refine ⟨7981384479344639415040987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10641845972459519220054649 7981384479344639415040987)
          ·
            refine ⟨11972076719016959122561481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7981384479344639415040987 11972076719016959122561481)
            ·
              refine ⟨8979057539262719341921111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11972076719016959122561481 8979057539262719341921111)
              ·
                refine ⟨13468586308894079012881667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8979057539262719341921111 13468586308894079012881667)
                ·
                  refine ⟨20202879463341118519322501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13468586308894079012881667 20202879463341118519322501)
                  ·
                    refine ⟨3788039899376459722372969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20202879463341118519322501 3788039899376459722372969)
                    ·
                      refine ⟨2841029924532344791779727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3788039899376459722372969 2841029924532344791779727)
                      ·
                        rfl

theorem cell23_5532886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_5532886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532886 prefixEnd_5532886 := by exact prefixLift 5532886
  have htrace : WordTrace (prefixWord ++ tailWord_5532886) baseStart_5532886 baseEnd_5532886 := by
    simpa [prefixWord, tailWord_5532886, baseEnd_5532886] using wordTrace_append hprefix tailTrace_5532886
  have hstable : (prefixWord ++ tailWord_5532886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532886).length < 2 ^ (prefixWord ++ tailWord_5532886).sum := by decide
  have hdescent : baseEnd_5532886 < baseStart_5532886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532938 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_5532938 : Nat := 118140960795 + 5532938 * 2 ^ 59
def prefixEnd_5532938 : Nat := 4983230072969 + 3 ^ 40 * 5532938 * 2
def baseEnd_5532938 : Nat := 2841056625526378588329487

theorem tailTrace_5532938 : CollatzResearch.WordTrace tailWord_5532938 prefixEnd_5532938 2841056625526378588329487 := by
  unfold tailWord_5532938
  simp only [CollatzResearch.WordTrace]
  refine ⟨50450706907279512856037867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134535218419412034282767645 50450706907279512856037867)
  ·
    refine ⟨75676060360919269284056801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50450706907279512856037867 75676060360919269284056801)
    ·
      refine ⟨56757045270689451963042601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75676060360919269284056801 56757045270689451963042601)
      ·
        refine ⟨42567783953017088972281951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56757045270689451963042601 42567783953017088972281951)
        ·
          refine ⟨63851675929525633458422927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42567783953017088972281951 63851675929525633458422927)
          ·
            refine ⟨95777513894288450187634391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63851675929525633458422927 95777513894288450187634391)
            ·
              refine ⟨143666270841432675281451587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95777513894288450187634391 143666270841432675281451587)
              ·
                refine ⟨215499406262149012922177381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143666270841432675281451587 215499406262149012922177381)
                ·
                  refine ⟨40406138674152939922908259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215499406262149012922177381 40406138674152939922908259)
                  ·
                    refine ⟨60609208011229409884362389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40406138674152939922908259 60609208011229409884362389)
                    ·
                      refine ⟨2841056625526378588329487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60609208011229409884362389 2841056625526378588329487)
                      ·
                        rfl

theorem cell23_5532938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_5532938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532938 prefixEnd_5532938 := by exact prefixLift 5532938
  have htrace : WordTrace (prefixWord ++ tailWord_5532938) baseStart_5532938 baseEnd_5532938 := by
    simpa [prefixWord, tailWord_5532938, baseEnd_5532938] using wordTrace_append hprefix tailTrace_5532938
  have hstable : (prefixWord ++ tailWord_5532938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532938).length < 2 ^ (prefixWord ++ tailWord_5532938).sum := by decide
  have hdescent : baseEnd_5532938 < baseStart_5532938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5532942 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2]
def baseStart_5532942 : Nat := 118140960795 + 5532942 * 2 ^ 59
def prefixEnd_5532942 : Nat := 4983230072969 + 3 ^ 40 * 5532942 * 2
def baseEnd_5532942 : Nat := 2841058679448996572679469

theorem tailTrace_5532942 : CollatzResearch.WordTrace tailWord_5532942 prefixEnd_5532942 2841058679448996572679469 := by
  unfold tailWord_5532942
  simp only [CollatzResearch.WordTrace]
  refine ⟨25225371690137945013412135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134535315680735706738198053 25225371690137945013412135)
  ·
    refine ⟨37838057535206917520118203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25225371690137945013412135 37838057535206917520118203)
    ·
      refine ⟨56757086302810376280177305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37838057535206917520118203 56757086302810376280177305)
      ·
        refine ⟨42567814727107782210132979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56757086302810376280177305 42567814727107782210132979)
        ·
          refine ⟨63851722090661673315199469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42567814727107782210132979 63851722090661673315199469)
          ·
            refine ⟨23944395783998127493199801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63851722090661673315199469 23944395783998127493199801)
            ·
              refine ⟨17958296837998595619899851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23944395783998127493199801 17958296837998595619899851)
              ·
                refine ⟨26937445256997893429849777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17958296837998595619899851 26937445256997893429849777)
                ·
                  refine ⟨20203083942748420072387333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26937445256997893429849777 20203083942748420072387333)
                  ·
                    refine ⟨3788078239265328763572625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20203083942748420072387333 3788078239265328763572625)
                    ·
                      refine ⟨2841058679448996572679469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3788078239265328763572625 2841058679448996572679469)
                      ·
                        rfl

theorem cell23_5532942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_5532942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5532942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5532942 prefixEnd_5532942 := by exact prefixLift 5532942
  have htrace : WordTrace (prefixWord ++ tailWord_5532942) baseStart_5532942 baseEnd_5532942 := by
    simpa [prefixWord, tailWord_5532942, baseEnd_5532942] using wordTrace_append hprefix tailTrace_5532942
  have hstable : (prefixWord ++ tailWord_5532942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5532942).length < 2 ^ (prefixWord ++ tailWord_5532942).sum := by decide
  have hdescent : baseEnd_5532942 < baseStart_5532942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5532942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533025 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 6, 4]
def baseStart_5533025 : Nat := 118140960795 + 5533025 * 2 ^ 59
def prefixEnd_5533025 : Nat := 4983230072969 + 3 ^ 40 * 5533025 * 2
def baseEnd_5533025 : Nat := 947033766114439915980529

theorem tailTrace_5533025 : CollatzResearch.WordTrace tailWord_5533025 prefixEnd_5533025 947033766114439915980529 := by
  unfold tailWord_5533025
  simp only [CollatzResearch.WordTrace]
  refine ⟨201806000779802865282568529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134537333853201910188379019 201806000779802865282568529)
  ·
    refine ⟨151354500584852148961926397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201806000779802865282568529 151354500584852148961926397)
    ·
      refine ⟨56757937719319555860722399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151354500584852148961926397 56757937719319555860722399)
      ·
        refine ⟨85136906578979333791083599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56757937719319555860722399 85136906578979333791083599)
        ·
          refine ⟨127705359868469000686625399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85136906578979333791083599 127705359868469000686625399)
          ·
            refine ⟨191558039802703501029938099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127705359868469000686625399 191558039802703501029938099)
            ·
              refine ⟨287337059704055251544907149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191558039802703501029938099 287337059704055251544907149)
              ·
                refine ⟨107751397389020719329340181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287337059704055251544907149 107751397389020719329340181)
                ·
                  refine ⟨5050846752610346218562821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107751397389020719329340181 5050846752610346218562821)
                  ·
                    refine ⟨947033766114439915980529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5050846752610346218562821 947033766114439915980529)
                    ·
                      rfl

theorem cell23_5533025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_5533025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533025 prefixEnd_5533025 := by exact prefixLift 5533025
  have htrace : WordTrace (prefixWord ++ tailWord_5533025) baseStart_5533025 baseEnd_5533025 := by
    simpa [prefixWord, tailWord_5533025, baseEnd_5533025] using wordTrace_append hprefix tailTrace_5533025
  have hstable : (prefixWord ++ tailWord_5533025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533025).length < 2 ^ (prefixWord ++ tailWord_5533025).sum := by decide
  have hdescent : baseEnd_5533025 < baseStart_5533025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533026 : List Nat := [3, 3, 2, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_5533026 : Nat := 118140960795 + 5533026 * 2 ^ 59
def prefixEnd_5533026 : Nat := 4983230072969 + 3 ^ 40 * 5533026 * 2
def baseEnd_5533026 : Nat := 2841101811823974244029083

theorem tailTrace_5533026 : CollatzResearch.WordTrace tailWord_5533026 prefixEnd_5533026 2841101811823974244029083 := by
  unfold tailWord_5533026
  simp only [CollatzResearch.WordTrace]
  refine ⟨50451509313199810613338733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134537358168532828302236621 50451509313199810613338733)
  ·
    refine ⟨18919315992449928980002025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50451509313199810613338733 18919315992449928980002025)
    ·
      refine ⟨14189486994337446735001519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18919315992449928980002025 14189486994337446735001519)
      ·
        refine ⟨21284230491506170102502279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14189486994337446735001519 21284230491506170102502279)
        ·
          refine ⟨31926345737259255153753419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21284230491506170102502279 31926345737259255153753419)
          ·
            refine ⟨47889518605888882730630129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31926345737259255153753419 47889518605888882730630129)
            ·
              refine ⟨35917138954416662047972597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47889518605888882730630129 35917138954416662047972597)
              ·
                refine ⟨3367231776976562066997431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35917138954416662047972597 3367231776976562066997431)
                ·
                  refine ⟨5050847665464843100496147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3367231776976562066997431 5050847665464843100496147)
                  ·
                    refine ⟨7576271498197264650744221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5050847665464843100496147 7576271498197264650744221)
                    ·
                      refine ⟨2841101811823974244029083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7576271498197264650744221 2841101811823974244029083)
                      ·
                        rfl

theorem cell23_5533026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_5533026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533026 prefixEnd_5533026 := by exact prefixLift 5533026
  have htrace : WordTrace (prefixWord ++ tailWord_5533026) baseStart_5533026 baseEnd_5533026 := by
    simpa [prefixWord, tailWord_5533026, baseEnd_5533026] using wordTrace_append hprefix tailTrace_5533026
  have hstable : (prefixWord ++ tailWord_5533026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533026).length < 2 ^ (prefixWord ++ tailWord_5533026).sum := by decide
  have hdescent : baseEnd_5533026 < baseStart_5533026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533035 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 3]
def baseStart_5533035 : Nat := 118140960795 + 5533035 * 2 ^ 59
def prefixEnd_5533035 : Nat := 4983230072969 + 3 ^ 40 * 5533035 * 2
def baseEnd_5533035 : Nat := 2841106433149864708816541

theorem tailTrace_5533035 : CollatzResearch.WordTrace tailWord_5533035 prefixEnd_5533035 2841106433149864708816541 := by
  unfold tailWord_5533035
  simp only [CollatzResearch.WordTrace]
  refine ⟨201806365509766636990432559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134537577006511091326955039 201806365509766636990432559)
  ·
    refine ⟨302709548264649955485648839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201806365509766636990432559 302709548264649955485648839)
    ·
      refine ⟨454064322396974933228473259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302709548264649955485648839 454064322396974933228473259)
      ·
        refine ⟨681096483595462399842709889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454064322396974933228473259 681096483595462399842709889)
        ·
          refine ⟨510822362696596799882032417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681096483595462399842709889 510822362696596799882032417)
          ·
            refine ⟨383116772022447599911524313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510822362696596799882032417 383116772022447599911524313)
            ·
              refine ⟨287337579016835699933643235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383116772022447599911524313 287337579016835699933643235)
              ·
                refine ⟨431006368525253549900464853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287337579016835699933643235 431006368525253549900464853)
                ·
                  refine ⟨10101711762310630075792145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 431006368525253549900464853 10101711762310630075792145)
                  ·
                    refine ⟨7576283821732972556844109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10101711762310630075792145 7576283821732972556844109)
                    ·
                      refine ⟨2841106433149864708816541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7576283821732972556844109 2841106433149864708816541)
                      ·
                        rfl

theorem cell23_5533035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 3].length) (baseStart_5533035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533035 prefixEnd_5533035 := by exact prefixLift 5533035
  have htrace : WordTrace (prefixWord ++ tailWord_5533035) baseStart_5533035 baseEnd_5533035 := by
    simpa [prefixWord, tailWord_5533035, baseEnd_5533035] using wordTrace_append hprefix tailTrace_5533035
  have hstable : (prefixWord ++ tailWord_5533035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533035).length < 2 ^ (prefixWord ++ tailWord_5533035).sum := by decide
  have hdescent : baseEnd_5533035 < baseStart_5533035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533082 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3]
def baseStart_5533082 : Nat := 118140960795 + 5533082 * 2 ^ 59
def prefixEnd_5533082 : Nat := 4983230072969 + 3 ^ 40 * 5533082 * 2
def baseEnd_5533082 : Nat := 2841130566740626024928825

theorem tailTrace_5533082 : CollatzResearch.WordTrace tailWord_5533082 prefixEnd_5533082 2841130566740626024928825 := by
  unfold tailWord_5533082
  simp only [CollatzResearch.WordTrace]
  refine ⟨50452019935149091004348375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134538719827064242678262333 50452019935149091004348375)
  ·
    refine ⟨75678029902723636506522563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50452019935149091004348375 75678029902723636506522563)
    ·
      refine ⟨113517044854085454759783845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75678029902723636506522563 113517044854085454759783845)
      ·
        refine ⟨21284445910141022767459471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113517044854085454759783845 21284445910141022767459471)
        ·
          refine ⟨31926668865211534151189207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21284445910141022767459471 31926668865211534151189207)
          ·
            refine ⟨47890003297817301226783811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31926668865211534151189207 47890003297817301226783811)
            ·
              refine ⟨71835004946725951840175717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47890003297817301226783811 71835004946725951840175717)
              ·
                refine ⟨13469063427511115970032947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71835004946725951840175717 13469063427511115970032947)
                ·
                  refine ⟨20203595141266673955049421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13469063427511115970032947 20203595141266673955049421)
                  ·
                    refine ⟨7576348177975002733143533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20203595141266673955049421 7576348177975002733143533)
                    ·
                      refine ⟨2841130566740626024928825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7576348177975002733143533 2841130566740626024928825)
                      ·
                        rfl

theorem cell23_5533082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_5533082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533082 prefixEnd_5533082 := by exact prefixLift 5533082
  have htrace : WordTrace (prefixWord ++ tailWord_5533082) baseStart_5533082 baseEnd_5533082 := by
    simpa [prefixWord, tailWord_5533082, baseEnd_5533082] using wordTrace_append hprefix tailTrace_5533082
  have hstable : (prefixWord ++ tailWord_5533082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533082).length < 2 ^ (prefixWord ++ tailWord_5533082).sum := by decide
  have hdescent : baseEnd_5533082 < baseStart_5533082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533116 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_5533116 : Nat := 118140960795 + 5533116 * 2 ^ 59
def prefixEnd_5533116 : Nat := 4983230072969 + 3 ^ 40 * 5533116 * 2
def baseEnd_5533116 : Nat := 2841148025082878891903669

theorem tailTrace_5533116 : CollatzResearch.WordTrace tailWord_5533116 prefixEnd_5533116 2841148025082878891903669 := by
  unfold tailWord_5533116
  simp only [CollatzResearch.WordTrace]
  refine ⟨100904659911236593912065601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134539546548315458549420801 100904659911236593912065601)
  ·
    refine ⟨75678494933427445434049201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100904659911236593912065601 75678494933427445434049201)
    ·
      refine ⟨56758871200070584075536901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75678494933427445434049201 56758871200070584075536901)
      ·
        refine ⟨10642288350013234514163169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56758871200070584075536901 10642288350013234514163169)
        ·
          refine ⟨7981716262509925885622377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10642288350013234514163169 7981716262509925885622377)
          ·
            refine ⟨5986287196882444414216783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7981716262509925885622377 5986287196882444414216783)
            ·
              refine ⟨8979430795323666621325175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5986287196882444414216783 8979430795323666621325175)
              ·
                refine ⟨13469146192985499931987763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8979430795323666621325175 13469146192985499931987763)
                ·
                  refine ⟨20203719289478249897981645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13469146192985499931987763 20203719289478249897981645)
                  ·
                    refine ⟨7576394733554343711743117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20203719289478249897981645 7576394733554343711743117)
                    ·
                      refine ⟨2841148025082878891903669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7576394733554343711743117 2841148025082878891903669)
                      ·
                        rfl

theorem cell23_5533116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_5533116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533116 prefixEnd_5533116 := by exact prefixLift 5533116
  have htrace : WordTrace (prefixWord ++ tailWord_5533116) baseStart_5533116 baseEnd_5533116 := by
    simpa [prefixWord, tailWord_5533116, baseEnd_5533116] using wordTrace_append hprefix tailTrace_5533116
  have hstable : (prefixWord ++ tailWord_5533116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533116).length < 2 ^ (prefixWord ++ tailWord_5533116).sum := by decide
  have hdescent : baseEnd_5533116 < baseStart_5533116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533135 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 4]
def baseStart_5533135 : Nat := 118140960795 + 5533135 * 2 ^ 59
def prefixEnd_5533135 : Nat := 4983230072969 + 3 ^ 40 * 5533135 * 2
def baseEnd_5533135 : Nat := 2841157781215314317566081

theorem tailTrace_5533135 : CollatzResearch.WordTrace tailWord_5533135 prefixEnd_5533135 2841157781215314317566081 := by
  unfold tailWord_5533135
  simp only [CollatzResearch.WordTrace]
  refine ⟨201810012809404354069072859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134540008539602902712715239 201810012809404354069072859)
  ·
    refine ⟨302715019214106531103609289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201810012809404354069072859 302715019214106531103609289)
    ·
      refine ⟨227036264410579898327706967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302715019214106531103609289 227036264410579898327706967)
      ·
        refine ⟨340554396615869847491560451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227036264410579898327706967 340554396615869847491560451)
        ·
          refine ⟨510831594923804771237340677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340554396615869847491560451 510831594923804771237340677)
          ·
            refine ⟨95780924048213394607001377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 510831594923804771237340677 95780924048213394607001377)
            ·
              refine ⟨71835693036160045955251033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95780924048213394607001377 71835693036160045955251033)
              ·
                refine ⟨53876769777120034466438275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71835693036160045955251033 53876769777120034466438275)
                ·
                  refine ⟨80815154665680051699657413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53876769777120034466438275 80815154665680051699657413)
                  ·
                    refine ⟨15152841499815009693685765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80815154665680051699657413 15152841499815009693685765)
                    ·
                      refine ⟨2841157781215314317566081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15152841499815009693685765 2841157781215314317566081)
                      ·
                        rfl

theorem cell23_5533135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_5533135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533135 prefixEnd_5533135 := by exact prefixLift 5533135
  have htrace : WordTrace (prefixWord ++ tailWord_5533135) baseStart_5533135 baseEnd_5533135 := by
    simpa [prefixWord, tailWord_5533135, baseEnd_5533135] using wordTrace_append hprefix tailTrace_5533135
  have hstable : (prefixWord ++ tailWord_5533135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533135).length < 2 ^ (prefixWord ++ tailWord_5533135).sum := by decide
  have hdescent : baseEnd_5533135 < baseStart_5533135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533175 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 1, 7]
def baseStart_5533175 : Nat := 118140960795 + 5533175 * 2 ^ 59
def prefixEnd_5533175 : Nat := 4983230072969 + 3 ^ 40 * 5533175 * 2
def baseEnd_5533175 : Nat := 947059440147164720355299

theorem tailTrace_5533175 : CollatzResearch.WordTrace tailWord_5533175 prefixEnd_5533175 947059440147164720355299 := by
  unfold tailWord_5533175
  simp only [CollatzResearch.WordTrace]
  refine ⟨201811471729259440900528979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134540981152839627267019319 201811471729259440900528979)
  ·
    refine ⟨302717207593889161350793469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201811471729259440900528979 302717207593889161350793469)
    ·
      refine ⟨113518952847708435506547551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302717207593889161350793469 113518952847708435506547551)
      ·
        refine ⟨170278429271562653259821327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113518952847708435506547551 170278429271562653259821327)
        ·
          refine ⟨255417643907343979889731991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170278429271562653259821327 255417643907343979889731991)
          ·
            refine ⟨383126465861015969834597987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255417643907343979889731991 383126465861015969834597987)
            ·
              refine ⟨574689698791523954751896981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383126465861015969834597987 574689698791523954751896981)
              ·
                refine ⟨26938579630852685378995171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 574689698791523954751896981 26938579630852685378995171)
                ·
                  refine ⟨40407869446279028068492757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26938579630852685378995171 40407869446279028068492757)
                  ·
                    refine ⟨947059440147164720355299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40407869446279028068492757 947059440147164720355299)
                    ·
                      rfl

theorem cell23_5533175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_5533175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533175 prefixEnd_5533175 := by exact prefixLift 5533175
  have htrace : WordTrace (prefixWord ++ tailWord_5533175) baseStart_5533175 baseEnd_5533175 := by
    simpa [prefixWord, tailWord_5533175, baseEnd_5533175] using wordTrace_append hprefix tailTrace_5533175
  have hstable : (prefixWord ++ tailWord_5533175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533175).length < 2 ^ (prefixWord ++ tailWord_5533175).sum := by decide
  have hdescent : baseEnd_5533175 < baseStart_5533175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533192 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 2, 5]
def baseStart_5533192 : Nat := 118140960795 + 5533192 * 2 ^ 59
def prefixEnd_5533192 : Nat := 4983230072969 + 3 ^ 40 * 5533192 * 2
def baseEnd_5533192 : Nat := 947062349870873531517773

theorem tailTrace_5533192 : CollatzResearch.WordTrace tailWord_5533192 prefixEnd_5533192 947062349870873531517773 := by
  unfold tailWord_5533192
  simp only [CollatzResearch.WordTrace]
  refine ⟨100906045885098926401948915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134541394513465235202598553 100906045885098926401948915)
  ·
    refine ⟨151359068827648389602923373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100906045885098926401948915 151359068827648389602923373)
    ·
      refine ⟨56759650810368146101096265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151359068827648389602923373 56759650810368146101096265)
      ·
        refine ⟨42569738107776109575822199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56759650810368146101096265 42569738107776109575822199)
        ·
          refine ⟨63854607161664164363733299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42569738107776109575822199 63854607161664164363733299)
          ·
            refine ⟨95781910742496246545599949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63854607161664164363733299 95781910742496246545599949)
            ·
              refine ⟨35918216528436092454599981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95781910742496246545599949 35918216528436092454599981)
              ·
                refine ⟨13469331198163534670474993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35918216528436092454599981 13469331198163534670474993)
                ·
                  refine ⟨10101998398622651002856245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13469331198163534670474993 10101998398622651002856245)
                  ·
                    refine ⟨947062349870873531517773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10101998398622651002856245 947062349870873531517773)
                    ·
                      rfl

theorem cell23_5533192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_5533192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533192 prefixEnd_5533192 := by exact prefixLift 5533192
  have htrace : WordTrace (prefixWord ++ tailWord_5533192) baseStart_5533192 baseEnd_5533192 := by
    simpa [prefixWord, tailWord_5533192, baseEnd_5533192] using wordTrace_append hprefix tailTrace_5533192
  have hstable : (prefixWord ++ tailWord_5533192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533192).length < 2 ^ (prefixWord ++ tailWord_5533192).sum := by decide
  have hdescent : baseEnd_5533192 < baseStart_5533192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533232 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 3]
def baseStart_5533232 : Nat := 118140960795 + 5533232 * 2 ^ 59
def prefixEnd_5533232 : Nat := 4983230072969 + 3 ^ 40 * 5533232 * 2
def baseEnd_5533232 : Nat := 2841207588838800438053135

theorem tailTrace_5533232 : CollatzResearch.WordTrace tailWord_5533232 prefixEnd_5533232 2841207588838800438053135 := by
  unfold tailWord_5533232
  simp only [CollatzResearch.WordTrace]
  refine ⟨100906775345026469817676975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134542367126701959756902633 100906775345026469817676975)
  ·
    refine ⟨151360163017539704726515463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100906775345026469817676975 151360163017539704726515463)
    ·
      refine ⟨227040244526309557089773195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151360163017539704726515463 227040244526309557089773195)
      ·
        refine ⟨340560366789464335634659793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227040244526309557089773195 340560366789464335634659793)
        ·
          refine ⟨255420275092098251725994845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340560366789464335634659793 255420275092098251725994845)
          ·
            refine ⟨95782603159536844397248067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255420275092098251725994845 95782603159536844397248067)
            ·
              refine ⟨143673904739305266595872101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95782603159536844397248067 143673904739305266595872101)
              ·
                refine ⟨26938857138619737486726019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143673904739305266595872101 26938857138619737486726019)
                ·
                  refine ⟨40408285707929606230089029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26938857138619737486726019 40408285707929606230089029)
                  ·
                    refine ⟨7576553570236801168141693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40408285707929606230089029 7576553570236801168141693)
                    ·
                      refine ⟨2841207588838800438053135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7576553570236801168141693 2841207588838800438053135)
                      ·
                        rfl

theorem cell23_5533232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 3].length) (baseStart_5533232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533232 prefixEnd_5533232 := by exact prefixLift 5533232
  have htrace : WordTrace (prefixWord ++ tailWord_5533232) baseStart_5533232 baseEnd_5533232 := by
    simpa [prefixWord, tailWord_5533232, baseEnd_5533232] using wordTrace_append hprefix tailTrace_5533232
  have hstable : (prefixWord ++ tailWord_5533232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533232).length < 2 ^ (prefixWord ++ tailWord_5533232).sum := by decide
  have hdescent : baseEnd_5533232 < baseStart_5533232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533239 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 3, 4]
def baseStart_5533239 : Nat := 118140960795 + 5533239 * 2 ^ 59
def prefixEnd_5533239 : Nat := 4983230072969 + 3 ^ 40 * 5533239 * 2
def baseEnd_5533239 : Nat := 947070394401127303555201

theorem tailTrace_5533239 : CollatzResearch.WordTrace tailWord_5533239 prefixEnd_5533239 947070394401127303555201 := by
  unfold tailWord_5533239
  simp only [CollatzResearch.WordTrace]
  refine ⟨201813806001027579830858771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134542537334018386553905847 201813806001027579830858771)
  ·
    refine ⟨302720709001541369746288157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201813806001027579830858771 302720709001541369746288157)
    ·
      refine ⟨113520265875578013654858059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302720709001541369746288157 113520265875578013654858059)
      ·
        refine ⟨170280398813367020482287089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113520265875578013654858059 170280398813367020482287089)
        ·
          refine ⟨127710299110025265361715317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170280398813367020482287089 127710299110025265361715317)
          ·
            refine ⟨11972840541564868627660811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127710299110025265361715317 11972840541564868627660811)
            ·
              refine ⟨17959260812347302941491217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11972840541564868627660811 17959260812347302941491217)
              ·
                refine ⟨13469445609260477206118413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17959260812347302941491217 13469445609260477206118413)
                ·
                  refine ⟨5051042103472678952294405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13469445609260477206118413 5051042103472678952294405)
                  ·
                    refine ⟨947070394401127303555201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5051042103472678952294405 947070394401127303555201)
                    ·
                      rfl

theorem cell23_5533239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_5533239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533239 prefixEnd_5533239 := by exact prefixLift 5533239
  have htrace : WordTrace (prefixWord ++ tailWord_5533239) baseStart_5533239 baseEnd_5533239 := by
    simpa [prefixWord, tailWord_5533239, baseEnd_5533239] using wordTrace_append hprefix tailTrace_5533239
  have hstable : (prefixWord ++ tailWord_5533239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533239).length < 2 ^ (prefixWord ++ tailWord_5533239).sum := by decide
  have hdescent : baseEnd_5533239 < baseStart_5533239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533249 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_5533249 : Nat := 118140960795 + 5533249 * 2 ^ 59
def prefixEnd_5533249 : Nat := 4983230072969 + 3 ^ 40 * 5533249 * 2
def baseEnd_5533249 : Nat := 2841216318009926871540557

theorem tailTrace_5533249 : CollatzResearch.WordTrace tailWord_5533249 prefixEnd_5533249 2841216318009926871540557 := by
  unfold tailWord_5533249
  simp only [CollatzResearch.WordTrace]
  refine ⟨201814170730991351538722801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134542780487327567692481867 201814170730991351538722801)
  ·
    refine ⟨151360628048243513654042101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201814170730991351538722801 151360628048243513654042101)
    ·
      refine ⟨14190058879522829405066447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151360628048243513654042101 14190058879522829405066447)
      ·
        refine ⟨21285088319284244107599671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14190058879522829405066447 21285088319284244107599671)
        ·
          refine ⟨31927632478926366161399507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21285088319284244107599671 31927632478926366161399507)
          ·
            refine ⟨47891448718389549242099261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31927632478926366161399507 47891448718389549242099261)
            ·
              refine ⟨17959293269396080965787223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47891448718389549242099261 17959293269396080965787223)
              ·
                refine ⟨26938939904094121448680835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17959293269396080965787223 26938939904094121448680835)
                ·
                  refine ⟨40408409856141182173021253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26938939904094121448680835 40408409856141182173021253)
                  ·
                    refine ⟨7576576848026471657441485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40408409856141182173021253 7576576848026471657441485)
                    ·
                      refine ⟨2841216318009926871540557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7576576848026471657441485 2841216318009926871540557)
                      ·
                        rfl

theorem cell23_5533249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_5533249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533249 prefixEnd_5533249 := by exact prefixLift 5533249
  have htrace : WordTrace (prefixWord ++ tailWord_5533249) baseStart_5533249 baseEnd_5533249 := by
    simpa [prefixWord, tailWord_5533249, baseEnd_5533249] using wordTrace_append hprefix tailTrace_5533249
  have hstable : (prefixWord ++ tailWord_5533249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533249).length < 2 ^ (prefixWord ++ tailWord_5533249).sum := by decide
  have hdescent : baseEnd_5533249 < baseStart_5533249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533289 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 1, 5, 2]
def baseStart_5533289 : Nat := 118140960795 + 5533289 * 2 ^ 59
def prefixEnd_5533289 : Nat := 4983230072969 + 3 ^ 40 * 5533289 * 2
def baseEnd_5533289 : Nat := 2841236857236106715040373

theorem tailTrace_5533289 : CollatzResearch.WordTrace tailWord_5533289 prefixEnd_5533289 2841236857236106715040373 := by
  unfold tailWord_5533289
  simp only [CollatzResearch.WordTrace]
  refine ⟨201815629650846438370178921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134543753100564292246785947 201815629650846438370178921)
  ·
    refine ⟨151361722238134828777634191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201815629650846438370178921 151361722238134828777634191)
    ·
      refine ⟨227042583357202243166451287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151361722238134828777634191 227042583357202243166451287)
      ·
        refine ⟨340563875035803364749676931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227042583357202243166451287 340563875035803364749676931)
        ·
          refine ⟨510845812553705047124515397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340563875035803364749676931 510845812553705047124515397)
          ·
            refine ⟨95783589853819696335846637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 510845812553705047124515397 95783589853819696335846637)
            ·
              refine ⟨35918846195182386125942489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95783589853819696335846637 35918846195182386125942489)
              ·
                refine ⟨26939134646386789594456867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35918846195182386125942489 26939134646386789594456867)
                ·
                  refine ⟨40408701969580184391685301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26939134646386789594456867 40408701969580184391685301)
                  ·
                    refine ⟨3788315809648142286720497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40408701969580184391685301 3788315809648142286720497)
                    ·
                      refine ⟨2841236857236106715040373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3788315809648142286720497 2841236857236106715040373)
                      ·
                        rfl

theorem cell23_5533289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 5, 2].length) (baseStart_5533289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533289 prefixEnd_5533289 := by exact prefixLift 5533289
  have htrace : WordTrace (prefixWord ++ tailWord_5533289) baseStart_5533289 baseEnd_5533289 := by
    simpa [prefixWord, tailWord_5533289, baseEnd_5533289] using wordTrace_append hprefix tailTrace_5533289
  have hstable : (prefixWord ++ tailWord_5533289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533289).length < 2 ^ (prefixWord ++ tailWord_5533289).sum := by decide
  have hdescent : baseEnd_5533289 < baseStart_5533289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533296 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 3, 1, 3]
def baseStart_5533296 : Nat := 118140960795 + 5533296 * 2 ^ 59
def prefixEnd_5533296 : Nat := 4983230072969 + 3 ^ 40 * 5533296 * 2
def baseEnd_5533296 : Nat := 2841240451600688187652841

theorem tailTrace_5533296 : CollatzResearch.WordTrace tailWord_5533296 prefixEnd_5533296 2841240451600688187652841 := by
  unfold tailWord_5533296
  simp only [CollatzResearch.WordTrace]
  refine ⟨100907942480910539282841871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134543923307880719043789161 100907942480910539282841871)
  ·
    refine ⟨151361913721365808924262807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100907942480910539282841871 151361913721365808924262807)
    ·
      refine ⟨227042870582048713386394211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151361913721365808924262807 227042870582048713386394211)
      ·
        refine ⟨340564305873073070079591317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227042870582048713386394211 340564305873073070079591317)
        ·
          refine ⟨15963951837800300159980843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 340564305873073070079591317 15963951837800300159980843)
          ·
            refine ⟨23945927756700450239971265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15963951837800300159980843 23945927756700450239971265)
            ·
              refine ⟨17959445817525337679978449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23945927756700450239971265 17959445817525337679978449)
              ·
                refine ⟨13469584363144003259983837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17959445817525337679978449 13469584363144003259983837)
                ·
                  refine ⟨5051094136179001222493939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13469584363144003259983837 5051094136179001222493939)
                  ·
                    refine ⟨7576641204268501833740909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5051094136179001222493939 7576641204268501833740909)
                    ·
                      refine ⟨2841240451600688187652841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7576641204268501833740909 2841240451600688187652841)
                      ·
                        rfl

theorem cell23_5533296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3, 1, 3].length) (baseStart_5533296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533296 prefixEnd_5533296 := by exact prefixLift 5533296
  have htrace : WordTrace (prefixWord ++ tailWord_5533296) baseStart_5533296 baseEnd_5533296 := by
    simpa [prefixWord, tailWord_5533296, baseEnd_5533296] using wordTrace_append hprefix tailTrace_5533296
  have hstable : (prefixWord ++ tailWord_5533296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533296).length < 2 ^ (prefixWord ++ tailWord_5533296).sum := by decide
  have hdescent : baseEnd_5533296 < baseStart_5533296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533312 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 3, 6]
def baseStart_5533312 : Nat := 118140960795 + 5533312 * 2 ^ 59
def prefixEnd_5533312 : Nat := 4983230072969 + 3 ^ 40 * 5533312 * 2
def baseEnd_5533312 : Nat := 947082889097053375017589

theorem tailTrace_5533312 : CollatzResearch.WordTrace tailWord_5533312 prefixEnd_5533312 947082889097053375017589 := by
  unfold tailWord_5533312
  simp only [CollatzResearch.WordTrace]
  refine ⟨100908234264881556649133095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134544312353175408865510793 100908234264881556649133095)
  ·
    refine ⟨151362351397322334973699643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100908234264881556649133095 151362351397322334973699643)
    ·
      refine ⟨227043527095983502460549465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151362351397322334973699643 227043527095983502460549465)
      ·
        refine ⟨170282645321987626845412099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227043527095983502460549465 170282645321987626845412099)
        ·
          refine ⟨255423967982981440268118149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170282645321987626845412099 255423967982981440268118149)
          ·
            refine ⟨47891993996809020050272153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255423967982981440268118149 47891993996809020050272153)
            ·
              refine ⟨35918995497606765037704115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47891993996809020050272153 35918995497606765037704115)
              ·
                refine ⟨53878493246410147556556173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35918995497606765037704115 53878493246410147556556173)
                ·
                  refine ⟨20204434967403805333708565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53878493246410147556556173 20204434967403805333708565)
                  ·
                    refine ⟨947082889097053375017589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20204434967403805333708565 947082889097053375017589)
                    ·
                      rfl

theorem cell23_5533312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_5533312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533312 prefixEnd_5533312 := by exact prefixLift 5533312
  have htrace : WordTrace (prefixWord ++ tailWord_5533312) baseStart_5533312 baseEnd_5533312 := by
    simpa [prefixWord, tailWord_5533312, baseEnd_5533312] using wordTrace_append hprefix tailTrace_5533312
  have hstable : (prefixWord ++ tailWord_5533312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533312).length < 2 ^ (prefixWord ++ tailWord_5533312).sum := by decide
  have hdescent : baseEnd_5533312 < baseStart_5533312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533330 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_5533330 : Nat := 118140960795 + 5533330 * 2 ^ 59
def prefixEnd_5533330 : Nat := 4983230072969 + 3 ^ 40 * 5533330 * 2
def baseEnd_5533330 : Nat := 2841257909942941054627685

theorem tailTrace_5533330 : CollatzResearch.WordTrace tailWord_5533330 prefixEnd_5533330 2841257909942941054627685 := by
  unfold tailWord_5533330
  simp only [CollatzResearch.WordTrace]
  refine ⟨50454281260924475593105361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134544750029131934914947629 50454281260924475593105361)
  ·
    refine ⟨37840710945693356694829021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50454281260924475593105361 37840710945693356694829021)
    ·
      refine ⟨14190266604635008760560883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37840710945693356694829021 14190266604635008760560883)
      ·
        refine ⟨21285399906952513140841325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14190266604635008760560883 21285399906952513140841325)
        ·
          refine ⟨7982024965107192427815497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21285399906952513140841325 7982024965107192427815497)
          ·
            refine ⟨5986518723830394320861623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7982024965107192427815497 5986518723830394320861623)
            ·
              refine ⟨8979778085745591481292435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5986518723830394320861623 8979778085745591481292435)
              ·
                refine ⟨13469667128618387221938653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8979778085745591481292435 13469667128618387221938653)
                ·
                  refine ⟨5051125173231895208226995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13469667128618387221938653 5051125173231895208226995)
                  ·
                    refine ⟨7576687759847842812340493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5051125173231895208226995 7576687759847842812340493)
                    ·
                      refine ⟨2841257909942941054627685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7576687759847842812340493 2841257909942941054627685)
                      ·
                        rfl

theorem cell23_5533330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_5533330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533330 prefixEnd_5533330 := by exact prefixLift 5533330
  have htrace : WordTrace (prefixWord ++ tailWord_5533330) baseStart_5533330 baseEnd_5533330 := by
    simpa [prefixWord, tailWord_5533330, baseEnd_5533330] using wordTrace_append hprefix tailTrace_5533330
  have hstable : (prefixWord ++ tailWord_5533330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533330).length < 2 ^ (prefixWord ++ tailWord_5533330).sum := by decide
  have hdescent : baseEnd_5533330 < baseStart_5533330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533369 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 3, 3, 3]
def baseStart_5533369 : Nat := 118140960795 + 5533369 * 2 ^ 59
def prefixEnd_5533369 : Nat := 4983230072969 + 3 ^ 40 * 5533369 * 2
def baseEnd_5533369 : Nat := 2841277935688466402040005

theorem tailTrace_5533369 : CollatzResearch.WordTrace tailWord_5533369 prefixEnd_5533369 2841277935688466402040005 := by
  unfold tailWord_5533369
  simp only [CollatzResearch.WordTrace]
  refine ⟨201818547490556612033091161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134545698327037741355394107 201818547490556612033091161)
  ·
    refine ⟨151363910617917459024818371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201818547490556612033091161 151363910617917459024818371)
    ·
      refine ⟨227045865926876188537227557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151363910617917459024818371 227045865926876188537227557)
      ·
        refine ⟨42571099861289285350730167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227045865926876188537227557 42571099861289285350730167)
        ·
          refine ⟨63856649791933928026095251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42571099861289285350730167 63856649791933928026095251)
          ·
            refine ⟨95784974687900892039142877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63856649791933928026095251 95784974687900892039142877)
            ·
              refine ⟨35919365507962834514678579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95784974687900892039142877 35919365507962834514678579)
              ·
                refine ⟨53879048261944251772017869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35919365507962834514678579 53879048261944251772017869)
                ·
                  refine ⟨20204643098229094414506701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53879048261944251772017869 20204643098229094414506701)
                  ·
                    refine ⟨7576741161835910405440013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20204643098229094414506701 7576741161835910405440013)
                    ·
                      refine ⟨2841277935688466402040005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7576741161835910405440013 2841277935688466402040005)
                      ·
                        rfl

theorem cell23_5533369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_5533369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533369 prefixEnd_5533369 := by exact prefixLift 5533369
  have htrace : WordTrace (prefixWord ++ tailWord_5533369) baseStart_5533369 baseEnd_5533369 := by
    simpa [prefixWord, tailWord_5533369, baseEnd_5533369] using wordTrace_append hprefix tailTrace_5533369
  have hstable : (prefixWord ++ tailWord_5533369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533369).length < 2 ^ (prefixWord ++ tailWord_5533369).sum := by decide
  have hdescent : baseEnd_5533369 < baseStart_5533369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533373 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 1, 2, 3]
def baseStart_5533373 : Nat := 118140960795 + 5533373 * 2 ^ 59
def prefixEnd_5533373 : Nat := 4983230072969 + 3 ^ 40 * 5533373 * 2
def baseEnd_5533373 : Nat := 2841279989611084386389987

theorem tailTrace_5533373 : CollatzResearch.WordTrace tailWord_5533373 prefixEnd_5533373 2841279989611084386389987 := by
  unfold tailWord_5533373
  simp only [CollatzResearch.WordTrace]
  refine ⟨201818693382542120716236773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134545795588361413810824515 201818693382542120716236773)
  ·
    refine ⟨37841005009226647634294395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201818693382542120716236773 37841005009226647634294395)
    ·
      refine ⟨56761507513839971451441593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37841005009226647634294395 56761507513839971451441593)
      ·
        refine ⟨42571130635379978588581195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56761507513839971451441593 42571130635379978588581195)
        ·
          refine ⟨63856695953069967882871793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42571130635379978588581195 63856695953069967882871793)
          ·
            refine ⟨47892521964802475912153845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63856695953069967882871793 47892521964802475912153845)
            ·
              refine ⟨4489923934200232116764423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47892521964802475912153845 4489923934200232116764423)
              ·
                refine ⟨6734885901300348175146635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4489923934200232116764423 6734885901300348175146635)
                ·
                  refine ⟨10102328851950522262719953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6734885901300348175146635 10102328851950522262719953)
                  ·
                    refine ⟨7576746638962891697039965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10102328851950522262719953 7576746638962891697039965)
                    ·
                      refine ⟨2841279989611084386389987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7576746638962891697039965 2841279989611084386389987)
                      ·
                        rfl

theorem cell23_5533373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_5533373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533373 prefixEnd_5533373 := by exact prefixLift 5533373
  have htrace : WordTrace (prefixWord ++ tailWord_5533373) baseStart_5533373 baseEnd_5533373 := by
    simpa [prefixWord, tailWord_5533373, baseEnd_5533373] using wordTrace_append hprefix tailTrace_5533373
  have hstable : (prefixWord ++ tailWord_5533373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533373).length < 2 ^ (prefixWord ++ tailWord_5533373).sum := by decide
  have hdescent : baseEnd_5533373 < baseStart_5533373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533413 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 1, 3, 2]
def baseStart_5533413 : Nat := 118140960795 + 5533413 * 2 ^ 59
def prefixEnd_5533413 : Nat := 4983230072969 + 3 ^ 40 * 5533413 * 2
def baseEnd_5533413 : Nat := 2841300528837264229889803

theorem tailTrace_5533413 : CollatzResearch.WordTrace tailWord_5533413 prefixEnd_5533413 2841300528837264229889803 := by
  unfold tailWord_5533413
  simp only [CollatzResearch.WordTrace]
  refine ⟨201820152302397207547692893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134546768201598138365128595 201820152302397207547692893)
  ·
    refine ⟨75682557113398952830384835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201820152302397207547692893 75682557113398952830384835)
    ·
      refine ⟨113523835670098429245577253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75682557113398952830384835 113523835670098429245577253)
      ·
        refine ⟨21285719188143455483545735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113523835670098429245577253 21285719188143455483545735)
        ·
          refine ⟨31928578782215183225318603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21285719188143455483545735 31928578782215183225318603)
          ·
            refine ⟨47892868173322774837977905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31928578782215183225318603 47892868173322774837977905)
            ·
              refine ⟨35919651129992081128483429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47892868173322774837977905 35919651129992081128483429)
              ·
                refine ⟨6734934586873515211590643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35919651129992081128483429 6734934586873515211590643)
                ·
                  refine ⟨10102401880310272817385965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6734934586873515211590643 10102401880310272817385965)
                  ·
                    refine ⟨3788400705116352306519737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10102401880310272817385965 3788400705116352306519737)
                    ·
                      refine ⟨2841300528837264229889803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3788400705116352306519737 2841300528837264229889803)
                      ·
                        rfl

theorem cell23_5533413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_5533413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533413 prefixEnd_5533413 := by exact prefixLift 5533413
  have htrace : WordTrace (prefixWord ++ tailWord_5533413) baseStart_5533413 baseEnd_5533413 := by
    simpa [prefixWord, tailWord_5533413, baseEnd_5533413] using wordTrace_append hprefix tailTrace_5533413
  have hstable : (prefixWord ++ tailWord_5533413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533413).length < 2 ^ (prefixWord ++ tailWord_5533413).sum := by decide
  have hdescent : baseEnd_5533413 < baseStart_5533413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533430 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_5533430 : Nat := 118140960795 + 5533430 * 2 ^ 59
def prefixEnd_5533430 : Nat := 4983230072969 + 3 ^ 40 * 5533430 * 2
def baseEnd_5533430 : Nat := 2841309258008390663377225

theorem tailTrace_5533430 : CollatzResearch.WordTrace tailWord_5533430 prefixEnd_5533430 2841309258008390663377225 := by
  unfold tailWord_5533430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12613798271458476215691359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134547181562223746300707829 12613798271458476215691359)
  ·
    refine ⟨18920697407187714323537039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12613798271458476215691359 18920697407187714323537039)
    ·
      refine ⟨28381046110781571485305559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18920697407187714323537039 28381046110781571485305559)
      ·
        refine ⟨42571569166172357227958339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28381046110781571485305559 42571569166172357227958339)
        ·
          refine ⟨63857353749258535841937509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42571569166172357227958339 63857353749258535841937509)
          ·
            refine ⟨11973253827985975470363283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63857353749258535841937509 11973253827985975470363283)
            ·
              refine ⟨17959880741978963205544925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11973253827985975470363283 17959880741978963205544925)
              ·
                refine ⟨6734955278242111202079347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17959880741978963205544925 6734955278242111202079347)
                ·
                  refine ⟨10102432917363166803119021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6734955278242111202079347 10102432917363166803119021)
                  ·
                    refine ⟨3788412344011187551169633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10102432917363166803119021 3788412344011187551169633)
                    ·
                      refine ⟨2841309258008390663377225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3788412344011187551169633 2841309258008390663377225)
                      ·
                        rfl

theorem cell23_5533430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_5533430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533430 prefixEnd_5533430 := by exact prefixLift 5533430
  have htrace : WordTrace (prefixWord ++ tailWord_5533430) baseStart_5533430 baseEnd_5533430 := by
    simpa [prefixWord, tailWord_5533430, baseEnd_5533430] using wordTrace_append hprefix tailTrace_5533430
  have hstable : (prefixWord ++ tailWord_5533430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533430).length < 2 ^ (prefixWord ++ tailWord_5533430).sum := by decide
  have hdescent : baseEnd_5533430 < baseStart_5533430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533439 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 4]
def baseStart_5533439 : Nat := 118140960795 + 5533439 * 2 ^ 59
def prefixEnd_5533439 : Nat := 4983230072969 + 3 ^ 40 * 5533439 * 2
def baseEnd_5533439 : Nat := 2841313879334281128164683

theorem tailTrace_5533439 : CollatzResearch.WordTrace tailWord_5533439 prefixEnd_5533439 2841313879334281128164683 := by
  unfold tailWord_5533439
  simp only [CollatzResearch.WordTrace]
  refine ⟨201821100600303013988139371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134547400400202009325426247 201821100600303013988139371)
  ·
    refine ⟨302731650900454520982209057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201821100600303013988139371 302731650900454520982209057)
    ·
      refine ⟨227048738175340890736656793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302731650900454520982209057 227048738175340890736656793)
      ·
        refine ⟨170286553631505668052492595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227048738175340890736656793 170286553631505668052492595)
        ·
          refine ⟨255429830447258502078738893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170286553631505668052492595 255429830447258502078738893)
          ·
            refine ⟨95786186417721938279527085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255429830447258502078738893 95786186417721938279527085)
            ·
              refine ⟨35919819906645726854822657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95786186417721938279527085 35919819906645726854822657)
              ·
                refine ⟨26939864929984295141116993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35919819906645726854822657 26939864929984295141116993)
                ·
                  refine ⟨20204898697488221355837745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26939864929984295141116993 20204898697488221355837745)
                  ·
                    refine ⟨15153674023116166016878309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20204898697488221355837745 15153674023116166016878309)
                    ·
                      refine ⟨2841313879334281128164683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15153674023116166016878309 2841313879334281128164683)
                      ·
                        rfl

theorem cell23_5533439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_5533439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533439 prefixEnd_5533439 := by exact prefixLift 5533439
  have htrace : WordTrace (prefixWord ++ tailWord_5533439) baseStart_5533439 baseEnd_5533439 := by
    simpa [prefixWord, tailWord_5533439, baseEnd_5533439] using wordTrace_append hprefix tailTrace_5533439
  have hstable : (prefixWord ++ tailWord_5533439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533439).length < 2 ^ (prefixWord ++ tailWord_5533439).sum := by decide
  have hdescent : baseEnd_5533439 < baseStart_5533439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533459 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 3]
def baseStart_5533459 : Nat := 118140960795 + 5533459 * 2 ^ 59
def prefixEnd_5533459 : Nat := 4983230072969 + 3 ^ 40 * 5533459 * 2
def baseEnd_5533459 : Nat := 2841324148947371049914591

theorem tailTrace_5533459 : CollatzResearch.WordTrace tailWord_5533459 prefixEnd_5533459 2841324148947371049914591 := by
  unfold tailWord_5533459
  simp only [CollatzResearch.WordTrace]
  refine ⟨201821830060230557403867431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134547886706820371602578287 201821830060230557403867431)
  ·
    refine ⟨302732745090345836105801147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201821830060230557403867431 302732745090345836105801147)
    ·
      refine ⟨454099117635518754158701721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302732745090345836105801147 454099117635518754158701721)
      ·
        refine ⟨340574338226639065619026291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454099117635518754158701721 340574338226639065619026291)
        ·
          refine ⟨510861507339958598428539437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340574338226639065619026291 510861507339958598428539437)
          ·
            refine ⟨191573065252484474410702289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 510861507339958598428539437 191573065252484474410702289)
            ·
              refine ⟨143679798939363355808026717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191573065252484474410702289 143679798939363355808026717)
              ·
                refine ⟨53879924602261258428010019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143679798939363355808026717 53879924602261258428010019)
                ·
                  refine ⟨80819886903391887642015029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53879924602261258428010019 80819886903391887642015029)
                  ·
                    refine ⟨7576864397192989466438909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80819886903391887642015029 7576864397192989466438909)
                    ·
                      refine ⟨2841324148947371049914591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7576864397192989466438909 2841324148947371049914591)
                      ·
                        rfl

theorem cell23_5533459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 3].length) (baseStart_5533459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533459 prefixEnd_5533459 := by exact prefixLift 5533459
  have htrace : WordTrace (prefixWord ++ tailWord_5533459) baseStart_5533459 baseEnd_5533459 := by
    simpa [prefixWord, tailWord_5533459, baseEnd_5533459] using wordTrace_append hprefix tailTrace_5533459
  have hstable : (prefixWord ++ tailWord_5533459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533459).length < 2 ^ (prefixWord ++ tailWord_5533459).sum := by decide
  have hdescent : baseEnd_5533459 < baseStart_5533459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533496 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 2, 5]
def baseStart_5533496 : Nat := 118140960795 + 5533496 * 2 ^ 59
def prefixEnd_5533496 : Nat := 4983230072969 + 3 ^ 40 * 5533496 * 2
def baseEnd_5533496 : Nat := 947114382577195801717307

theorem tailTrace_5533496 : CollatzResearch.WordTrace tailWord_5533496 prefixEnd_5533496 947114382577195801717307 := by
  unfold tailWord_5533496
  simp only [CollatzResearch.WordTrace]
  refine ⟨100911589780548256361482171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134548786374064341815309561 100911589780548256361482171)
  ·
    refine ⟨151367384670822384542223257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100911589780548256361482171 151367384670822384542223257)
    ·
      refine ⟨113525538503116788406667443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151367384670822384542223257 113525538503116788406667443)
      ·
        refine ⟨170288307754675182610001165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113525538503116788406667443 170288307754675182610001165)
        ·
          refine ⟨63858115408003193478750437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170288307754675182610001165 63858115408003193478750437)
          ·
            refine ⟨11973396639000598777265707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63858115408003193478750437 11973396639000598777265707)
            ·
              refine ⟨17960094958500898165898561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11973396639000598777265707 17960094958500898165898561)
              ·
                refine ⟨13470071218875673624423921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17960094958500898165898561 13470071218875673624423921)
                ·
                  refine ⟨10102553414156755218317941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13470071218875673624423921 10102553414156755218317941)
                  ·
                    refine ⟨947114382577195801717307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10102553414156755218317941 947114382577195801717307)
                    ·
                      rfl

theorem cell23_5533496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_5533496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533496 prefixEnd_5533496 := by exact prefixLift 5533496
  have htrace : WordTrace (prefixWord ++ tailWord_5533496) baseStart_5533496 baseEnd_5533496 := by
    simpa [prefixWord, tailWord_5533496, baseEnd_5533496] using wordTrace_append hprefix tailTrace_5533496
  have hstable : (prefixWord ++ tailWord_5533496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533496).length < 2 ^ (prefixWord ++ tailWord_5533496).sum := by decide
  have hdescent : baseEnd_5533496 < baseStart_5533496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533579 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 7]
def baseStart_5533579 : Nat := 118140960795 + 5533579 * 2 ^ 59
def prefixEnd_5533579 : Nat := 4983230072969 + 3 ^ 40 * 5533579 * 2
def baseEnd_5533579 : Nat := 2841385766625910580414039

theorem tailTrace_5533579 : CollatzResearch.WordTrace tailWord_5533579 prefixEnd_5533579 2841385766625910580414039 := by
  unfold tailWord_5533579
  simp only [CollatzResearch.WordTrace]
  refine ⟨201826206819795817898235791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134550804546530545265490527 201826206819795817898235791)
  ·
    refine ⟨302739310229693726847353687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201826206819795817898235791 302739310229693726847353687)
    ·
      refine ⟨454108965344540590271030531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302739310229693726847353687 454108965344540590271030531)
      ·
        refine ⟨681163448016810885406545797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454108965344540590271030531 681163448016810885406545797)
        ·
          refine ⟨127718146503152041013727337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 681163448016810885406545797 127718146503152041013727337)
          ·
            refine ⟨95788609877364030760295503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127718146503152041013727337 95788609877364030760295503)
            ·
              refine ⟨143682914816046046140443255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95788609877364030760295503 143682914816046046140443255)
              ·
                refine ⟨215524372224069069210664883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143682914816046046140443255 215524372224069069210664883)
                ·
                  refine ⟨323286558336103603815997325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215524372224069069210664883 323286558336103603815997325)
                  ·
                    refine ⟨121232459376038851430998997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 323286558336103603815997325 121232459376038851430998997)
                    ·
                      refine ⟨2841385766625910580414039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121232459376038851430998997 2841385766625910580414039)
                      ·
                        rfl

theorem cell23_5533579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_5533579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533579 prefixEnd_5533579 := by exact prefixLift 5533579
  have htrace : WordTrace (prefixWord ++ tailWord_5533579) baseStart_5533579 baseEnd_5533579 := by
    simpa [prefixWord, tailWord_5533579, baseEnd_5533579] using wordTrace_append hprefix tailTrace_5533579
  have hstable : (prefixWord ++ tailWord_5533579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533579).length < 2 ^ (prefixWord ++ tailWord_5533579).sum := by decide
  have hdescent : baseEnd_5533579 < baseStart_5533579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533617 : List Nat := [1, 2, 2, 4, 2, 1, 2, 4, 1, 1, 3]
def baseStart_5533617 : Nat := 118140960795 + 5533617 * 2 ^ 59
def prefixEnd_5533617 : Nat := 4983230072969 + 3 ^ 40 * 5533617 * 2
def baseEnd_5533617 : Nat := 2841405278890781431738865

theorem tailTrace_5533617 : CollatzResearch.WordTrace tailWord_5533617 prefixEnd_5533617 2841405278890781431738865 := by
  unfold tailWord_5533617
  simp only [CollatzResearch.WordTrace]
  refine ⟨201827592793658150388119105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134551728529105433592079403 201827592793658150388119105)
  ·
    refine ⟨151370694595243612791089329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201827592793658150388119105 151370694595243612791089329)
    ·
      refine ⟨113528020946432709593316997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151370694595243612791089329 113528020946432709593316997)
      ·
        refine ⟨21286503927456133048746937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113528020946432709593316997 21286503927456133048746937)
        ·
          refine ⟨15964877945592099786560203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21286503927456133048746937 15964877945592099786560203)
          ·
            refine ⟨23947316918388149679840305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15964877945592099786560203 23947316918388149679840305)
            ·
              refine ⟨17960487688791112259880229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23947316918388149679840305 17960487688791112259880229)
              ·
                refine ⟨3367591441648333548727543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17960487688791112259880229 3367591441648333548727543)
                ·
                  refine ⟨5051387162472500323091315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3367591441648333548727543 5051387162472500323091315)
                  ·
                    refine ⟨7577080743708750484636973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5051387162472500323091315 7577080743708750484636973)
                    ·
                      refine ⟨2841405278890781431738865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7577080743708750484636973 2841405278890781431738865)
                      ·
                        rfl

theorem cell23_5533617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_5533617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533617 prefixEnd_5533617 := by exact prefixLift 5533617
  have htrace : WordTrace (prefixWord ++ tailWord_5533617) baseStart_5533617 baseEnd_5533617 := by
    simpa [prefixWord, tailWord_5533617, baseEnd_5533617] using wordTrace_append hprefix tailTrace_5533617
  have hstable : (prefixWord ++ tailWord_5533617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533617).length < 2 ^ (prefixWord ++ tailWord_5533617).sum := by decide
  have hdescent : baseEnd_5533617 < baseStart_5533617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533626 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3]
def baseStart_5533626 : Nat := 118140960795 + 5533626 * 2 ^ 59
def prefixEnd_5533626 : Nat := 4983230072969 + 3 ^ 40 * 5533626 * 2
def baseEnd_5533626 : Nat := 2841409900216671896526323

theorem tailTrace_5533626 : CollatzResearch.WordTrace tailWord_5533626 prefixEnd_5533626 2841409900216671896526323 := by
  unfold tailWord_5533626
  simp only [CollatzResearch.WordTrace]
  refine ⟨50456980262656386231299183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134551947367083696616797821 50456980262656386231299183)
  ·
    refine ⟨75685470393984579346948775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50456980262656386231299183 75685470393984579346948775)
    ·
      refine ⟨113528205590976869020423163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75685470393984579346948775 113528205590976869020423163)
      ·
        refine ⟨170292308386465303530634745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113528205590976869020423163 170292308386465303530634745)
        ·
          refine ⟨127719231289848977647976059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170292308386465303530634745 127719231289848977647976059)
          ·
            refine ⟨191578846934773466471964089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127719231289848977647976059 191578846934773466471964089)
            ·
              refine ⟨143684135201080099853973067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191578846934773466471964089 143684135201080099853973067)
              ·
                refine ⟨215526202801620149780959601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143684135201080099853973067 215526202801620149780959601)
                ·
                  refine ⟨161644652101215112335719701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215526202801620149780959601 161644652101215112335719701)
                  ·
                    refine ⟨7577093067244458390736861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161644652101215112335719701 7577093067244458390736861)
                    ·
                      refine ⟨2841409900216671896526323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7577093067244458390736861 2841409900216671896526323)
                      ·
                        rfl

theorem cell23_5533626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_5533626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533626 prefixEnd_5533626 := by exact prefixLift 5533626
  have htrace : WordTrace (prefixWord ++ tailWord_5533626) baseStart_5533626 baseEnd_5533626 := by
    simpa [prefixWord, tailWord_5533626, baseEnd_5533626] using wordTrace_append hprefix tailTrace_5533626
  have hstable : (prefixWord ++ tailWord_5533626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533626).length < 2 ^ (prefixWord ++ tailWord_5533626).sum := by decide
  have hdescent : baseEnd_5533626 < baseStart_5533626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533640 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_5533640 : Nat := 118140960795 + 5533640 * 2 ^ 59
def prefixEnd_5533640 : Nat := 4983230072969 + 3 ^ 40 * 5533640 * 2
def baseEnd_5533640 : Nat := 2841417088945834841751259

theorem tailTrace_5533640 : CollatzResearch.WordTrace tailWord_5533640 prefixEnd_5533640 2841417088945834841751259 := by
  unfold tailWord_5533640
  simp only [CollatzResearch.WordTrace]
  refine ⟨100914215836287412658103187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134552287781716550210804249 100914215836287412658103187)
  ·
    refine ⟨151371323754431118987154781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100914215836287412658103187 151371323754431118987154781)
    ·
      refine ⟨56764246407911669620183043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151371323754431118987154781 56764246407911669620183043)
      ·
        refine ⟨85146369611867504430274565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56764246407911669620183043 85146369611867504430274565)
        ·
          refine ⟨15964944302225157080676481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85146369611867504430274565 15964944302225157080676481)
          ·
            refine ⟨11973708226668867810507361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15964944302225157080676481 11973708226668867810507361)
            ·
              refine ⟨8980281170001650857880521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11973708226668867810507361 8980281170001650857880521)
              ·
                refine ⟨6735210877501238143410391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8980281170001650857880521 6735210877501238143410391)
                ·
                  refine ⟨10102816316251857215115587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6735210877501238143410391 10102816316251857215115587)
                  ·
                    refine ⟨15154224474377785822673381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10102816316251857215115587 15154224474377785822673381)
                    ·
                      refine ⟨2841417088945834841751259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15154224474377785822673381 2841417088945834841751259)
                      ·
                        rfl

theorem cell23_5533640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_5533640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533640 prefixEnd_5533640 := by exact prefixLift 5533640
  have htrace : WordTrace (prefixWord ++ tailWord_5533640) baseStart_5533640 baseEnd_5533640 := by
    simpa [prefixWord, tailWord_5533640, baseEnd_5533640] using wordTrace_append hprefix tailTrace_5533640
  have hstable : (prefixWord ++ tailWord_5533640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533640).length < 2 ^ (prefixWord ++ tailWord_5533640).sum := by decide
  have hdescent : baseEnd_5533640 < baseStart_5533640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
