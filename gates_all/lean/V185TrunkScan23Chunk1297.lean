import V185TrunkScan23Chunk1296

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7681569 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 4, 5]
def baseStart_7681569 : Nat := 118140960795 + 7681569 * 2 ^ 59
def prefixEnd_7681569 : Nat := 4983230072969 + 3 ^ 40 * 7681569 * 2
def baseEnd_7681569 : Nat := 1314779025892320519886871

theorem tailTrace_7681569 : CollatzResearch.WordTrace tailWord_7681569 prefixEnd_7681569 1314779025892320519886871 := by
  unfold tailWord_7681569
  simp only [CollatzResearch.WordTrace]
  refine ⟨280169838307994895384015761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186779892205329930256010507 280169838307994895384015761)
  ·
    refine ⟨210127378730996171538011821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280169838307994895384015761 210127378730996171538011821)
    ·
      refine ⟨78797767024123564326754433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210127378730996171538011821 78797767024123564326754433)
      ·
        refine ⟨59098325268092673245065825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78797767024123564326754433 59098325268092673245065825)
        ·
          refine ⟨44323743951069504933799369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59098325268092673245065825 44323743951069504933799369)
          ·
            refine ⟨33242807963302128700349527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44323743951069504933799369 33242807963302128700349527)
            ·
              refine ⟨49864211944953193050524291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33242807963302128700349527 49864211944953193050524291)
              ·
                refine ⟨74796317917429789575786437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49864211944953193050524291 74796317917429789575786437)
                ·
                  refine ⟨14024309609518085545459957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74796317917429789575786437 14024309609518085545459957)
                  ·
                    refine ⟨1314779025892320519886871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14024309609518085545459957 1314779025892320519886871)
                    ·
                      rfl

theorem cell23_7681569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_7681569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681569 prefixEnd_7681569 := by exact prefixLift 7681569
  have htrace : WordTrace (prefixWord ++ tailWord_7681569) baseStart_7681569 baseEnd_7681569 := by
    simpa [prefixWord, tailWord_7681569, baseEnd_7681569] using wordTrace_append hprefix tailTrace_7681569
  have hstable : (prefixWord ++ tailWord_7681569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681569).length < 2 ^ (prefixWord ++ tailWord_7681569).sum := by decide
  have hdescent : baseEnd_7681569 < baseStart_7681569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681609 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 1, 4, 3]
def baseStart_7681609 : Nat := 118140960795 + 7681609 * 2 ^ 59
def prefixEnd_7681609 : Nat := 4983230072969 + 3 ^ 40 * 7681609 * 2
def baseEnd_7681609 : Nat := 3944357616903141403160429

theorem tailTrace_7681609 : CollatzResearch.WordTrace tailWord_7681609 prefixEnd_7681609 3944357616903141403160429 := by
  unfold tailWord_7681609
  simp only [CollatzResearch.WordTrace]
  refine ⟨280171297227849982215471881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186780864818566654810314587 280171297227849982215471881)
  ·
    refine ⟨210128472920887486661603911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280171297227849982215471881 210128472920887486661603911)
    ·
      refine ⟨315192709381331229992405867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210128472920887486661603911 315192709381331229992405867)
      ·
        refine ⟨472789064071996844988608801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315192709381331229992405867 472789064071996844988608801)
        ·
          refine ⟨354591798053997633741456601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472789064071996844988608801 354591798053997633741456601)
          ·
            refine ⟨265943848540498225306092451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354591798053997633741456601 265943848540498225306092451)
            ·
              refine ⟨398915772810747337959138677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265943848540498225306092451 398915772810747337959138677)
              ·
                refine ⟨37398353701007562933669251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398915772810747337959138677 37398353701007562933669251)
                ·
                  refine ⟨56097530551511344400503877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37398353701007562933669251 56097530551511344400503877)
                  ·
                    refine ⟨10518286978408377075094477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56097530551511344400503877 10518286978408377075094477)
                    ·
                      refine ⟨3944357616903141403160429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10518286978408377075094477 3944357616903141403160429)
                      ·
                        rfl

theorem cell23_7681609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4, 3].length) (baseStart_7681609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681609 prefixEnd_7681609 := by exact prefixLift 7681609
  have htrace : WordTrace (prefixWord ++ tailWord_7681609) baseStart_7681609 baseEnd_7681609 := by
    simpa [prefixWord, tailWord_7681609, baseEnd_7681609] using wordTrace_append hprefix tailTrace_7681609
  have hstable : (prefixWord ++ tailWord_7681609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681609).length < 2 ^ (prefixWord ++ tailWord_7681609).sum := by decide
  have hdescent : baseEnd_7681609 < baseStart_7681609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681633 : List Nat := [1, 2, 3, 1, 1, 3, 3, 4, 1, 4]
def baseStart_7681633 : Nat := 118140960795 + 7681633 * 2 ^ 59
def prefixEnd_7681633 : Nat := 4983230072969 + 3 ^ 40 * 7681633 * 2
def baseEnd_7681633 : Nat := 1314789980146283103086773

theorem tailTrace_7681633 : CollatzResearch.WordTrace tailWord_7681633 prefixEnd_7681633 1314789980146283103086773 := by
  unfold tailWord_7681633
  simp only [CollatzResearch.WordTrace]
  refine ⟨280172172579763034314345553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186781448386508689542897035 280172172579763034314345553)
  ·
    refine ⟨210129129434822275735759165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280172172579763034314345553 210129129434822275735759165)
    ·
      refine ⟨78798423538058353400909687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210129129434822275735759165 78798423538058353400909687)
      ·
        refine ⟨118197635307087530101364531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78798423538058353400909687 118197635307087530101364531)
        ·
          refine ⟨177296452960631295152046797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118197635307087530101364531 177296452960631295152046797)
          ·
            refine ⟨66486169860236735682017549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177296452960631295152046797 66486169860236735682017549)
            ·
              refine ⟨24932313697588775880756581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66486169860236735682017549 24932313697588775880756581)
              ·
                refine ⟨4674808818297895477641859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24932313697588775880756581 4674808818297895477641859)
                ·
                  refine ⟨7012213227446843216462789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674808818297895477641859 7012213227446843216462789)
                  ·
                    refine ⟨1314789980146283103086773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7012213227446843216462789 1314789980146283103086773)
                    ·
                      rfl

theorem cell23_7681633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_7681633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681633 prefixEnd_7681633 := by exact prefixLift 7681633
  have htrace : WordTrace (prefixWord ++ tailWord_7681633) baseStart_7681633 baseEnd_7681633 := by
    simpa [prefixWord, tailWord_7681633, baseEnd_7681633] using wordTrace_append hprefix tailTrace_7681633
  have hstable : (prefixWord ++ tailWord_7681633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681633).length < 2 ^ (prefixWord ++ tailWord_7681633).sum := by decide
  have hdescent : baseEnd_7681633 < baseStart_7681633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681659 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 3, 5]
def baseStart_7681659 : Nat := 118140960795 + 7681659 * 2 ^ 59
def prefixEnd_7681659 : Nat := 4983230072969 + 3 ^ 40 * 7681659 * 2
def baseEnd_7681659 : Nat := 1314794430311955402511733

theorem tailTrace_7681659 : CollatzResearch.WordTrace tailWord_7681659 prefixEnd_7681659 1314794430311955402511733 := by
  unfold tailWord_7681659
  simp only [CollatzResearch.WordTrace]
  refine ⟨280173120877668840754792031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186782080585112560503194687 280173120877668840754792031)
  ·
    refine ⟨420259681316503261132188047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280173120877668840754792031 420259681316503261132188047)
    ·
      refine ⟨630389521974754891698282071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420259681316503261132188047 630389521974754891698282071)
      ·
        refine ⟨945584282962132337547423107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630389521974754891698282071 945584282962132337547423107)
        ·
          refine ⟨1418376424443198506321134661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945584282962132337547423107 1418376424443198506321134661)
          ·
            refine ⟨265945579583099719935212749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1418376424443198506321134661 265945579583099719935212749)
            ·
              refine ⟨99729592343662394975704781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265945579583099719935212749 99729592343662394975704781)
              ·
                refine ⟨37398597128873398115889293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99729592343662394975704781 37398597128873398115889293)
                ·
                  refine ⟨14024473923327524293458485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37398597128873398115889293 14024473923327524293458485)
                  ·
                    refine ⟨1314794430311955402511733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14024473923327524293458485 1314794430311955402511733)
                    ·
                      rfl

theorem cell23_7681659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 5].length) (baseStart_7681659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681659 prefixEnd_7681659 := by exact prefixLift 7681659
  have htrace : WordTrace (prefixWord ++ tailWord_7681659) baseStart_7681659 baseEnd_7681659 := by
    simpa [prefixWord, tailWord_7681659, baseEnd_7681659] using wordTrace_append hprefix tailTrace_7681659
  have hstable : (prefixWord ++ tailWord_7681659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681659).length < 2 ^ (prefixWord ++ tailWord_7681659).sum := by decide
  have hdescent : baseEnd_7681659 < baseStart_7681659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681676 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 1, 5]
def baseStart_7681676 : Nat := 118140960795 + 7681676 * 2 ^ 59
def prefixEnd_7681676 : Nat := 4983230072969 + 3 ^ 40 * 7681676 * 2
def baseEnd_7681676 : Nat := 1314797340035664213674207

theorem tailTrace_7681676 : CollatzResearch.WordTrace tailWord_7681676 prefixEnd_7681676 1314797340035664213674207 := by
  unfold tailWord_7681676
  simp only [CollatzResearch.WordTrace]
  refine ⟨140086870459303626329080441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186782493945738168438773921 140086870459303626329080441)
  ·
    refine ⟨105065152844477719746810331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140086870459303626329080441 105065152844477719746810331)
    ·
      refine ⟨157597729266716579620215497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105065152844477719746810331 157597729266716579620215497)
      ·
        refine ⟨118198296950037434715161623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157597729266716579620215497 118198296950037434715161623)
        ·
          refine ⟨177297445425056152072742435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118198296950037434715161623 177297445425056152072742435)
          ·
            refine ⟨265946168137584228109113653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177297445425056152072742435 265946168137584228109113653)
            ·
              refine ⟨24932453262898521385229405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265946168137584228109113653 24932453262898521385229405)
              ·
                refine ⟨9349669973586945519461027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24932453262898521385229405 9349669973586945519461027)
                ·
                  refine ⟨14024504960380418279191541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9349669973586945519461027 14024504960380418279191541)
                  ·
                    refine ⟨1314797340035664213674207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14024504960380418279191541 1314797340035664213674207)
                    ·
                      rfl

theorem cell23_7681676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_7681676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681676 prefixEnd_7681676 := by exact prefixLift 7681676
  have htrace : WordTrace (prefixWord ++ tailWord_7681676) baseStart_7681676 baseEnd_7681676 := by
    simpa [prefixWord, tailWord_7681676, baseEnd_7681676] using wordTrace_append hprefix tailTrace_7681676
  have hstable : (prefixWord ++ tailWord_7681676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681676).length < 2 ^ (prefixWord ++ tailWord_7681676).sum := by decide
  have hdescent : baseEnd_7681676 < baseStart_7681676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681734 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_7681734 : Nat := 118140960795 + 7681734 * 2 ^ 59
def prefixEnd_7681734 : Nat := 4983230072969 + 3 ^ 40 * 7681734 * 2
def baseEnd_7681734 : Nat := 3944421801984953414097355

theorem tailTrace_7681734 : CollatzResearch.WordTrace tailWord_7681734 prefixEnd_7681734 3944421801984953414097355 := by
  unfold tailWord_7681734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8755495511012410267617883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186783904234931419042514837 8755495511012410267617883)
  ·
    refine ⟨13133243266518615401426825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8755495511012410267617883 13133243266518615401426825)
    ·
      refine ⟨9849932449888961551070119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13133243266518615401426825 9849932449888961551070119)
      ·
        refine ⟨14774898674833442326605179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9849932449888961551070119 14774898674833442326605179)
        ·
          refine ⟨22162348012250163489907769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14774898674833442326605179 22162348012250163489907769)
          ·
            refine ⟨16621761009187622617430827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22162348012250163489907769 16621761009187622617430827)
            ·
              refine ⟨24932641513781433926146241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16621761009187622617430827 24932641513781433926146241)
              ·
                refine ⟨18699481135336075444609681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24932641513781433926146241 18699481135336075444609681)
                ·
                  refine ⟨14024610851502056583457261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18699481135336075444609681 14024610851502056583457261)
                  ·
                    refine ⟨5259229069313271218796473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14024610851502056583457261 5259229069313271218796473)
                    ·
                      refine ⟨3944421801984953414097355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5259229069313271218796473 3944421801984953414097355)
                      ·
                        rfl

theorem cell23_7681734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_7681734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681734 prefixEnd_7681734 := by exact prefixLift 7681734
  have htrace : WordTrace (prefixWord ++ tailWord_7681734) baseStart_7681734 baseEnd_7681734 := by
    simpa [prefixWord, tailWord_7681734, baseEnd_7681734] using wordTrace_append hprefix tailTrace_7681734
  have hstable : (prefixWord ++ tailWord_7681734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681734).length < 2 ^ (prefixWord ++ tailWord_7681734).sum := by decide
  have hdescent : baseEnd_7681734 < baseStart_7681734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681741 : List Nat := [1, 6, 2, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_7681741 : Nat := 118140960795 + 7681741 * 2 ^ 59
def prefixEnd_7681741 : Nat := 4983230072969 + 3 ^ 40 * 7681741 * 2
def baseEnd_7681741 : Nat := 3944425396349534886709823

theorem tailTrace_7681741 : CollatzResearch.WordTrace tailWord_7681741 prefixEnd_7681741 3944425396349534886709823 := by
  unfold tailWord_7681741
  simp only [CollatzResearch.WordTrace]
  refine ⟨280176111663371768759277077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186784074442247845839518051 280176111663371768759277077)
  ·
    refine ⟨13133255234220551660591113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 280176111663371768759277077 13133255234220551660591113)
    ·
      refine ⟨9849941425665413745443335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13133255234220551660591113 9849941425665413745443335)
      ·
        refine ⟨14774912138498120618165003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9849941425665413745443335 14774912138498120618165003)
        ·
          refine ⟨22162368207747180927247505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14774912138498120618165003 22162368207747180927247505)
          ·
            refine ⟨16621776155810385695435629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22162368207747180927247505 16621776155810385695435629)
            ·
              refine ⟨6233166058428894635788361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16621776155810385695435629 6233166058428894635788361)
              ·
                refine ⟨4674874543821670976841271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6233166058428894635788361 4674874543821670976841271)
                ·
                  refine ⟨7012311815732506465261907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674874543821670976841271 7012311815732506465261907)
                  ·
                    refine ⟨10518467723598759697892861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7012311815732506465261907 10518467723598759697892861)
                    ·
                      refine ⟨3944425396349534886709823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10518467723598759697892861 3944425396349534886709823)
                      ·
                        rfl

theorem cell23_7681741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_7681741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681741 prefixEnd_7681741 := by exact prefixLift 7681741
  have htrace : WordTrace (prefixWord ++ tailWord_7681741) baseStart_7681741 baseEnd_7681741 := by
    simpa [prefixWord, tailWord_7681741, baseEnd_7681741] using wordTrace_append hprefix tailTrace_7681741
  have hstable : (prefixWord ++ tailWord_7681741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681741).length < 2 ^ (prefixWord ++ tailWord_7681741).sum := by decide
  have hdescent : baseEnd_7681741 < baseStart_7681741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681757 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_7681757 : Nat := 118140960795 + 7681757 * 2 ^ 59
def prefixEnd_7681757 : Nat := 4983230072969 + 3 ^ 40 * 7681757 * 2
def baseEnd_7681757 : Nat := 1314811204013335608036583

theorem tailTrace_7681757 : CollatzResearch.WordTrace tailWord_7681757 prefixEnd_7681757 1314811204013335608036583 := by
  unfold tailWord_7681757
  simp only [CollatzResearch.WordTrace]
  refine ⟨280176695231313803491859525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186784463487542535661239683 280176695231313803491859525)
  ·
    refine ⟨52533130355871338154723661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280176695231313803491859525 52533130355871338154723661)
    ·
      refine ⟨19699923883451751808021373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52533130355871338154723661 19699923883451751808021373)
      ·
        refine ⟨7387471456294406928008015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19699923883451751808021373 7387471456294406928008015)
        ·
          refine ⟨11081207184441610392012023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7387471456294406928008015 11081207184441610392012023)
          ·
            refine ⟨16621810776662415588018035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11081207184441610392012023 16621810776662415588018035)
            ·
              refine ⟨24932716164993623382027053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16621810776662415588018035 24932716164993623382027053)
              ·
                refine ⟨9349768561872608768260145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24932716164993623382027053 9349768561872608768260145)
                ·
                  refine ⟨7012326421404456576195109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9349768561872608768260145 7012326421404456576195109)
                  ·
                    refine ⟨1314811204013335608036583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7012326421404456576195109 1314811204013335608036583)
                    ·
                      rfl

theorem cell23_7681757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_7681757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681757 prefixEnd_7681757 := by exact prefixLift 7681757
  have htrace : WordTrace (prefixWord ++ tailWord_7681757) baseStart_7681757 baseEnd_7681757 := by
    simpa [prefixWord, tailWord_7681757, baseEnd_7681757] using wordTrace_append hprefix tailTrace_7681757
  have hstable : (prefixWord ++ tailWord_7681757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681757).length < 2 ^ (prefixWord ++ tailWord_7681757).sum := by decide
  have hdescent : baseEnd_7681757 < baseStart_7681757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681769 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_7681769 : Nat := 118140960795 + 7681769 * 2 ^ 59
def prefixEnd_7681769 : Nat := 4983230072969 + 3 ^ 40 * 7681769 * 2
def baseEnd_7681769 : Nat := 3944439773807860777159693

theorem tailTrace_7681769 : CollatzResearch.WordTrace tailWord_7681769 prefixEnd_7681769 3944439773807860777159693 := by
  unfold tailWord_7681769
  simp only [CollatzResearch.WordTrace]
  refine ⟨280177132907270329541296361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186784755271513553027530907 280177132907270329541296361)
  ·
    refine ⟨210132849680452747155972271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280177132907270329541296361 210132849680452747155972271)
    ·
      refine ⟨315199274520679120733958407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210132849680452747155972271 315199274520679120733958407)
      ·
        refine ⟨472798911781018681100937611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315199274520679120733958407 472798911781018681100937611)
        ·
          refine ⟨709198367671528021651406417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472798911781018681100937611 709198367671528021651406417)
          ·
            refine ⟨531898775753646016238554813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709198367671528021651406417 531898775753646016238554813)
            ·
              refine ⟨199462040907617256089458055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531898775753646016238554813 199462040907617256089458055)
              ·
                refine ⟨299193061361425884134187083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199462040907617256089458055 299193061361425884134187083)
                ·
                  refine ⟨448789592042138826201280625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299193061361425884134187083 448789592042138826201280625)
                  ·
                    refine ⟨336592194031604119650960469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 448789592042138826201280625 336592194031604119650960469)
                    ·
                      refine ⟨3944439773807860777159693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 336592194031604119650960469 3944439773807860777159693)
                      ·
                        rfl

theorem cell23_7681769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_7681769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681769 prefixEnd_7681769 := by exact prefixLift 7681769
  have htrace : WordTrace (prefixWord ++ tailWord_7681769) baseStart_7681769 baseEnd_7681769 := by
    simpa [prefixWord, tailWord_7681769, baseEnd_7681769] using wordTrace_append hprefix tailTrace_7681769
  have hstable : (prefixWord ++ tailWord_7681769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681769).length < 2 ^ (prefixWord ++ tailWord_7681769).sum := by decide
  have hdescent : baseEnd_7681769 < baseStart_7681769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681806 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_7681806 : Nat := 118140960795 + 7681806 * 2 ^ 59
def prefixEnd_7681806 : Nat := 4983230072969 + 3 ^ 40 * 7681806 * 2
def baseEnd_7681806 : Nat := 3944458772592077132397023

theorem tailTrace_7681806 : CollatzResearch.WordTrace tailWord_7681806 prefixEnd_7681806 3944458772592077132397023 := by
  unfold tailWord_7681806
  simp only [CollatzResearch.WordTrace]
  refine ⟨35022310301017035607549159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186785654938757523240262181 35022310301017035607549159)
  ·
    refine ⟨52533465451525553411323739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35022310301017035607549159 52533465451525553411323739)
    ·
      refine ⟨78800198177288330116985609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52533465451525553411323739 78800198177288330116985609)
      ·
        refine ⟨59100148632966247587739207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78800198177288330116985609 59100148632966247587739207)
        ·
          refine ⟨88650222949449371381608811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59100148632966247587739207 88650222949449371381608811)
          ·
            refine ⟨132975334424174057072413217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88650222949449371381608811 132975334424174057072413217)
            ·
              refine ⟨99731500818130542804309913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132975334424174057072413217 99731500818130542804309913)
              ·
                refine ⟨74798625613597907103232435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99731500818130542804309913 74798625613597907103232435)
                ·
                  refine ⟨112197938420396860654848653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74798625613597907103232435 112197938420396860654848653)
                  ·
                    refine ⟨42074226907648822745568245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112197938420396860654848653 42074226907648822745568245)
                    ·
                      refine ⟨3944458772592077132397023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42074226907648822745568245 3944458772592077132397023)
                      ·
                        rfl

theorem cell23_7681806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_7681806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681806 prefixEnd_7681806 := by exact prefixLift 7681806
  have htrace : WordTrace (prefixWord ++ tailWord_7681806) baseStart_7681806 baseEnd_7681806 := by
    simpa [prefixWord, tailWord_7681806, baseEnd_7681806] using wordTrace_append hprefix tailTrace_7681806
  have hstable : (prefixWord ++ tailWord_7681806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681806).length < 2 ^ (prefixWord ++ tailWord_7681806).sum := by decide
  have hdescent : baseEnd_7681806 < baseStart_7681806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681816 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_7681816 : Nat := 118140960795 + 7681816 * 2 ^ 59
def prefixEnd_7681816 : Nat := 4983230072969 + 3 ^ 40 * 7681816 * 2
def baseEnd_7681816 : Nat := 3944463907398622093271977

theorem tailTrace_7681816 : CollatzResearch.WordTrace tailWord_7681816 prefixEnd_7681816 3944463907398622093271977 := by
  unfold tailWord_7681816
  simp only [CollatzResearch.WordTrace]
  refine ⟨140089423569050028284128651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186785898092066704378838201 140089423569050028284128651)
  ·
    refine ⟨210134135353575042426192977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140089423569050028284128651 210134135353575042426192977)
    ·
      refine ⟨157600601515181281819644733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210134135353575042426192977 157600601515181281819644733)
      ·
        refine ⟨59100225568192980682366775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157600601515181281819644733 59100225568192980682366775)
        ·
          refine ⟨88650338352289471023550163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59100225568192980682366775 88650338352289471023550163)
          ·
            refine ⟨132975507528434206535325245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88650338352289471023550163 132975507528434206535325245)
            ·
              refine ⟨49865815323162827450746967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132975507528434206535325245 49865815323162827450746967)
              ·
                refine ⟨74798722984744241176120451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49865815323162827450746967 74798722984744241176120451)
                ·
                  refine ⟨112198084477116361764180677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74798722984744241176120451 112198084477116361764180677)
                  ·
                    refine ⟨21037140839459317830783877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112198084477116361764180677 21037140839459317830783877)
                    ·
                      refine ⟨3944463907398622093271977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21037140839459317830783877 3944463907398622093271977)
                      ·
                        rfl

theorem cell23_7681816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_7681816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681816 prefixEnd_7681816 := by exact prefixLift 7681816
  have htrace : WordTrace (prefixWord ++ tailWord_7681816) baseStart_7681816 baseEnd_7681816 := by
    simpa [prefixWord, tailWord_7681816, baseEnd_7681816] using wordTrace_append hprefix tailTrace_7681816
  have hstable : (prefixWord ++ tailWord_7681816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681816).length < 2 ^ (prefixWord ++ tailWord_7681816).sum := by decide
  have hdescent : baseEnd_7681816 < baseStart_7681816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681820 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_7681820 : Nat := 118140960795 + 7681820 * 2 ^ 59
def prefixEnd_7681820 : Nat := 4983230072969 + 3 ^ 40 * 7681820 * 2
def baseEnd_7681820 : Nat := 3944465961321240077621959

theorem tailTrace_7681820 : CollatzResearch.WordTrace tailWord_7681820 prefixEnd_7681820 3944465961321240077621959 := by
  unfold tailWord_7681820
  simp only [CollatzResearch.WordTrace]
  refine ⟨140089496515042782625701457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186785995353390376834268609 140089496515042782625701457)
  ·
    refine ⟨105067122386282086969276093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140089496515042782625701457 105067122386282086969276093)
    ·
      refine ⟨39400170894855782613478535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105067122386282086969276093 39400170894855782613478535)
      ·
        refine ⟨59100256342283673920217803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39400170894855782613478535 59100256342283673920217803)
        ·
          refine ⟨88650384513425510880326705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59100256342283673920217803 88650384513425510880326705)
          ·
            refine ⟨66487788385069133160245029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88650384513425510880326705 66487788385069133160245029)
            ·
              refine ⟨12466460322200462467545943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66487788385069133160245029 12466460322200462467545943)
              ·
                refine ⟨18699690483300693701318915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12466460322200462467545943 18699690483300693701318915)
                ·
                  refine ⟨28049535724951040551978373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18699690483300693701318915 28049535724951040551978373)
                  ·
                    refine ⟨5259287948428320103495945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28049535724951040551978373 5259287948428320103495945)
                    ·
                      refine ⟨3944465961321240077621959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5259287948428320103495945 3944465961321240077621959)
                      ·
                        rfl

theorem cell23_7681820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_7681820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681820 prefixEnd_7681820 := by exact prefixLift 7681820
  have htrace : WordTrace (prefixWord ++ tailWord_7681820) baseStart_7681820 baseEnd_7681820 := by
    simpa [prefixWord, tailWord_7681820, baseEnd_7681820] using wordTrace_append hprefix tailTrace_7681820
  have hstable : (prefixWord ++ tailWord_7681820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681820).length < 2 ^ (prefixWord ++ tailWord_7681820).sum := by decide
  have hdescent : baseEnd_7681820 < baseStart_7681820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681854 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_7681854 : Nat := 118140960795 + 7681854 * 2 ^ 59
def prefixEnd_7681854 : Nat := 4983230072969 + 3 ^ 40 * 7681854 * 2
def baseEnd_7681854 : Nat := 3944483419663492944596803

theorem tailTrace_7681854 : CollatzResearch.WordTrace tailWord_7681854 prefixEnd_7681854 3944483419663492944596803 := by
  unfold tailWord_7681854
  simp only [CollatzResearch.WordTrace]
  refine ⟨35022529138995298632267577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186786822074641592705427077 35022529138995298632267577)
  ·
    refine ⟨26266896854246473974200683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35022529138995298632267577 26266896854246473974200683)
    ·
      refine ⟨39400345281369710961301025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26266896854246473974200683 39400345281369710961301025)
      ·
        refine ⟨29550258961027283220975769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39400345281369710961301025 29550258961027283220975769)
        ·
          refine ⟨22162694220770462415731827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29550258961027283220975769 22162694220770462415731827)
          ·
            refine ⟨33244041331155693623597741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22162694220770462415731827 33244041331155693623597741)
            ·
              refine ⟨12466515499183385108849153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33244041331155693623597741 12466515499183385108849153)
              ·
                refine ⟨9349886624387538831636865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12466515499183385108849153 9349886624387538831636865)
                ·
                  refine ⟨7012414968290654123727649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9349886624387538831636865 7012414968290654123727649)
                  ·
                    refine ⟨5259311226217990592795737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7012414968290654123727649 5259311226217990592795737)
                    ·
                      refine ⟨3944483419663492944596803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5259311226217990592795737 3944483419663492944596803)
                      ·
                        rfl

theorem cell23_7681854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_7681854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681854 prefixEnd_7681854 := by exact prefixLift 7681854
  have htrace : WordTrace (prefixWord ++ tailWord_7681854) baseStart_7681854 baseEnd_7681854 := by
    simpa [prefixWord, tailWord_7681854, baseEnd_7681854] using wordTrace_append hprefix tailTrace_7681854
  have hstable : (prefixWord ++ tailWord_7681854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681854).length < 2 ^ (prefixWord ++ tailWord_7681854).sum := by decide
  have hdescent : baseEnd_7681854 < baseStart_7681854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681863 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 1, 7, 2]
def baseStart_7681863 : Nat := 118140960795 + 7681863 * 2 ^ 59
def prefixEnd_7681863 : Nat := 4983230072969 + 3 ^ 40 * 7681863 * 2
def baseEnd_7681863 : Nat := 3944488040989383409384261

theorem tailTrace_7681863 : CollatzResearch.WordTrace tailWord_7681863 prefixEnd_7681863 3944488040989383409384261 := by
  unfold tailWord_7681863
  simp only [CollatzResearch.WordTrace]
  refine ⟨280180561368929783595218243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186787040912619855730145495 280180561368929783595218243)
  ·
    refine ⟨420270842053394675392827365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280180561368929783595218243 420270842053394675392827365)
    ·
      refine ⟨78800782885011501636155131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420270842053394675392827365 78800782885011501636155131)
      ·
        refine ⟨118201174327517252454232697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78800782885011501636155131 118201174327517252454232697)
        ·
          refine ⟨88650880745637939340674523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118201174327517252454232697 88650880745637939340674523)
          ·
            refine ⟨132976321118456909011011785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88650880745637939340674523 132976321118456909011011785)
            ·
              refine ⟨99732240838842681758258839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132976321118456909011011785 99732240838842681758258839)
              ·
                refine ⟨149598361258264022637388259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99732240838842681758258839 149598361258264022637388259)
                ·
                  refine ⟨224397541887396033956082389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149598361258264022637388259 224397541887396033956082389)
                  ·
                    refine ⟨5259317387985844545845681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 224397541887396033956082389 5259317387985844545845681)
                    ·
                      refine ⟨3944488040989383409384261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5259317387985844545845681 3944488040989383409384261)
                      ·
                        rfl

theorem cell23_7681863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_7681863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681863 prefixEnd_7681863 := by exact prefixLift 7681863
  have htrace : WordTrace (prefixWord ++ tailWord_7681863) baseStart_7681863 baseEnd_7681863 := by
    simpa [prefixWord, tailWord_7681863, baseEnd_7681863] using wordTrace_append hprefix tailTrace_7681863
  have hstable : (prefixWord ++ tailWord_7681863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681863).length < 2 ^ (prefixWord ++ tailWord_7681863).sum := by decide
  have hdescent : baseEnd_7681863 < baseStart_7681863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681866 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_7681866 : Nat := 118140960795 + 7681866 * 2 ^ 59
def prefixEnd_7681866 : Nat := 4983230072969 + 3 ^ 40 * 7681866 * 2
def baseEnd_7681866 : Nat := 3944489581431346897646747

theorem tailTrace_7681866 : CollatzResearch.WordTrace tailWord_7681866 prefixEnd_7681866 3944489581431346897646747 := by
  unfold tailWord_7681866
  simp only [CollatzResearch.WordTrace]
  refine ⟨70045167696979728776894363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186787113858612610071718301 70045167696979728776894363)
  ·
    refine ⟨105067751545469593165341545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70045167696979728776894363 105067751545469593165341545)
    ·
      refine ⟨78800813659102194874006159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105067751545469593165341545 78800813659102194874006159)
      ·
        refine ⟨118201220488653292311009239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78800813659102194874006159 118201220488653292311009239)
        ·
          refine ⟨177301830732979938466513859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118201220488653292311009239 177301830732979938466513859)
          ·
            refine ⟨265952746099469907699770789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177301830732979938466513859 265952746099469907699770789)
            ·
              refine ⟨49866139893650607693707023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265952746099469907699770789 49866139893650607693707023)
              ·
                refine ⟨74799209840475911540560535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49866139893650607693707023 74799209840475911540560535)
                ·
                  refine ⟨112198814760713867310840803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74799209840475911540560535 112198814760713867310840803)
                  ·
                    refine ⟨168298222141070800966261205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112198814760713867310840803 168298222141070800966261205)
                    ·
                      refine ⟨3944489581431346897646747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168298222141070800966261205 3944489581431346897646747)
                      ·
                        rfl

theorem cell23_7681866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_7681866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681866 prefixEnd_7681866 := by exact prefixLift 7681866
  have htrace : WordTrace (prefixWord ++ tailWord_7681866) baseStart_7681866 baseEnd_7681866 := by
    simpa [prefixWord, tailWord_7681866, baseEnd_7681866] using wordTrace_append hprefix tailTrace_7681866
  have hstable : (prefixWord ++ tailWord_7681866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681866).length < 2 ^ (prefixWord ++ tailWord_7681866).sum := by decide
  have hdescent : baseEnd_7681866 < baseStart_7681866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681893 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_7681893 : Nat := 118140960795 + 7681893 * 2 ^ 59
def prefixEnd_7681893 : Nat := 4983230072969 + 3 ^ 40 * 7681893 * 2
def baseEnd_7681893 : Nat := 3944503445409018292009123

theorem tailTrace_7681893 : CollatzResearch.WordTrace tailWord_7681893 prefixEnd_7681893 3944503445409018292009123 := by
  unfold tailWord_7681893
  simp only [CollatzResearch.WordTrace]
  refine ⟨280181655558821098718810333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186787770372547399145873555 280181655558821098718810333)
  ·
    refine ⟨105068120834557912019553875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280181655558821098718810333 105068120834557912019553875)
    ·
      refine ⟨157602181251836868029330813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105068120834557912019553875 157602181251836868029330813)
      ·
        refine ⟨59100817969438825510999055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157602181251836868029330813 59100817969438825510999055)
        ·
          refine ⟨88651226954158238266498583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59100817969438825510999055 88651226954158238266498583)
          ·
            refine ⟨132976840431237357399747875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88651226954158238266498583 132976840431237357399747875)
            ·
              refine ⟨199465260646856036099621813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132976840431237357399747875 199465260646856036099621813)
              ·
                refine ⟨18699868185642753384339545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199465260646856036099621813 18699868185642753384339545)
                ·
                  refine ⟨14024901139232065038254659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18699868185642753384339545 14024901139232065038254659)
                  ·
                    refine ⟨21037351708848097557381989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14024901139232065038254659 21037351708848097557381989)
                    ·
                      refine ⟨3944503445409018292009123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21037351708848097557381989 3944503445409018292009123)
                      ·
                        rfl

theorem cell23_7681893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_7681893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681893 prefixEnd_7681893 := by exact prefixLift 7681893
  have htrace : WordTrace (prefixWord ++ tailWord_7681893) baseStart_7681893 baseEnd_7681893 := by
    simpa [prefixWord, tailWord_7681893, baseEnd_7681893] using wordTrace_append hprefix tailTrace_7681893
  have hstable : (prefixWord ++ tailWord_7681893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681893).length < 2 ^ (prefixWord ++ tailWord_7681893).sum := by decide
  have hdescent : baseEnd_7681893 < baseStart_7681893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681936 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_7681936 : Nat := 118140960795 + 7681936 * 2 ^ 59
def prefixEnd_7681936 : Nat := 4983230072969 + 3 ^ 40 * 7681936 * 2
def baseEnd_7681936 : Nat := 3944525525077161623771425

theorem tailTrace_7681936 : CollatzResearch.WordTrace tailWord_7681936 prefixEnd_7681936 3944525525077161623771425 := by
  unfold tailWord_7681936
  simp only [CollatzResearch.WordTrace]
  refine ⟨140091611948832658531312831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186788815931776878041750441 140091611948832658531312831)
  ·
    refine ⟨210137417923248987796969247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140091611948832658531312831 210137417923248987796969247)
    ·
      refine ⟨315206126884873481695453871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210137417923248987796969247 315206126884873481695453871)
      ·
        refine ⟨472809190327310222543180807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315206126884873481695453871 472809190327310222543180807)
        ·
          refine ⟨709213785490965333814771211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472809190327310222543180807 709213785490965333814771211)
          ·
            refine ⟨1063820678236448000722156817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709213785490965333814771211 1063820678236448000722156817)
            ·
              refine ⟨797865508677336000541617613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063820678236448000722156817 797865508677336000541617613)
              ·
                refine ⟨299199565754001000203106605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 797865508677336000541617613 299199565754001000203106605)
                ·
                  refine ⟨112199837157750375076164977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299199565754001000203106605 112199837157750375076164977)
                  ·
                    refine ⟨84149877868312781307123733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112199837157750375076164977 84149877868312781307123733)
                    ·
                      refine ⟨3944525525077161623771425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84149877868312781307123733 3944525525077161623771425)
                      ·
                        rfl

theorem cell23_7681936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_7681936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681936 prefixEnd_7681936 := by exact prefixLift 7681936
  have htrace : WordTrace (prefixWord ++ tailWord_7681936) baseStart_7681936 baseEnd_7681936 := by
    simpa [prefixWord, tailWord_7681936, baseEnd_7681936] using wordTrace_append hprefix tailTrace_7681936
  have hstable : (prefixWord ++ tailWord_7681936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681936).length < 2 ^ (prefixWord ++ tailWord_7681936).sum := by decide
  have hdescent : baseEnd_7681936 < baseStart_7681936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681983 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 4]
def baseStart_7681983 : Nat := 118140960795 + 7681983 * 2 ^ 59
def prefixEnd_7681983 : Nat := 4983230072969 + 3 ^ 40 * 7681983 * 2
def baseEnd_7681983 : Nat := 3944549658667922939883709

theorem tailTrace_7681983 : CollatzResearch.WordTrace tailWord_7681983 prefixEnd_7681983 3944549658667922939883709 := by
  unfold tailWord_7681983
  simp only [CollatzResearch.WordTrace]
  refine ⟨280184938128495044089586603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186789958752330029393057735 280184938128495044089586603)
  ·
    refine ⟨420277407192742566134379905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280184938128495044089586603 420277407192742566134379905)
    ·
      refine ⟨315208055394556924600784929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420277407192742566134379905 315208055394556924600784929)
      ·
        refine ⟨236406041545917693450588697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315208055394556924600784929 236406041545917693450588697)
        ·
          refine ⟨177304531159438270087941523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236406041545917693450588697 177304531159438270087941523)
          ·
            refine ⟨265956796739157405131912285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177304531159438270087941523 265956796739157405131912285)
            ·
              refine ⟨99733798777184026924467107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265956796739157405131912285 99733798777184026924467107)
              ·
                refine ⟨149600698165776040386700661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99733798777184026924467107 149600698165776040386700661)
                ·
                  refine ⟨14025065453041503786253187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149600698165776040386700661 14025065453041503786253187)
                  ·
                    refine ⟨21037598179562255679379781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14025065453041503786253187 21037598179562255679379781)
                    ·
                      refine ⟨3944549658667922939883709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21037598179562255679379781 3944549658667922939883709)
                      ·
                        rfl

theorem cell23_7681983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_7681983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681983 prefixEnd_7681983 := by exact prefixLift 7681983
  have htrace : WordTrace (prefixWord ++ tailWord_7681983) baseStart_7681983 baseEnd_7681983 := by
    simpa [prefixWord, tailWord_7681983, baseEnd_7681983] using wordTrace_append hprefix tailTrace_7681983
  have hstable : (prefixWord ++ tailWord_7681983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681983).length < 2 ^ (prefixWord ++ tailWord_7681983).sum := by decide
  have hdescent : baseEnd_7681983 < baseStart_7681983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682017 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 1, 1, 4]
def baseStart_7682017 : Nat := 118140960795 + 7682017 * 2 ^ 59
def prefixEnd_7682017 : Nat := 4983230072969 + 3 ^ 40 * 7682017 * 2
def baseEnd_7682017 : Nat := 3944567117010175806858553

theorem tailTrace_7682017 : CollatzResearch.WordTrace tailWord_7682017 prefixEnd_7682017 3944567117010175806858553 := by
  unfold tailWord_7682017
  simp only [CollatzResearch.WordTrace]
  refine ⟨280186178210371867896324305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186790785473581245264216203 280186178210371867896324305)
  ·
    refine ⟨210139633657778900922243229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280186178210371867896324305 210139633657778900922243229)
    ·
      refine ⟨78802362621667087845841211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210139633657778900922243229 78802362621667087845841211)
      ·
        refine ⟨118203543932500631768761817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78802362621667087845841211 118203543932500631768761817)
        ·
          refine ⟨88652657949375473826571363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118203543932500631768761817 88652657949375473826571363)
          ·
            refine ⟨132978986924063210739857045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88652657949375473826571363 132978986924063210739857045)
            ·
              refine ⟨6233390012065463003430799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132978986924063210739857045 6233390012065463003430799)
              ·
                refine ⟨9350085018098194505146199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6233390012065463003430799 9350085018098194505146199)
                ·
                  refine ⟨14025127527147291757719299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9350085018098194505146199 14025127527147291757719299)
                  ·
                    refine ⟨21037691290720937636578949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14025127527147291757719299 21037691290720937636578949)
                    ·
                      refine ⟨3944567117010175806858553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21037691290720937636578949 3944567117010175806858553)
                      ·
                        rfl

theorem cell23_7682017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_7682017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682017 prefixEnd_7682017 := by exact prefixLift 7682017
  have htrace : WordTrace (prefixWord ++ tailWord_7682017) baseStart_7682017 baseEnd_7682017 := by
    simpa [prefixWord, tailWord_7682017, baseEnd_7682017] using wordTrace_append hprefix tailTrace_7682017
  have hstable : (prefixWord ++ tailWord_7682017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682017).length < 2 ^ (prefixWord ++ tailWord_7682017).sum := by decide
  have hdescent : baseEnd_7682017 < baseStart_7682017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682073 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 4]
def baseStart_7682073 : Nat := 118140960795 + 7682073 * 2 ^ 59
def prefixEnd_7682073 : Nat := 4983230072969 + 3 ^ 40 * 7682073 * 2
def baseEnd_7682073 : Nat := 3944595871926827587758295

theorem tailTrace_7682073 : CollatzResearch.WordTrace tailWord_7682073 prefixEnd_7682073 3944595871926827587758295 := by
  unfold tailWord_7682073
  simp only [CollatzResearch.WordTrace]
  refine ⟨280188220698168989460362873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186792147132112659640241915 280188220698168989460362873)
  ·
    refine ⟨210141165523626742095272155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280188220698168989460362873 210141165523626742095272155)
    ·
      refine ⟨315211748285440113142908233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210141165523626742095272155 315211748285440113142908233)
      ·
        refine ⟨236408811214080084857181175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315211748285440113142908233 236408811214080084857181175)
        ·
          refine ⟨354613216821120127285771763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236408811214080084857181175 354613216821120127285771763)
          ·
            refine ⟨531919825231680190928657645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354613216821120127285771763 531919825231680190928657645)
            ·
              refine ⟨199469934461880071598246617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531919825231680190928657645 199469934461880071598246617)
              ·
                refine ⟨149602450846410053698684963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199469934461880071598246617 149602450846410053698684963)
                ·
                  refine ⟨224403676269615080548027445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149602450846410053698684963 224403676269615080548027445)
                  ·
                    refine ⟨21037844650276413801377573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 224403676269615080548027445 21037844650276413801377573)
                    ·
                      refine ⟨3944595871926827587758295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21037844650276413801377573 3944595871926827587758295)
                      ·
                        rfl

theorem cell23_7682073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_7682073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682073 prefixEnd_7682073 := by exact prefixLift 7682073
  have htrace : WordTrace (prefixWord ++ tailWord_7682073) baseStart_7682073 baseEnd_7682073 := by
    simpa [prefixWord, tailWord_7682073, baseEnd_7682073] using wordTrace_append hprefix tailTrace_7682073
  have hstable : (prefixWord ++ tailWord_7682073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682073).length < 2 ^ (prefixWord ++ tailWord_7682073).sum := by decide
  have hdescent : baseEnd_7682073 < baseStart_7682073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682157 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_7682157 : Nat := 118140960795 + 7682157 * 2 ^ 59
def prefixEnd_7682157 : Nat := 4983230072969 + 3 ^ 40 * 7682157 * 2
def baseEnd_7682157 : Nat := 3944639004301805259107909

theorem tailTrace_7682157 : CollatzResearch.WordTrace tailWord_7682157 prefixEnd_7682157 3944639004301805259107909 := by
  unfold tailWord_7682157
  simp only [CollatzResearch.WordTrace]
  refine ⟨280191284429864671806420725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186794189619909781204280483 280191284429864671806420725)
  ·
    refine ⟨26267932915299812981851943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280191284429864671806420725 26267932915299812981851943)
    ·
      refine ⟨39401899372949719472777915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26267932915299812981851943 39401899372949719472777915)
      ·
        refine ⟨59102849059424579209166873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39401899372949719472777915 59102849059424579209166873)
        ·
          refine ⟨44327136794568434406875155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59102849059424579209166873 44327136794568434406875155)
          ·
            refine ⟨66490705191852651610312733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44327136794568434406875155 66490705191852651610312733)
            ·
              refine ⟨24934014446944744353867275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66490705191852651610312733 24934014446944744353867275)
              ·
                refine ⟨37401021670417116530800913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24934014446944744353867275 37401021670417116530800913)
                ·
                  refine ⟨28050766252812837398100685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37401021670417116530800913 28050766252812837398100685)
                  ·
                    refine ⟨10519037344804814024287757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28050766252812837398100685 10519037344804814024287757)
                    ·
                      refine ⟨3944639004301805259107909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10519037344804814024287757 3944639004301805259107909)
                      ·
                        rfl

theorem cell23_7682157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_7682157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682157 prefixEnd_7682157 := by exact prefixLift 7682157
  have htrace : WordTrace (prefixWord ++ tailWord_7682157) baseStart_7682157 baseEnd_7682157 := by
    simpa [prefixWord, tailWord_7682157, baseEnd_7682157] using wordTrace_append hprefix tailTrace_7682157
  have hstable : (prefixWord ++ tailWord_7682157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682157).length < 2 ^ (prefixWord ++ tailWord_7682157).sum := by decide
  have hdescent : baseEnd_7682157 < baseStart_7682157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682177 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 1, 7]
def baseStart_7682177 : Nat := 118140960795 + 7682177 * 2 ^ 59
def prefixEnd_7682177 : Nat := 4983230072969 + 3 ^ 40 * 7682177 * 2
def baseEnd_7682177 : Nat := 1314883091304965060285939

theorem tailTrace_7682177 : CollatzResearch.WordTrace tailWord_7682177 prefixEnd_7682177 1314883091304965060285939 := by
  unfold tailWord_7682177
  simp only [CollatzResearch.WordTrace]
  refine ⟨280192013889792215222148785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186794675926528143481432523 280192013889792215222148785)
  ·
    refine ⟨210144010417344161416611589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280192013889792215222148785 210144010417344161416611589)
    ·
      refine ⟨39402001953252030265614673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210144010417344161416611589 39402001953252030265614673)
      ·
        refine ⟨29551501464939022699211005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39402001953252030265614673 29551501464939022699211005)
        ·
          refine ⟨11081813049352133512204127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29551501464939022699211005 11081813049352133512204127)
          ·
            refine ⟨16622719574028200268306191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11081813049352133512204127 16622719574028200268306191)
            ·
              refine ⟨24934079361042300402459287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16622719574028200268306191 24934079361042300402459287)
              ·
                refine ⟨37401119041563450603688931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24934079361042300402459287 37401119041563450603688931)
                ·
                  refine ⟨56101678562345175905533397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37401119041563450603688931 56101678562345175905533397)
                  ·
                    refine ⟨1314883091304965060285939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56101678562345175905533397 1314883091304965060285939)
                    ·
                      rfl

theorem cell23_7682177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_7682177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682177 prefixEnd_7682177 := by exact prefixLift 7682177
  have htrace : WordTrace (prefixWord ++ tailWord_7682177) baseStart_7682177 baseEnd_7682177 := by
    simpa [prefixWord, tailWord_7682177, baseEnd_7682177] using wordTrace_append hprefix tailTrace_7682177
  have hstable : (prefixWord ++ tailWord_7682177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682177).length < 2 ^ (prefixWord ++ tailWord_7682177).sum := by decide
  have hdescent : baseEnd_7682177 < baseStart_7682177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682197 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 4, 4, 2]
def baseStart_7682197 : Nat := 118140960795 + 7682197 * 2 ^ 59
def prefixEnd_7682197 : Nat := 4983230072969 + 3 ^ 40 * 7682197 * 2
def baseEnd_7682197 : Nat := 3944659543527985102607725

theorem tailTrace_7682197 : CollatzResearch.WordTrace tailWord_7682197 prefixEnd_7682197 3944659543527985102607725 := by
  unfold tailWord_7682197
  simp only [CollatzResearch.WordTrace]
  refine ⟨280192743349719758637876845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186795162233146505758584563 280192743349719758637876845)
  ·
    refine ⟨105072278756144909489203817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280192743349719758637876845 105072278756144909489203817)
    ·
      refine ⟨78804209067108682116902863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105072278756144909489203817 78804209067108682116902863)
      ·
        refine ⟨118206313600663023175354295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78804209067108682116902863 118206313600663023175354295)
        ·
          refine ⟨177309470400994534763031443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118206313600663023175354295 177309470400994534763031443)
          ·
            refine ⟨265964205601491802144547165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177309470400994534763031443 265964205601491802144547165)
            ·
              refine ⟨99736577100559425804205187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265964205601491802144547165 99736577100559425804205187)
              ·
                refine ⟨149604865650839138706307781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99736577100559425804205187 149604865650839138706307781)
                ·
                  refine ⟨28050912309532338507432709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149604865650839138706307781 28050912309532338507432709)
                  ·
                    refine ⟨5259546058037313470143633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28050912309532338507432709 5259546058037313470143633)
                    ·
                      refine ⟨3944659543527985102607725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5259546058037313470143633 3944659543527985102607725)
                      ·
                        rfl

theorem cell23_7682197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_7682197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682197 prefixEnd_7682197 := by exact prefixLift 7682197
  have htrace : WordTrace (prefixWord ++ tailWord_7682197) baseStart_7682197 baseEnd_7682197 := by
    simpa [prefixWord, tailWord_7682197, baseEnd_7682197] using wordTrace_append hprefix tailTrace_7682197
  have hstable : (prefixWord ++ tailWord_7682197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682197).length < 2 ^ (prefixWord ++ tailWord_7682197).sum := by decide
  have hdescent : baseEnd_7682197 < baseStart_7682197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682258 : List Nat := [3, 2, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_7682258 : Nat := 118140960795 + 7682258 * 2 ^ 59
def prefixEnd_7682258 : Nat := 4983230072969 + 3 ^ 40 * 7682258 * 2
def baseEnd_7682258 : Nat := 1314896955282636454648315

theorem tailTrace_7682258 : CollatzResearch.WordTrace tailWord_7682258 prefixEnd_7682258 1314896955282636454648315 := by
  unfold tailWord_7682258
  simp only [CollatzResearch.WordTrace]
  refine ⟨70048742050624691513961857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186796645468332510703898285 70048742050624691513961857)
  ·
    refine ⟨52536556537968518635471393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70048742050624691513961857 52536556537968518635471393)
    ·
      refine ⟨39402417403476388976603545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52536556537968518635471393 39402417403476388976603545)
      ·
        refine ⟨29551813052607291732452659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39402417403476388976603545 29551813052607291732452659)
        ·
          refine ⟨44327719578910937598678989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29551813052607291732452659 44327719578910937598678989)
          ·
            refine ⟨16622894842091601599504621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44327719578910937598678989 16622894842091601599504621)
            ·
              refine ⟨6233585565784350599814233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16622894842091601599504621 6233585565784350599814233)
              ·
                refine ⟨4675189174338262949860675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6233585565784350599814233 4675189174338262949860675)
                ·
                  refine ⟨7012783761507394424791013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675189174338262949860675 7012783761507394424791013)
                  ·
                    refine ⟨1314896955282636454648315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7012783761507394424791013 1314896955282636454648315)
                    ·
                      rfl

theorem cell23_7682258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_7682258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682258 prefixEnd_7682258 := by exact prefixLift 7682258
  have htrace : WordTrace (prefixWord ++ tailWord_7682258) baseStart_7682258 baseEnd_7682258 := by
    simpa [prefixWord, tailWord_7682258, baseEnd_7682258] using wordTrace_append hprefix tailTrace_7682258
  have hstable : (prefixWord ++ tailWord_7682258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682258).length < 2 ^ (prefixWord ++ tailWord_7682258).sum := by decide
  have hdescent : baseEnd_7682258 < baseStart_7682258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682297 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 4, 4]
def baseStart_7682297 : Nat := 118140960795 + 7682297 * 2 ^ 59
def prefixEnd_7682297 : Nat := 4983230072969 + 3 ^ 40 * 7682297 * 2
def baseEnd_7682297 : Nat := 1314903630531144903785755

theorem tailTrace_7682297 : CollatzResearch.WordTrace tailWord_7682297 prefixEnd_7682297 1314903630531144903785755 := by
  unfold tailWord_7682297
  simp only [CollatzResearch.WordTrace]
  refine ⟨280196390649357475716517145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186797593766238317144344763 280196390649357475716517145)
  ·
    refine ⟨210147292987018106787387859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280196390649357475716517145 210147292987018106787387859)
    ·
      refine ⟨315220939480527160181081789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210147292987018106787387859 315220939480527160181081789)
      ·
        refine ⟨118207852305197685067905671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315220939480527160181081789 118207852305197685067905671)
        ·
          refine ⟨177311778457796527601858507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118207852305197685067905671 177311778457796527601858507)
          ·
            refine ⟨265967667686694791402787761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177311778457796527601858507 265967667686694791402787761)
            ·
              refine ⟨199475750765021093552090821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265967667686694791402787761 199475750765021093552090821)
              ·
                refine ⟨37401703268441455041017029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199475750765021093552090821 37401703268441455041017029)
                ·
                  refine ⟨7012819362832772820190693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37401703268441455041017029 7012819362832772820190693)
                  ·
                    refine ⟨1314903630531144903785755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7012819362832772820190693 1314903630531144903785755)
                    ·
                      rfl

theorem cell23_7682297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 4].length) (baseStart_7682297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682297 prefixEnd_7682297 := by exact prefixLift 7682297
  have htrace : WordTrace (prefixWord ++ tailWord_7682297) baseStart_7682297 baseEnd_7682297 := by
    simpa [prefixWord, tailWord_7682297, baseEnd_7682297] using wordTrace_append hprefix tailTrace_7682297
  have hstable : (prefixWord ++ tailWord_7682297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682297).length < 2 ^ (prefixWord ++ tailWord_7682297).sum := by decide
  have hdescent : baseEnd_7682297 < baseStart_7682297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682314 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 2, 4]
def baseStart_7682314 : Nat := 118140960795 + 7682314 * 2 ^ 59
def prefixEnd_7682314 : Nat := 4983230072969 + 3 ^ 40 * 7682314 * 2
def baseEnd_7682314 : Nat := 1314906540254853714948229

theorem tailTrace_7682314 : CollatzResearch.WordTrace tailWord_7682314 prefixEnd_7682314 1314906540254853714948229 := by
  unfold tailWord_7682314
  simp only [CollatzResearch.WordTrace]
  refine ⟨70049252672573971904971499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186798007126863925079923997 70049252672573971904971499)
  ·
    refine ⟨105073879008860957857457249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70049252672573971904971499 105073879008860957857457249)
    ·
      refine ⟨78805409256645718393092937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105073879008860957857457249 78805409256645718393092937)
      ·
        refine ⟨59104056942484288794819703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78805409256645718393092937 59104056942484288794819703)
        ·
          refine ⟨88656085413726433192229555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59104056942484288794819703 88656085413726433192229555)
          ·
            refine ⟨132984128120589649788344333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88656085413726433192229555 132984128120589649788344333)
            ·
              refine ⟨49869048045221118670629125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132984128120589649788344333 49869048045221118670629125)
              ·
                refine ⟨9350446508478959750742961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49869048045221118670629125 9350446508478959750742961)
                ·
                  refine ⟨7012834881359219813057221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9350446508478959750742961 7012834881359219813057221)
                  ·
                    refine ⟨1314906540254853714948229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7012834881359219813057221 1314906540254853714948229)
                    ·
                      rfl

theorem cell23_7682314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_7682314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682314 prefixEnd_7682314 := by exact prefixLift 7682314
  have htrace : WordTrace (prefixWord ++ tailWord_7682314) baseStart_7682314 baseEnd_7682314 := by
    simpa [prefixWord, tailWord_7682314, baseEnd_7682314] using wordTrace_append hprefix tailTrace_7682314
  have hstable : (prefixWord ++ tailWord_7682314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682314).length < 2 ^ (prefixWord ++ tailWord_7682314).sum := by decide
  have hdescent : baseEnd_7682314 < baseStart_7682314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682327 : List Nat := [1, 1, 3, 4, 1, 2, 3, 8]
def baseStart_7682327 : Nat := 118140960795 + 7682327 * 2 ^ 59
def prefixEnd_7682327 : Nat := 4983230072969 + 3 ^ 40 * 7682327 * 2
def baseEnd_7682327 : Nat := 146100973926409984962301

theorem tailTrace_7682327 : CollatzResearch.WordTrace tailWord_7682327 prefixEnd_7682327 146100973926409984962301 := by
  unfold tailWord_7682327
  simp only [CollatzResearch.WordTrace]
  refine ⟨280197484839248790840109235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186798323226165860560072823 280197484839248790840109235)
  ·
    refine ⟨420296227258873186260163853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280197484839248790840109235 420296227258873186260163853)
    ·
      refine ⟨157611085222077444847561445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420296227258873186260163853 157611085222077444847561445)
      ·
        refine ⟨29552078479139520908917771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157611085222077444847561445 29552078479139520908917771)
        ·
          refine ⟨44328117718709281363376657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29552078479139520908917771 44328117718709281363376657)
          ·
            refine ⟨33246088289031961022532493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44328117718709281363376657 33246088289031961022532493)
            ·
              refine ⟨12467283108386985383449685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33246088289031961022532493 12467283108386985383449685)
              ·
                refine ⟨146100973926409984962301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12467283108386985383449685 146100973926409984962301)
                ·
                  rfl

theorem cell23_7682327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 8].length) (baseStart_7682327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682327 prefixEnd_7682327 := by exact prefixLift 7682327
  have htrace : WordTrace (prefixWord ++ tailWord_7682327) baseStart_7682327 baseEnd_7682327 := by
    simpa [prefixWord, tailWord_7682327, baseEnd_7682327] using wordTrace_append hprefix tailTrace_7682327
  have hstable : (prefixWord ++ tailWord_7682327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682327).length < 2 ^ (prefixWord ++ tailWord_7682327).sum := by decide
  have hdescent : baseEnd_7682327 < baseStart_7682327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682338 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_7682338 : Nat := 118140960795 + 7682338 * 2 ^ 59
def prefixEnd_7682338 : Nat := 4983230072969 + 3 ^ 40 * 7682338 * 2
def baseEnd_7682338 : Nat := 3944731944300269050944577

theorem tailTrace_7682338 : CollatzResearch.WordTrace tailWord_7682338 prefixEnd_7682338 3944731944300269050944577 := by
  unfold tailWord_7682338
  simp only [CollatzResearch.WordTrace]
  refine ⟨70049471510552234929689917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186798590694805959812506445 70049471510552234929689917)
  ·
    refine ⟨26268551816457088098633719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70049471510552234929689917 26268551816457088098633719)
    ·
      refine ⟨39402827724685632147950579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26268551816457088098633719 39402827724685632147950579)
      ·
        refine ⟨59104241587028448221925869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39402827724685632147950579 59104241587028448221925869)
        ·
          refine ⟨22164090595135668083222201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59104241587028448221925869 22164090595135668083222201)
          ·
            refine ⟨16623067946351751062416651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22164090595135668083222201 16623067946351751062416651)
            ·
              refine ⟨24934601919527626593624977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16623067946351751062416651 24934601919527626593624977)
              ·
                refine ⟨18700951439645719945218733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24934601919527626593624977 18700951439645719945218733)
                ·
                  refine ⟨7012856789867144979457025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18700951439645719945218733 7012856789867144979457025)
                  ·
                    refine ⟨5259642592400358734592769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7012856789867144979457025 5259642592400358734592769)
                    ·
                      refine ⟨3944731944300269050944577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5259642592400358734592769 3944731944300269050944577)
                      ·
                        rfl

theorem cell23_7682338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_7682338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682338 prefixEnd_7682338 := by exact prefixLift 7682338
  have htrace : WordTrace (prefixWord ++ tailWord_7682338) baseStart_7682338 baseEnd_7682338 := by
    simpa [prefixWord, tailWord_7682338, baseEnd_7682338] using wordTrace_append hprefix tailTrace_7682338
  have hstable : (prefixWord ++ tailWord_7682338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682338).length < 2 ^ (prefixWord ++ tailWord_7682338).sum := by decide
  have hdescent : baseEnd_7682338 < baseStart_7682338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682371 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 2, 1, 3]
def baseStart_7682371 : Nat := 118140960795 + 7682371 * 2 ^ 59
def prefixEnd_7682371 : Nat := 4983230072969 + 3 ^ 40 * 7682371 * 2
def baseEnd_7682371 : Nat := 3944748889161867421831925

theorem tailTrace_7682371 : CollatzResearch.WordTrace tailWord_7682371 prefixEnd_7682371 3944748889161867421831925 := by
  unfold tailWord_7682371
  simp only [CollatzResearch.WordTrace]
  refine ⟨280199089651089386354710967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186799393100726257569807311 280199089651089386354710967)
  ·
    refine ⟨420298634476634079532066451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280199089651089386354710967 420298634476634079532066451)
    ·
      refine ⟨630447951714951119298099677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420298634476634079532066451 630447951714951119298099677)
      ·
        refine ⟨236417981893106669736787379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 630447951714951119298099677 236417981893106669736787379)
        ·
          refine ⟨354626972839660004605181069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236417981893106669736787379 354626972839660004605181069)
          ·
            refine ⟨132985114814872501726942901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354626972839660004605181069 132985114814872501726942901)
            ·
              refine ⟨12467354513894297036900897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132985114814872501726942901 12467354513894297036900897)
              ·
                refine ⟨9350515885420722777675673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12467354513894297036900897 9350515885420722777675673)
                ·
                  refine ⟨7012886914065542083256755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9350515885420722777675673 7012886914065542083256755)
                  ·
                    refine ⟨10519330371098313124885133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7012886914065542083256755 10519330371098313124885133)
                    ·
                      refine ⟨3944748889161867421831925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10519330371098313124885133 3944748889161867421831925)
                      ·
                        rfl

theorem cell23_7682371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_7682371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682371 prefixEnd_7682371 := by exact prefixLift 7682371
  have htrace : WordTrace (prefixWord ++ tailWord_7682371) baseStart_7682371 baseEnd_7682371 := by
    simpa [prefixWord, tailWord_7682371, baseEnd_7682371] using wordTrace_append hprefix tailTrace_7682371
  have hstable : (prefixWord ++ tailWord_7682371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682371).length < 2 ^ (prefixWord ++ tailWord_7682371).sum := by decide
  have hdescent : baseEnd_7682371 < baseStart_7682371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682457 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_7682457 : Nat := 118140960795 + 7682457 * 2 ^ 59
def prefixEnd_7682457 : Nat := 4983230072969 + 3 ^ 40 * 7682457 * 2
def baseEnd_7682457 : Nat := 3944793048498154085356529

theorem tailTrace_7682457 : CollatzResearch.WordTrace tailWord_7682457 prefixEnd_7682457 3944793048498154085356529 := by
  unfold tailWord_7682457
  simp only [CollatzResearch.WordTrace]
  refine ⟨280202226328777823042341625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186801484219185215361561083 280202226328777823042341625)
  ·
    refine ⟨210151669746583367281756219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280202226328777823042341625 210151669746583367281756219)
    ·
      refine ⟨315227504619875050922634329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210151669746583367281756219 315227504619875050922634329)
      ·
        refine ⟨236420628464906288191975747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315227504619875050922634329 236420628464906288191975747)
        ·
          refine ⟨354630942697359432287963621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236420628464906288191975747 354630942697359432287963621)
          ·
            refine ⟨66493301755754893553993179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354630942697359432287963621 66493301755754893553993179)
            ·
              refine ⟨99739952633632340330989769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66493301755754893553993179 99739952633632340330989769)
              ·
                refine ⟨74804964475224255248242327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99739952633632340330989769 74804964475224255248242327)
                ·
                  refine ⟨112207446712836382872363491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74804964475224255248242327 112207446712836382872363491)
                  ·
                    refine ⟨168311170069254574308545237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112207446712836382872363491 168311170069254574308545237)
                    ·
                      refine ⟨3944793048498154085356529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168311170069254574308545237 3944793048498154085356529)
                      ·
                        rfl

theorem cell23_7682457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_7682457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682457 prefixEnd_7682457 := by exact prefixLift 7682457
  have htrace : WordTrace (prefixWord ++ tailWord_7682457) baseStart_7682457 baseEnd_7682457 := by
    simpa [prefixWord, tailWord_7682457, baseEnd_7682457] using wordTrace_append hprefix tailTrace_7682457
  have hstable : (prefixWord ++ tailWord_7682457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682457).length < 2 ^ (prefixWord ++ tailWord_7682457).sum := by decide
  have hdescent : baseEnd_7682457 < baseStart_7682457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682464 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 2, 5]
def baseStart_7682464 : Nat := 118140960795 + 7682464 * 2 ^ 59
def prefixEnd_7682464 : Nat := 4983230072969 + 3 ^ 40 * 7682464 * 2
def baseEnd_7682464 : Nat := 1314932214287578519322999

theorem tailTrace_7682464 : CollatzResearch.WordTrace tailWord_7682464 prefixEnd_7682464 1314932214287578519322999 := by
  unfold tailWord_7682464
  simp only [CollatzResearch.WordTrace]
  refine ⟨140101240819876231618923223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186801654426501642158564297 140101240819876231618923223)
  ·
    refine ⟨210151861229814347428384835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140101240819876231618923223 210151861229814347428384835)
    ·
      refine ⟨315227791844721521142577253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210151861229814347428384835 315227791844721521142577253)
      ·
        refine ⟨59105210970885285214233235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315227791844721521142577253 59105210970885285214233235)
        ·
          refine ⟨88657816456327927821349853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59105210970885285214233235 88657816456327927821349853)
          ·
            refine ⟨33246681171122972933006195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88657816456327927821349853 33246681171122972933006195)
            ·
              refine ⟨49870021756684459399509293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33246681171122972933006195 49870021756684459399509293)
              ·
                refine ⟨18701258158756672274815985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49870021756684459399509293 18701258158756672274815985)
                ·
                  refine ⟨14025943619067504206111989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18701258158756672274815985 14025943619067504206111989)
                  ·
                    refine ⟨1314932214287578519322999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14025943619067504206111989 1314932214287578519322999)
                    ·
                      rfl

theorem cell23_7682464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_7682464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682464 prefixEnd_7682464 := by exact prefixLift 7682464
  have htrace : WordTrace (prefixWord ++ tailWord_7682464) baseStart_7682464 baseEnd_7682464 := by
    simpa [prefixWord, tailWord_7682464, baseEnd_7682464] using wordTrace_append hprefix tailTrace_7682464
  have hstable : (prefixWord ++ tailWord_7682464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682464).length < 2 ^ (prefixWord ++ tailWord_7682464).sum := by decide
  have hdescent : baseEnd_7682464 < baseStart_7682464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682485 : List Nat := [1, 3, 3, 2, 3, 2, 2, 2, 5]
def baseStart_7682485 : Nat := 118140960795 + 7682485 * 2 ^ 59
def prefixEnd_7682485 : Nat := 4983230072969 + 3 ^ 40 * 7682485 * 2
def baseEnd_7682485 : Nat := 438311936217386663978489

theorem tailTrace_7682485 : CollatzResearch.WordTrace tailWord_7682485 prefixEnd_7682485 438311936217386663978489 := by
  unfold tailWord_7682485
  simp only [CollatzResearch.WordTrace]
  refine ⟨280203247572676383824360909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186802165048450922549573939 280203247572676383824360909)
  ·
    refine ⟨105076217839753643934135341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280203247572676383824360909 105076217839753643934135341)
    ·
      refine ⟨39403581689907616475300753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105076217839753643934135341 39403581689907616475300753)
      ·
        refine ⟨29552686267430712356475565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39403581689907616475300753 29552686267430712356475565)
        ·
          refine ⟨11082257350286517133678337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29552686267430712356475565 11082257350286517133678337)
          ·
            refine ⟨8311693012714887850258753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11082257350286517133678337 8311693012714887850258753)
            ·
              refine ⟨6233769759536165887694065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8311693012714887850258753 6233769759536165887694065)
              ·
                refine ⟨4675327319652124415770549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6233769759536165887694065 4675327319652124415770549)
                ·
                  refine ⟨438311936217386663978489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4675327319652124415770549 438311936217386663978489)
                  ·
                    rfl

theorem cell23_7682485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_7682485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682485 prefixEnd_7682485 := by exact prefixLift 7682485
  have htrace : WordTrace (prefixWord ++ tailWord_7682485) baseStart_7682485 baseEnd_7682485 := by
    simpa [prefixWord, tailWord_7682485, baseEnd_7682485] using wordTrace_append hprefix tailTrace_7682485
  have hstable : (prefixWord ++ tailWord_7682485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682485).length < 2 ^ (prefixWord ++ tailWord_7682485).sum := by decide
  have hdescent : baseEnd_7682485 < baseStart_7682485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682507 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 10]
def baseStart_7682507 : Nat := 118140960795 + 7682507 * 2 ^ 59
def prefixEnd_7682507 : Nat := 4983230072969 + 3 ^ 40 * 7682507 * 2
def baseEnd_7682507 : Nat := 438313191392319876636811

theorem tailTrace_7682507 : CollatzResearch.WordTrace tailWord_7682507 prefixEnd_7682507 438313191392319876636811 := by
  unfold tailWord_7682507
  simp only [CollatzResearch.WordTrace]
  refine ⟨280204049978596681581661775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186802699985731121054441183 280204049978596681581661775)
  ·
    refine ⟨420306074967895022372492663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280204049978596681581661775 420306074967895022372492663)
    ·
      refine ⟨630459112451842533558738995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420306074967895022372492663 630459112451842533558738995)
      ·
        refine ⟨945688668677763800338108493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630459112451842533558738995 945688668677763800338108493)
        ·
          refine ⟨354633250754161425126790685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 945688668677763800338108493 354633250754161425126790685)
          ·
            refine ⟨132987469032810534422546507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354633250754161425126790685 132987469032810534422546507)
            ·
              refine ⟨199481203549215801633819761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132987469032810534422546507 199481203549215801633819761)
              ·
                refine ⟨149610902661911851225364821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199481203549215801633819761 149610902661911851225364821)
                ·
                  refine ⟨438313191392319876636811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149610902661911851225364821 438313191392319876636811)
                  ·
                    rfl

theorem cell23_7682507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 10].length) (baseStart_7682507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682507 prefixEnd_7682507 := by exact prefixLift 7682507
  have htrace : WordTrace (prefixWord ++ tailWord_7682507) baseStart_7682507 baseEnd_7682507 := by
    simpa [prefixWord, tailWord_7682507, baseEnd_7682507] using wordTrace_append hprefix tailTrace_7682507
  have hstable : (prefixWord ++ tailWord_7682507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682507).length < 2 ^ (prefixWord ++ tailWord_7682507).sum := by decide
  have hdescent : baseEnd_7682507 < baseStart_7682507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682518 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_7682518 : Nat := 118140960795 + 7682518 * 2 ^ 59
def prefixEnd_7682518 : Nat := 4983230072969 + 3 ^ 40 * 7682518 * 2
def baseEnd_7682518 : Nat := 3944824370818078346693749

theorem tailTrace_7682518 : CollatzResearch.WordTrace tailWord_7682518 prefixEnd_7682518 3944824370818078346693749 := by
  unfold tailWord_7682518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17512778198847301903769513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186802967454371220306874805 17512778198847301903769513)
  ·
    refine ⟨13134583649135476427827135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17512778198847301903769513 13134583649135476427827135)
    ·
      refine ⟨19701875473703214641740703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13134583649135476427827135 19701875473703214641740703)
      ·
        refine ⟨29552813210554821962611055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19701875473703214641740703 29552813210554821962611055)
        ·
          refine ⟨44329219815832232943916583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29552813210554821962611055 44329219815832232943916583)
          ·
            refine ⟨66493829723748349415874875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44329219815832232943916583 66493829723748349415874875)
            ·
              refine ⟨99740744585622524123812313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66493829723748349415874875 99740744585622524123812313)
              ·
                refine ⟨74805558439216893092859235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99740744585622524123812313 74805558439216893092859235)
                ·
                  refine ⟨112208337658825339639288853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74805558439216893092859235 112208337658825339639288853)
                  ·
                    refine ⟨5259765827757437795591665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112208337658825339639288853 5259765827757437795591665)
                    ·
                      refine ⟨3944824370818078346693749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5259765827757437795591665 3944824370818078346693749)
                      ·
                        rfl

theorem cell23_7682518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_7682518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682518 prefixEnd_7682518 := by exact prefixLift 7682518
  have htrace : WordTrace (prefixWord ++ tailWord_7682518) baseStart_7682518 baseEnd_7682518 := by
    simpa [prefixWord, tailWord_7682518, baseEnd_7682518] using wordTrace_append hprefix tailTrace_7682518
  have hstable : (prefixWord ++ tailWord_7682518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682518).length < 2 ^ (prefixWord ++ tailWord_7682518).sum := by decide
  have hdescent : baseEnd_7682518 < baseStart_7682518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682528 : List Nat := [2, 1, 1, 3, 1, 1, 6, 3, 1, 4]
def baseStart_7682528 : Nat := 118140960795 + 7682528 * 2 ^ 59
def prefixEnd_7682528 : Nat := 4983230072969 + 3 ^ 40 * 7682528 * 2
def baseEnd_7682528 : Nat := 1314943168541541102522901

theorem tailTrace_7682528 : CollatzResearch.WordTrace tailWord_7682528 prefixEnd_7682528 1314943168541541102522901 := by
  unfold tailWord_7682528
  simp only [CollatzResearch.WordTrace]
  refine ⟨140102407955760301084088119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186803210607680401445450825 140102407955760301084088119)
  ·
    refine ⟨210153611933640451626132179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140102407955760301084088119 210153611933640451626132179)
    ·
      refine ⟨315230417900460677439198269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210153611933640451626132179 315230417900460677439198269)
      ·
        refine ⟨118211406712672754039699351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315230417900460677439198269 118211406712672754039699351)
        ·
          refine ⟨177317110069009131059549027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118211406712672754039699351 177317110069009131059549027)
          ·
            refine ⟨265975665103513696589323541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177317110069009131059549027 265975665103513696589323541)
            ·
              refine ⟨12467609301727204527624541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 265975665103513696589323541 12467609301727204527624541)
              ·
                refine ⟨4675353488147701697859203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12467609301727204527624541 4675353488147701697859203)
                ·
                  refine ⟨7013030232221552546788805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675353488147701697859203 7013030232221552546788805)
                  ·
                    refine ⟨1314943168541541102522901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7013030232221552546788805 1314943168541541102522901)
                    ·
                      rfl

theorem cell23_7682528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 1, 4].length) (baseStart_7682528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682528 prefixEnd_7682528 := by exact prefixLift 7682528
  have htrace : WordTrace (prefixWord ++ tailWord_7682528) baseStart_7682528 baseEnd_7682528 := by
    simpa [prefixWord, tailWord_7682528, baseEnd_7682528] using wordTrace_append hprefix tailTrace_7682528
  have hstable : (prefixWord ++ tailWord_7682528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682528).length < 2 ^ (prefixWord ++ tailWord_7682528).sum := by decide
  have hdescent : baseEnd_7682528 < baseStart_7682528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682541 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 8]
def baseStart_7682541 : Nat := 118140960795 + 7682541 * 2 ^ 59
def prefixEnd_7682541 : Nat := 4983230072969 + 3 ^ 40 * 7682541 * 2
def baseEnd_7682541 : Nat := 438315131208125750745127

theorem tailTrace_7682541 : CollatzResearch.WordTrace tailWord_7682541 prefixEnd_7682541 438315131208125750745127 := by
  unfold tailWord_7682541
  simp only [CollatzResearch.WordTrace]
  refine ⟨280205290060473505388399477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186803526706982336925599651 280205290060473505388399477)
  ·
    refine ⟨26269245943169391130162451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280205290060473505388399477 26269245943169391130162451)
    ·
      refine ⟨39403868914754086695243677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26269245943169391130162451 39403868914754086695243677)
      ·
        refine ⟨14776450843032782510716379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39403868914754086695243677 14776450843032782510716379)
        ·
          refine ⟨22164676264549173766074569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14776450843032782510716379 22164676264549173766074569)
          ·
            refine ⟨16623507198411880324555927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22164676264549173766074569 16623507198411880324555927)
            ·
              refine ⟨24935260797617820486833891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16623507198411880324555927 24935260797617820486833891)
              ·
                refine ⟨37402891196426730730250837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24935260797617820486833891 37402891196426730730250837)
                ·
                  refine ⟨438315131208125750745127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37402891196426730730250837 438315131208125750745127)
                  ·
                    rfl

theorem cell23_7682541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_7682541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682541 prefixEnd_7682541 := by exact prefixLift 7682541
  have htrace : WordTrace (prefixWord ++ tailWord_7682541) baseStart_7682541 baseEnd_7682541 := by
    simpa [prefixWord, tailWord_7682541, baseEnd_7682541] using wordTrace_append hprefix tailTrace_7682541
  have hstable : (prefixWord ++ tailWord_7682541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682541).length < 2 ^ (prefixWord ++ tailWord_7682541).sum := by decide
  have hdescent : baseEnd_7682541 < baseStart_7682541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682554 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_7682554 : Nat := 118140960795 + 7682554 * 2 ^ 59
def prefixEnd_7682554 : Nat := 4983230072969 + 3 ^ 40 * 7682554 * 2
def baseEnd_7682554 : Nat := 1314947618707213401947861

theorem tailTrace_7682554 : CollatzResearch.WordTrace tailWord_7682554 prefixEnd_7682554 1314947618707213401947861 := by
  unfold tailWord_7682554
  simp only [CollatzResearch.WordTrace]
  refine ⟨70051441052356602152155679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186803842806284272405748477 70051441052356602152155679)
  ·
    refine ⟨105077161578534903228233519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70051441052356602152155679 105077161578534903228233519)
    ·
      refine ⟨157615742367802354842350279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105077161578534903228233519 157615742367802354842350279)
      ·
        refine ⟨236423613551703532263525419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157615742367802354842350279 236423613551703532263525419)
        ·
          refine ⟨354635420327555298395288129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236423613551703532263525419 354635420327555298395288129)
          ·
            refine ⟨265976565245666473796466097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354635420327555298395288129 265976565245666473796466097)
            ·
              refine ⟨199482423934249855347349573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265976565245666473796466097 199482423934249855347349573)
              ·
                refine ⟨37402954487671847877628045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199482423934249855347349573 37402954487671847877628045)
                ·
                  refine ⟨14026107932876942954110517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37402954487671847877628045 14026107932876942954110517)
                  ·
                    refine ⟨1314947618707213401947861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14026107932876942954110517 1314947618707213401947861)
                    ·
                      rfl

theorem cell23_7682554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_7682554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682554 prefixEnd_7682554 := by exact prefixLift 7682554
  have htrace : WordTrace (prefixWord ++ tailWord_7682554) baseStart_7682554 baseEnd_7682554 := by
    simpa [prefixWord, tailWord_7682554, baseEnd_7682554] using wordTrace_append hprefix tailTrace_7682554
  have hstable : (prefixWord ++ tailWord_7682554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682554).length < 2 ^ (prefixWord ++ tailWord_7682554).sum := by decide
  have hdescent : baseEnd_7682554 < baseStart_7682554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682571 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 1, 5]
def baseStart_7682571 : Nat := 118140960795 + 7682571 * 2 ^ 59
def prefixEnd_7682571 : Nat := 4983230072969 + 3 ^ 40 * 7682571 * 2
def baseEnd_7682571 : Nat := 1314950528430922213110335

theorem tailTrace_7682571 : CollatzResearch.WordTrace tailWord_7682571 prefixEnd_7682571 1314950528430922213110335 := by
  unfold tailWord_7682571
  simp only [CollatzResearch.WordTrace]
  refine ⟨280206384250364820511991567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186804256166909880341327711 280206384250364820511991567)
  ·
    refine ⟨420309576375547230767987351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280206384250364820511991567 420309576375547230767987351)
    ·
      refine ⟨630464364563320846151981027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420309576375547230767987351 630464364563320846151981027)
      ·
        refine ⟨945696546844981269227971541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630464364563320846151981027 945696546844981269227971541)
        ·
          refine ⟨22164762816679248497530583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 945696546844981269227971541 22164762816679248497530583)
          ·
            refine ⟨33247144225018872746295875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22164762816679248497530583 33247144225018872746295875)
            ·
              refine ⟨49870716337528309119443813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33247144225018872746295875 49870716337528309119443813)
              ·
                refine ⟨9350759313286557959895715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49870716337528309119443813 9350759313286557959895715)
                ·
                  refine ⟨14026138969929836939843573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9350759313286557959895715 14026138969929836939843573)
                  ·
                    refine ⟨1314950528430922213110335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14026138969929836939843573 1314950528430922213110335)
                    ·
                      rfl

theorem cell23_7682571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 5].length) (baseStart_7682571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682571 prefixEnd_7682571 := by exact prefixLift 7682571
  have htrace : WordTrace (prefixWord ++ tailWord_7682571) baseStart_7682571 baseEnd_7682571 := by
    simpa [prefixWord, tailWord_7682571, baseEnd_7682571] using wordTrace_append hprefix tailTrace_7682571
  have hstable : (prefixWord ++ tailWord_7682571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682571).length < 2 ^ (prefixWord ++ tailWord_7682571).sum := by decide
  have hdescent : baseEnd_7682571 < baseStart_7682571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682611 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 3]
def baseStart_7682611 : Nat := 118140960795 + 7682611 * 2 ^ 59
def prefixEnd_7682611 : Nat := 4983230072969 + 3 ^ 40 * 7682611 * 2
def baseEnd_7682611 : Nat := 3944872124518946482830821

theorem tailTrace_7682611 : CollatzResearch.WordTrace tailWord_7682611 prefixEnd_7682611 3944872124518946482830821 := by
  unfold tailWord_7682611
  simp only [CollatzResearch.WordTrace]
  refine ⟨280207843170219907343447687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186805228780146604895631791 280207843170219907343447687)
  ·
    refine ⟨420311764755329861015171531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280207843170219907343447687 420311764755329861015171531)
    ·
      refine ⟨630467647132994791522757297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420311764755329861015171531 630467647132994791522757297)
      ·
        refine ⟨472850735349746093642067973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630467647132994791522757297 472850735349746093642067973)
        ·
          refine ⟨88659512878077392557887745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472850735349746093642067973 88659512878077392557887745)
          ·
            refine ⟨66494634658558044418415809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88659512878077392557887745 66494634658558044418415809)
            ·
              refine ⟨49870975993918533313811857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66494634658558044418415809 49870975993918533313811857)
              ·
                refine ⟨37403231995438899985358893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49870975993918533313811857 37403231995438899985358893)
                ·
                  refine ⟨14026211998289587494509585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37403231995438899985358893 14026211998289587494509585)
                  ·
                    refine ⟨10519658998717190620882189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14026211998289587494509585 10519658998717190620882189)
                    ·
                      refine ⟨3944872124518946482830821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10519658998717190620882189 3944872124518946482830821)
                      ·
                        rfl

theorem cell23_7682611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 3].length) (baseStart_7682611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682611 prefixEnd_7682611 := by exact prefixLift 7682611
  have htrace : WordTrace (prefixWord ++ tailWord_7682611) baseStart_7682611 baseEnd_7682611 := by
    simpa [prefixWord, tailWord_7682611, baseEnd_7682611] using wordTrace_append hprefix tailTrace_7682611
  have hstable : (prefixWord ++ tailWord_7682611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682611).length < 2 ^ (prefixWord ++ tailWord_7682611).sum := by decide
  have hdescent : baseEnd_7682611 < baseStart_7682611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682618 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 2, 4]
def baseStart_7682618 : Nat := 118140960795 + 7682618 * 2 ^ 59
def prefixEnd_7682618 : Nat := 4983230072969 + 3 ^ 40 * 7682618 * 2
def baseEnd_7682618 : Nat := 1314958572961175985147763

theorem tailTrace_7682618 : CollatzResearch.WordTrace tailWord_7682618 prefixEnd_7682618 1314958572961175985147763 := by
  unfold tailWord_7682618
  simp only [CollatzResearch.WordTrace]
  refine ⟨70052024620298636884738127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186805398987463031692635005 70052024620298636884738127)
  ·
    refine ⟨105078036930447955327107191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70052024620298636884738127 105078036930447955327107191)
    ·
      refine ⟨157617055395671932990660787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105078036930447955327107191 157617055395671932990660787)
      ·
        refine ⟨236425583093507899485991181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157617055395671932990660787 236425583093507899485991181)
        ·
          refine ⟨88659593660065462307246693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236425583093507899485991181 88659593660065462307246693)
          ·
            refine ⟨16623673811262274182608755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88659593660065462307246693 16623673811262274182608755)
            ·
              refine ⟨24935510716893411273913133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16623673811262274182608755 24935510716893411273913133)
              ·
                refine ⟨9350816518835029227717425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24935510716893411273913133 9350816518835029227717425)
                ·
                  refine ⟨7013112389126271920788069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9350816518835029227717425 7013112389126271920788069)
                  ·
                    refine ⟨1314958572961175985147763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7013112389126271920788069 1314958572961175985147763)
                    ·
                      rfl

theorem cell23_7682618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_7682618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682618 prefixEnd_7682618 := by exact prefixLift 7682618
  have htrace : WordTrace (prefixWord ++ tailWord_7682618) baseStart_7682618 baseEnd_7682618 := by
    simpa [prefixWord, tailWord_7682618, baseEnd_7682618] using wordTrace_append hprefix tailTrace_7682618
  have hstable : (prefixWord ++ tailWord_7682618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682618).length < 2 ^ (prefixWord ++ tailWord_7682618).sum := by decide
  have hdescent : baseEnd_7682618 < baseStart_7682618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682621 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7682621 : Nat := 118140960795 + 7682621 * 2 ^ 59
def prefixEnd_7682621 : Nat := 4983230072969 + 3 ^ 40 * 7682621 * 2
def baseEnd_7682621 : Nat := 3944877259325491443705775

theorem tailTrace_7682621 : CollatzResearch.WordTrace tailWord_7682621 prefixEnd_7682621 3944877259325491443705775 := by
  unfold tailWord_7682621
  simp only [CollatzResearch.WordTrace]
  refine ⟨280208207900183679051311717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186805471933455786034207811 280208207900183679051311717)
  ·
    refine ⟨52539038981284439822120947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280208207900183679051311717 52539038981284439822120947)
    ·
      refine ⟨78808558471926659733181421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52539038981284439822120947 78808558471926659733181421)
      ·
        refine ⟨29553209426972497399943033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78808558471926659733181421 29553209426972497399943033)
        ·
          refine ⟨22164907070229373049957275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29553209426972497399943033 22164907070229373049957275)
          ·
            refine ⟨33247360605344059574935913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22164907070229373049957275 33247360605344059574935913)
            ·
              refine ⟨24935520454008044681201935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33247360605344059574935913 24935520454008044681201935)
              ·
                refine ⟨37403280681012067021802903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24935520454008044681201935 37403280681012067021802903)
                ·
                  refine ⟨56104921021518100532704355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37403280681012067021802903 56104921021518100532704355)
                  ·
                    refine ⟨84157381532277150799056533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56104921021518100532704355 84157381532277150799056533)
                    ·
                      refine ⟨3944877259325491443705775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84157381532277150799056533 3944877259325491443705775)
                      ·
                        rfl

theorem cell23_7682621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7682621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682621 prefixEnd_7682621 := by exact prefixLift 7682621
  have htrace : WordTrace (prefixWord ++ tailWord_7682621) baseStart_7682621 baseEnd_7682621 := by
    simpa [prefixWord, tailWord_7682621, baseEnd_7682621] using wordTrace_append hprefix tailTrace_7682621
  have hstable : (prefixWord ++ tailWord_7682621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682621).length < 2 ^ (prefixWord ++ tailWord_7682621).sum := by decide
  have hdescent : baseEnd_7682621 < baseStart_7682621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682622 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_7682622 : Nat := 118140960795 + 7682622 * 2 ^ 59
def prefixEnd_7682622 : Nat := 4983230072969 + 3 ^ 40 * 7682622 * 2
def baseEnd_7682622 : Nat := 1314959257602048646597757

theorem tailTrace_7682622 : CollatzResearch.WordTrace tailWord_7682622 prefixEnd_7682622 1314959257602048646597757 := by
  unfold tailWord_7682622
  simp only [CollatzResearch.WordTrace]
  refine ⟨35026030546647507027762265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186805496248786704148065413 35026030546647507027762265)
  ·
    refine ⟨26269522909985630270821699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35026030546647507027762265 26269522909985630270821699)
    ·
      refine ⟨39404284364978445406232549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26269522909985630270821699 39404284364978445406232549)
      ·
        refine ⟨7388303318433458513668603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39404284364978445406232549 7388303318433458513668603)
        ·
          refine ⟨11082454977650187770502905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7388303318433458513668603 11082454977650187770502905)
          ·
            refine ⟨8311841233237640827877179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11082454977650187770502905 8311841233237640827877179)
            ·
              refine ⟨12467761849856461241815769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8311841233237640827877179 12467761849856461241815769)
              ·
                refine ⟨9350821387392345931361827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12467761849856461241815769 9350821387392345931361827)
                ·
                  refine ⟨14026232081088518897042741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9350821387392345931361827 14026232081088518897042741)
                  ·
                    refine ⟨1314959257602048646597757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14026232081088518897042741 1314959257602048646597757)
                    ·
                      rfl

theorem cell23_7682622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_7682622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682622 prefixEnd_7682622 := by exact prefixLift 7682622
  have htrace : WordTrace (prefixWord ++ tailWord_7682622) baseStart_7682622 baseEnd_7682622 := by
    simpa [prefixWord, tailWord_7682622, baseEnd_7682622] using wordTrace_append hprefix tailTrace_7682622
  have hstable : (prefixWord ++ tailWord_7682622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682622).length < 2 ^ (prefixWord ++ tailWord_7682622).sum := by decide
  have hdescent : baseEnd_7682622 < baseStart_7682622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682625 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_7682625 : Nat := 118140960795 + 7682625 * 2 ^ 59
def prefixEnd_7682625 : Nat := 4983230072969 + 3 ^ 40 * 7682625 * 2
def baseEnd_7682625 : Nat := 3944879313248109428055757

theorem tailTrace_7682625 : CollatzResearch.WordTrace tailWord_7682625 prefixEnd_7682625 3944879313248109428055757 := by
  unfold tailWord_7682625
  simp only [CollatzResearch.WordTrace]
  refine ⟨280208353792169187734457329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186805569194779458489638219 280208353792169187734457329)
  ·
    refine ⟨210156265344126890800842997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280208353792169187734457329 210156265344126890800842997)
    ·
      refine ⟨19702149876011896012579031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210156265344126890800842997 19702149876011896012579031)
      ·
        refine ⟨29553224814017844018868547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19702149876011896012579031 29553224814017844018868547)
        ·
          refine ⟨44329837221026766028302821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29553224814017844018868547 44329837221026766028302821)
          ·
            refine ⟨8311844478942518630306779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44329837221026766028302821 8311844478942518630306779)
            ·
              refine ⟨12467766718413777945460169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8311844478942518630306779 12467766718413777945460169)
              ·
                refine ⟨9350825038810333459095127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12467766718413777945460169 9350825038810333459095127)
                ·
                  refine ⟨14026237558215500188642691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9350825038810333459095127 14026237558215500188642691)
                  ·
                    refine ⟨21039356337323250282964037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14026237558215500188642691 21039356337323250282964037)
                    ·
                      refine ⟨3944879313248109428055757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21039356337323250282964037 3944879313248109428055757)
                      ·
                        rfl

theorem cell23_7682625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_7682625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682625 prefixEnd_7682625 := by exact prefixLift 7682625
  have htrace : WordTrace (prefixWord ++ tailWord_7682625) baseStart_7682625 baseEnd_7682625 := by
    simpa [prefixWord, tailWord_7682625, baseEnd_7682625] using wordTrace_append hprefix tailTrace_7682625
  have hstable : (prefixWord ++ tailWord_7682625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682625).length < 2 ^ (prefixWord ++ tailWord_7682625).sum := by decide
  have hdescent : baseEnd_7682625 < baseStart_7682625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682641 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 3, 3, 3]
def baseStart_7682641 : Nat := 118140960795 + 7682641 * 2 ^ 59
def prefixEnd_7682641 : Nat := 4983230072969 + 3 ^ 40 * 7682641 * 2
def baseEnd_7682641 : Nat := 3944887528938581365455683

theorem tailTrace_7682641 : CollatzResearch.WordTrace tailWord_7682641 prefixEnd_7682641 3944887528938581365455683 := by
  unfold tailWord_7682641
  simp only [CollatzResearch.WordTrace]
  refine ⟨280208937360111222467039777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186805958240074148311359851 280208937360111222467039777)
  ·
    refine ⟨210156703020083416850279833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280208937360111222467039777 210156703020083416850279833)
    ·
      refine ⟨157617527265062562637709875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210156703020083416850279833 157617527265062562637709875)
      ·
        refine ⟨236426290897593843956564813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157617527265062562637709875 236426290897593843956564813)
        ·
          refine ⟨88659859086597691483711805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236426290897593843956564813 88659859086597691483711805)
          ·
            refine ⟨33247447157474134306391927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88659859086597691483711805 33247447157474134306391927)
            ·
              refine ⟨49871170736211201459587891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33247447157474134306391927 49871170736211201459587891)
              ·
                refine ⟨74806756104316802189381837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49871170736211201459587891 74806756104316802189381837)
                ·
                  refine ⟨28052533539118800821018189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74806756104316802189381837 28052533539118800821018189)
                  ·
                    refine ⟨10519700077169550307881821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28052533539118800821018189 10519700077169550307881821)
                    ·
                      refine ⟨3944887528938581365455683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10519700077169550307881821 3944887528938581365455683)
                      ·
                        rfl

theorem cell23_7682641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_7682641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682641 prefixEnd_7682641 := by exact prefixLift 7682641
  have htrace : WordTrace (prefixWord ++ tailWord_7682641) baseStart_7682641 baseEnd_7682641 := by
    simpa [prefixWord, tailWord_7682641, baseEnd_7682641] using wordTrace_append hprefix tailTrace_7682641
  have hstable : (prefixWord ++ tailWord_7682641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682641).length < 2 ^ (prefixWord ++ tailWord_7682641).sum := by decide
  have hdescent : baseEnd_7682641 < baseStart_7682641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682642 : List Nat := [3, 2, 2, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_7682642 : Nat := 118140960795 + 7682642 * 2 ^ 59
def prefixEnd_7682642 : Nat := 4983230072969 + 3 ^ 40 * 7682642 * 2
def baseEnd_7682642 : Nat := 3944888042419235861543179

theorem tailTrace_7682642 : CollatzResearch.WordTrace tailWord_7682642 prefixEnd_7682642 3944888042419235861543179 := by
  unfold tailWord_7682642
  simp only [CollatzResearch.WordTrace]
  refine ⟨70052243458276899909456545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186805982555405066425217453 70052243458276899909456545)
  ·
    refine ⟨52539182593707674932092409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70052243458276899909456545 52539182593707674932092409)
    ·
      refine ⟨39404386945280756199069307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52539182593707674932092409 39404386945280756199069307)
      ·
        refine ⟨59106580417921134298603961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39404386945280756199069307 59106580417921134298603961)
        ·
          refine ⟨44329935313440850723952971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59106580417921134298603961 44329935313440850723952971)
          ·
            refine ⟨66494902970161276085929457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44329935313440850723952971 66494902970161276085929457)
            ·
              refine ⟨49871177227620957064447093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66494902970161276085929457 49871177227620957064447093)
              ·
                refine ⟨4675422865089464724791915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49871177227620957064447093 4675422865089464724791915)
                ·
                  refine ⟨7013134297634197087187873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675422865089464724791915 7013134297634197087187873)
                  ·
                    refine ⟨5259850723225647815390905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7013134297634197087187873 5259850723225647815390905)
                    ·
                      refine ⟨3944888042419235861543179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5259850723225647815390905 3944888042419235861543179)
                      ·
                        rfl

theorem cell23_7682642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_7682642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682642 prefixEnd_7682642 := by exact prefixLift 7682642
  have htrace : WordTrace (prefixWord ++ tailWord_7682642) baseStart_7682642 baseEnd_7682642 := by
    simpa [prefixWord, tailWord_7682642, baseEnd_7682642] using wordTrace_append hprefix tailTrace_7682642
  have hstable : (prefixWord ++ tailWord_7682642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682642).length < 2 ^ (prefixWord ++ tailWord_7682642).sum := by decide
  have hdescent : baseEnd_7682642 < baseStart_7682642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682668 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 3, 3, 2]
def baseStart_7682668 : Nat := 118140960795 + 7682668 * 2 ^ 59
def prefixEnd_7682668 : Nat := 4983230072969 + 3 ^ 40 * 7682668 * 2
def baseEnd_7682668 : Nat := 3944901392916252759818059

theorem tailTrace_7682668 : CollatzResearch.WordTrace tailWord_7682668 prefixEnd_7682668 3944901392916252759818059 := by
  unfold tailWord_7682668
  simp only [CollatzResearch.WordTrace]
  refine ⟨140104961065506703039136329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186806614754008937385515105 140104961065506703039136329)
  ·
    refine ⟨105078720799130027279352247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140104961065506703039136329 105078720799130027279352247)
    ·
      refine ⟨157618081198695040919028371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105078720799130027279352247 157618081198695040919028371)
      ·
        refine ⟨236427121798042561378542557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157618081198695040919028371 236427121798042561378542557)
        ·
          refine ⟨88660170674265960516953459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236427121798042561378542557 88660170674265960516953459)
          ·
            refine ⟨132990256011398940775430189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88660170674265960516953459 132990256011398940775430189)
            ·
              refine ⟨49871346004274602790786321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132990256011398940775430189 49871346004274602790786321)
              ·
                refine ⟨37403509503205952093089741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49871346004274602790786321 37403509503205952093089741)
                ·
                  refine ⟨14026316063702232034908653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37403509503205952093089741 14026316063702232034908653)
                  ·
                    refine ⟨5259868523888337013090745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14026316063702232034908653 5259868523888337013090745)
                    ·
                      refine ⟨3944901392916252759818059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5259868523888337013090745 3944901392916252759818059)
                      ·
                        rfl

theorem cell23_7682668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 3, 2].length) (baseStart_7682668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682668 prefixEnd_7682668 := by exact prefixLift 7682668
  have htrace : WordTrace (prefixWord ++ tailWord_7682668) baseStart_7682668 baseEnd_7682668 := by
    simpa [prefixWord, tailWord_7682668, baseEnd_7682668] using wordTrace_append hprefix tailTrace_7682668
  have hstable : (prefixWord ++ tailWord_7682668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682668).length < 2 ^ (prefixWord ++ tailWord_7682668).sum := by decide
  have hdescent : baseEnd_7682668 < baseStart_7682668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682708 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_7682708 : Nat := 118140960795 + 7682708 * 2 ^ 59
def prefixEnd_7682708 : Nat := 4983230072969 + 3 ^ 40 * 7682708 * 2
def baseEnd_7682708 : Nat := 1314973977380810867772625

theorem tailTrace_7682708 : CollatzResearch.WordTrace tailWord_7682708 prefixEnd_7682708 1314973977380810867772625 := by
  unfold tailWord_7682708
  simp only [CollatzResearch.WordTrace]
  refine ⟨140105690525434246454864389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186807587367245661939819185 140105690525434246454864389)
  ·
    refine ⟨26269816973518921210287073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140105690525434246454864389 26269816973518921210287073)
    ·
      refine ⟨19702362730139190907715305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26269816973518921210287073 19702362730139190907715305)
      ·
        refine ⟨14776772047604393180786479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19702362730139190907715305 14776772047604393180786479)
        ·
          refine ⟨22165158071406589771179719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14776772047604393180786479 22165158071406589771179719)
          ·
            refine ⟨33247737107109884656769579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22165158071406589771179719 33247737107109884656769579)
            ·
              refine ⟨49871605660664826985154369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33247737107109884656769579 49871605660664826985154369)
              ·
                refine ⟨37403704245498620238865777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49871605660664826985154369 37403704245498620238865777)
                ·
                  refine ⟨28052778184123965179149333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37403704245498620238865777 28052778184123965179149333)
                  ·
                    refine ⟨1314973977380810867772625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28052778184123965179149333 1314973977380810867772625)
                    ·
                      rfl

theorem cell23_7682708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_7682708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682708 prefixEnd_7682708 := by exact prefixLift 7682708
  have htrace : WordTrace (prefixWord ++ tailWord_7682708) baseStart_7682708 baseEnd_7682708 := by
    simpa [prefixWord, tailWord_7682708, baseEnd_7682708] using wordTrace_append hprefix tailTrace_7682708
  have hstable : (prefixWord ++ tailWord_7682708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682708).length < 2 ^ (prefixWord ++ tailWord_7682708).sum := by decide
  have hdescent : baseEnd_7682708 < baseStart_7682708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682711 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_7682711 : Nat := 118140960795 + 7682711 * 2 ^ 59
def prefixEnd_7682711 : Nat := 4983230072969 + 3 ^ 40 * 7682711 * 2
def baseEnd_7682711 : Nat := 3944923472584396091580361

theorem tailTrace_7682711 : CollatzResearch.WordTrace tailWord_7682711 prefixEnd_7682711 3944923472584396091580361 := by
  unfold tailWord_7682711
  simp only [CollatzResearch.WordTrace]
  refine ⟨280211490469857624422087987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186807660313238416281391991 280211490469857624422087987)
  ·
    refine ⟨420317235704786436633131981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280211490469857624422087987 420317235704786436633131981)
    ·
      refine ⟨157618963389294913737424493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420317235704786436633131981 157618963389294913737424493)
      ·
        refine ⟨59107111270985592651534185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157618963389294913737424493 59107111270985592651534185)
        ·
          refine ⟨44330333453239194488650639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59107111270985592651534185 44330333453239194488650639)
          ·
            refine ⟨66495500179858791732975959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44330333453239194488650639 66495500179858791732975959)
            ·
              refine ⟨99743250269788187599463939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66495500179858791732975959 99743250269788187599463939)
              ·
                refine ⟨149614875404682281399195909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99743250269788187599463939 149614875404682281399195909)
                ·
                  refine ⟨28052789138377927762349233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149614875404682281399195909 28052789138377927762349233)
                  ·
                    refine ⟨21039591853783445821761925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28052789138377927762349233 21039591853783445821761925)
                    ·
                      refine ⟨3944923472584396091580361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21039591853783445821761925 3944923472584396091580361)
                      ·
                        rfl

theorem cell23_7682711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_7682711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682711 prefixEnd_7682711 := by exact prefixLift 7682711
  have htrace : WordTrace (prefixWord ++ tailWord_7682711) baseStart_7682711 baseEnd_7682711 := by
    simpa [prefixWord, tailWord_7682711, baseEnd_7682711] using wordTrace_append hprefix tailTrace_7682711
  have hstable : (prefixWord ++ tailWord_7682711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682711).length < 2 ^ (prefixWord ++ tailWord_7682711).sum := by decide
  have hdescent : baseEnd_7682711 < baseStart_7682711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682751 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 1, 7]
def baseStart_7682751 : Nat := 118140960795 + 7682751 * 2 ^ 59
def prefixEnd_7682751 : Nat := 4983230072969 + 3 ^ 40 * 7682751 * 2
def baseEnd_7682751 : Nat := 1314981337270191978360059

theorem tailTrace_7682751 : CollatzResearch.WordTrace tailWord_7682751 prefixEnd_7682751 1314981337270191978360059 := by
  unfold tailWord_7682751
  simp only [CollatzResearch.WordTrace]
  refine ⟨280212949389712711253544107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186808632926475140835696071 280212949389712711253544107)
  ·
    refine ⟨420319424084569066880316161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280212949389712711253544107 420319424084569066880316161)
    ·
      refine ⟨315239568063426800160237121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420319424084569066880316161 315239568063426800160237121)
      ·
        refine ⟨236429676047570100120177841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315239568063426800160237121 236429676047570100120177841)
        ·
          refine ⟨177322257035677575090133381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236429676047570100120177841 177322257035677575090133381)
          ·
            refine ⟨33247923194189545329400009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177322257035677575090133381 33247923194189545329400009)
            ·
              refine ⟨24935942395642158997050007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33247923194189545329400009 24935942395642158997050007)
              ·
                refine ⟨37403913593463238495575011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24935942395642158997050007 37403913593463238495575011)
                ·
                  refine ⟨56105870390194857743362517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37403913593463238495575011 56105870390194857743362517)
                  ·
                    refine ⟨1314981337270191978360059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56105870390194857743362517 1314981337270191978360059)
                    ·
                      rfl

theorem cell23_7682751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_7682751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682751 prefixEnd_7682751 := by exact prefixLift 7682751
  have htrace : WordTrace (prefixWord ++ tailWord_7682751) baseStart_7682751 baseEnd_7682751 := by
    simpa [prefixWord, tailWord_7682751, baseEnd_7682751] using wordTrace_append hprefix tailTrace_7682751
  have hstable : (prefixWord ++ tailWord_7682751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682751).length < 2 ^ (prefixWord ++ tailWord_7682751).sum := by decide
  have hdescent : baseEnd_7682751 < baseStart_7682751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682772 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 7]
def baseStart_7682772 : Nat := 118140960795 + 7682772 * 2 ^ 59
def prefixEnd_7682772 : Nat := 4983230072969 + 3 ^ 40 * 7682772 * 2
def baseEnd_7682772 : Nat := 438328310544924483657509

theorem tailTrace_7682772 : CollatzResearch.WordTrace tailWord_7682772 prefixEnd_7682772 438328310544924483657509 := by
  unfold tailWord_7682772
  simp only [CollatzResearch.WordTrace]
  refine ⟨140106857661318315920029285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186809143548424421226705713 140106857661318315920029285)
  ·
    refine ⟨26270035811497184235005491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140106857661318315920029285 26270035811497184235005491)
    ·
      refine ⟨39405053717245776352508237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26270035811497184235005491 39405053717245776352508237)
      ·
        refine ⟨14776895143967166132190589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39405053717245776352508237 14776895143967166132190589)
        ·
          refine ⟨5541335678987687299571471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14776895143967166132190589 5541335678987687299571471)
          ·
            refine ⟨8312003518481530949357207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541335678987687299571471 8312003518481530949357207)
            ·
              refine ⟨12468005277722296424035811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8312003518481530949357207 12468005277722296424035811)
              ·
                refine ⟨18702007916583444636053717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12468005277722296424035811 18702007916583444636053717)
                ·
                  refine ⟨438328310544924483657509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18702007916583444636053717 438328310544924483657509)
                  ·
                    rfl

theorem cell23_7682772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_7682772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682772 prefixEnd_7682772 := by exact prefixLift 7682772
  have htrace : WordTrace (prefixWord ++ tailWord_7682772) baseStart_7682772 baseEnd_7682772 := by
    simpa [prefixWord, tailWord_7682772, baseEnd_7682772] using wordTrace_append hprefix tailTrace_7682772
  have hstable : (prefixWord ++ tailWord_7682772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682772).length < 2 ^ (prefixWord ++ tailWord_7682772).sum := by decide
  have hdescent : baseEnd_7682772 < baseStart_7682772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682815 : List Nat := [1, 1, 2, 2, 1, 3, 1, 7, 1, 4]
def baseStart_7682815 : Nat := 118140960795 + 7682815 * 2 ^ 59
def prefixEnd_7682815 : Nat := 4983230072969 + 3 ^ 40 * 7682815 * 2
def baseEnd_7682815 : Nat := 1314992291524154561559961

theorem tailTrace_7682815 : CollatzResearch.WordTrace tailWord_7682815 prefixEnd_7682815 1314992291524154561559961 := by
  unfold tailWord_7682815
  simp only [CollatzResearch.WordTrace]
  refine ⟨280215283661480850183873899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186810189107653900122582599 280215283661480850183873899)
  ·
    refine ⟨420322925492221275275810849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280215283661480850183873899 420322925492221275275810849)
    ·
      refine ⟨315242194119165956456858137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420322925492221275275810849 315242194119165956456858137)
      ·
        refine ⟨236431645589374467342643603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315242194119165956456858137 236431645589374467342643603)
        ·
          refine ⟨354647468384061701013965405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236431645589374467342643603 354647468384061701013965405)
          ·
            refine ⟨132992800644023137880237027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354647468384061701013965405 132992800644023137880237027)
            ·
              refine ⟨199489200966034706820355541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132992800644023137880237027 199489200966034706820355541)
              ·
                refine ⟨4675528147641438441102083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 199489200966034706820355541 4675528147641438441102083)
                ·
                  refine ⟨7013292221462157661653125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675528147641438441102083 7013292221462157661653125)
                  ·
                    refine ⟨1314992291524154561559961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7013292221462157661653125 1314992291524154561559961)
                    ·
                      rfl

theorem cell23_7682815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 1, 4].length) (baseStart_7682815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682815 prefixEnd_7682815 := by exact prefixLift 7682815
  have htrace : WordTrace (prefixWord ++ tailWord_7682815) baseStart_7682815 baseEnd_7682815 := by
    simpa [prefixWord, tailWord_7682815, baseEnd_7682815] using wordTrace_append hprefix tailTrace_7682815
  have hstable : (prefixWord ++ tailWord_7682815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682815).length < 2 ^ (prefixWord ++ tailWord_7682815).sum := by decide
  have hdescent : baseEnd_7682815 < baseStart_7682815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682831 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_7682831 : Nat := 118140960795 + 7682831 * 2 ^ 59
def prefixEnd_7682831 : Nat := 4983230072969 + 3 ^ 40 * 7682831 * 2
def baseEnd_7682831 : Nat := 3944985090262935622079809

theorem tailTrace_7682831 : CollatzResearch.WordTrace tailWord_7682831 prefixEnd_7682831 3944985090262935622079809 := by
  unfold tailWord_7682831
  simp only [CollatzResearch.WordTrace]
  refine ⟨280215867229422884916456347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186810578152948589944304231 280215867229422884916456347)
  ·
    refine ⟨420323800844134327374684521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280215867229422884916456347 420323800844134327374684521)
    ·
      refine ⟨315242850633100745531013391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420323800844134327374684521 315242850633100745531013391)
      ·
        refine ⟨472864275949651118296520087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315242850633100745531013391 472864275949651118296520087)
        ·
          refine ⟨709296413924476677444780131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472864275949651118296520087 709296413924476677444780131)
          ·
            refine ⟨1063944620886715016167170197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709296413924476677444780131 1063944620886715016167170197)
            ·
              refine ⟨49872404104064766382836103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1063944620886715016167170197 49872404104064766382836103)
              ·
                refine ⟨74808606156097149574254155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49872404104064766382836103 74808606156097149574254155)
                ·
                  refine ⟨112212909234145724361381233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74808606156097149574254155 112212909234145724361381233)
                  ·
                    refine ⟨84159681925609293271035925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112212909234145724361381233 84159681925609293271035925)
                    ·
                      refine ⟨3944985090262935622079809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84159681925609293271035925 3944985090262935622079809)
                      ·
                        rfl

theorem cell23_7682831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_7682831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682831 prefixEnd_7682831 := by exact prefixLift 7682831
  have htrace : WordTrace (prefixWord ++ tailWord_7682831) baseStart_7682831 baseEnd_7682831 := by
    simpa [prefixWord, tailWord_7682831, baseEnd_7682831] using wordTrace_append hprefix tailTrace_7682831
  have hstable : (prefixWord ++ tailWord_7682831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682831).length < 2 ^ (prefixWord ++ tailWord_7682831).sum := by decide
  have hdescent : baseEnd_7682831 < baseStart_7682831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682851 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 7]
def baseStart_7682851 : Nat := 118140960795 + 7682851 * 2 ^ 59
def prefixEnd_7682851 : Nat := 4983230072969 + 3 ^ 40 * 7682851 * 2
def baseEnd_7682851 : Nat := 3944995359876025543829717

theorem tailTrace_7682851 : CollatzResearch.WordTrace tailWord_7682851 prefixEnd_7682851 3944995359876025543829717 := by
  unfold tailWord_7682851
  simp only [CollatzResearch.WordTrace]
  refine ⟨280216596689350428332184407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186811064459566952221456271 280216596689350428332184407)
  ·
    refine ⟨420324895034025642498276611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280216596689350428332184407 420324895034025642498276611)
    ·
      refine ⟨630487342551038463747414917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420324895034025642498276611 630487342551038463747414917)
      ·
        refine ⟨118216376728319711952640297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 630487342551038463747414917 118216376728319711952640297)
        ·
          refine ⟨88662282546239783964480223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118216376728319711952640297 88662282546239783964480223)
          ·
            refine ⟨132993423819359675946720335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88662282546239783964480223 132993423819359675946720335)
            ·
              refine ⟨199490135729039513920080503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132993423819359675946720335 199490135729039513920080503)
              ·
                refine ⟨299235203593559270880120755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199490135729039513920080503 299235203593559270880120755)
                ·
                  refine ⟨448852805390338906320181133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299235203593559270880120755 448852805390338906320181133)
                  ·
                    refine ⟨168319802021377089870067925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 448852805390338906320181133 168319802021377089870067925)
                    ·
                      refine ⟨3944995359876025543829717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168319802021377089870067925 3944995359876025543829717)
                      ·
                        rfl

theorem cell23_7682851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_7682851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682851 prefixEnd_7682851 := by exact prefixLift 7682851
  have htrace : WordTrace (prefixWord ++ tailWord_7682851) baseStart_7682851 baseEnd_7682851 := by
    simpa [prefixWord, tailWord_7682851, baseEnd_7682851] using wordTrace_append hprefix tailTrace_7682851
  have hstable : (prefixWord ++ tailWord_7682851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682851).length < 2 ^ (prefixWord ++ tailWord_7682851).sum := by decide
  have hdescent : baseEnd_7682851 < baseStart_7682851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682865 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 1, 5, 2]
def baseStart_7682865 : Nat := 118140960795 + 7682865 * 2 ^ 59
def prefixEnd_7682865 : Nat := 4983230072969 + 3 ^ 40 * 7682865 * 2
def baseEnd_7682865 : Nat := 3945002548605188489054653

theorem tailTrace_7682865 : CollatzResearch.WordTrace tailWord_7682865 prefixEnd_7682865 3945002548605188489054653 := by
  unfold tailWord_7682865
  simp only [CollatzResearch.WordTrace]
  refine ⟨280217107311299708723194049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186811404874199805815462699 280217107311299708723194049)
  ·
    refine ⟨210162830483474781542395537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280217107311299708723194049 210162830483474781542395537)
    ·
      refine ⟨157622122862606086156796653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210162830483474781542395537 157622122862606086156796653)
      ·
        refine ⟨59108296073477282308798745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157622122862606086156796653 59108296073477282308798745)
        ·
          refine ⟨44331222055107961731599059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59108296073477282308798745 44331222055107961731599059)
          ·
            refine ⟨66496833082661942597398589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44331222055107961731599059 66496833082661942597398589)
            ·
              refine ⟨24936312405998228474024471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66496833082661942597398589 24936312405998228474024471)
              ·
                refine ⟨37404468608997342711036707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24936312405998228474024471 37404468608997342711036707)
                ·
                  refine ⟨56106702913496014066555061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37404468608997342711036707 56106702913496014066555061)
                  ·
                    refine ⟨5260003398140251318739537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56106702913496014066555061 5260003398140251318739537)
                    ·
                      refine ⟨3945002548605188489054653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260003398140251318739537 3945002548605188489054653)
                      ·
                        rfl

theorem cell23_7682865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_7682865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682865 prefixEnd_7682865 := by exact prefixLift 7682865
  have htrace : WordTrace (prefixWord ++ tailWord_7682865) baseStart_7682865 baseEnd_7682865 := by
    simpa [prefixWord, tailWord_7682865, baseEnd_7682865] using wordTrace_append hprefix tailTrace_7682865
  have hstable : (prefixWord ++ tailWord_7682865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682865).length < 2 ^ (prefixWord ++ tailWord_7682865).sum := by decide
  have hdescent : baseEnd_7682865 < baseStart_7682865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682905 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 1, 6]
def baseStart_7682905 : Nat := 118140960795 + 7682905 * 2 ^ 59
def prefixEnd_7682905 : Nat := 4983230072969 + 3 ^ 40 * 7682905 * 2
def baseEnd_7682905 : Nat := 1315007695943789444184823

theorem tailTrace_7682905 : CollatzResearch.WordTrace tailWord_7682905 prefixEnd_7682905 1315007695943789444184823 := by
  unfold tailWord_7682905
  simp only [CollatzResearch.WordTrace]
  refine ⟨280218566231154795554650169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186812377487436530369766779 280218566231154795554650169)
  ·
    refine ⟨210163924673366096665987627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280218566231154795554650169 210163924673366096665987627)
    ·
      refine ⟨315245887010049144998981441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210163924673366096665987627 315245887010049144998981441)
      ·
        refine ⟨236434415257536858749236081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315245887010049144998981441 236434415257536858749236081)
        ·
          refine ⟨177325811443152644061927061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236434415257536858749236081 177325811443152644061927061)
          ·
            refine ⟨8312147411397780190402831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177325811443152644061927061 8312147411397780190402831)
            ·
              refine ⟨12468221117096670285604247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8312147411397780190402831 12468221117096670285604247)
              ·
                refine ⟨18702331675645005428406371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12468221117096670285604247 18702331675645005428406371)
                ·
                  refine ⟨28053497513467508142609557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18702331675645005428406371 28053497513467508142609557)
                  ·
                    refine ⟨1315007695943789444184823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28053497513467508142609557 1315007695943789444184823)
                    ·
                      rfl

theorem cell23_7682905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 6].length) (baseStart_7682905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682905 prefixEnd_7682905 := by exact prefixLift 7682905
  have htrace : WordTrace (prefixWord ++ tailWord_7682905) baseStart_7682905 baseEnd_7682905 := by
    simpa [prefixWord, tailWord_7682905, baseEnd_7682905] using wordTrace_append hprefix tailTrace_7682905
  have hstable : (prefixWord ++ tailWord_7682905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682905).length < 2 ^ (prefixWord ++ tailWord_7682905).sum := by decide
  have hdescent : baseEnd_7682905 < baseStart_7682905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682912 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 3, 2, 2]
def baseStart_7682912 : Nat := 118140960795 + 7682912 * 2 ^ 59
def prefixEnd_7682912 : Nat := 4983230072969 + 3 ^ 40 * 7682912 * 2
def baseEnd_7682912 : Nat := 3945026682195949805166937

theorem tailTrace_7682912 : CollatzResearch.WordTrace tailWord_7682912 prefixEnd_7682912 3945026682195949805166937 := by
  unfold tailWord_7682912
  simp only [CollatzResearch.WordTrace]
  refine ⟨140109410771064717875077495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186812547694752957166769993 140109410771064717875077495)
  ·
    refine ⟨210164116156597076812616243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140109410771064717875077495 210164116156597076812616243)
    ·
      refine ⟨315246174234895615218924365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210164116156597076812616243 315246174234895615218924365)
      ·
        refine ⟨118217315338085855707096637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315246174234895615218924365 118217315338085855707096637)
        ·
          refine ⟨44331493251782195890161239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118217315338085855707096637 44331493251782195890161239)
          ·
            refine ⟨66497239877673293835241859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44331493251782195890161239 66497239877673293835241859)
            ·
              refine ⟨99745859816509940752862789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66497239877673293835241859 99745859816509940752862789)
              ·
                refine ⟨18702348715595613891161773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99745859816509940752862789 18702348715595613891161773)
                ·
                  refine ⟨7013380768348355209185665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18702348715595613891161773 7013380768348355209185665)
                  ·
                    refine ⟨5260035576261266406889249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7013380768348355209185665 5260035576261266406889249)
                    ·
                      refine ⟨3945026682195949805166937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260035576261266406889249 3945026682195949805166937)
                      ·
                        rfl

theorem cell23_7682912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_7682912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682912 prefixEnd_7682912 := by exact prefixLift 7682912
  have htrace : WordTrace (prefixWord ++ tailWord_7682912) baseStart_7682912 baseEnd_7682912 := by
    simpa [prefixWord, tailWord_7682912, baseEnd_7682912] using wordTrace_append hprefix tailTrace_7682912
  have hstable : (prefixWord ++ tailWord_7682912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682912).length < 2 ^ (prefixWord ++ tailWord_7682912).sum := by decide
  have hdescent : baseEnd_7682912 < baseStart_7682912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682948 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_7682948 : Nat := 118140960795 + 7682948 * 2 ^ 59
def prefixEnd_7682948 : Nat := 4983230072969 + 3 ^ 40 * 7682948 * 2
def baseEnd_7682948 : Nat := 1315015055833170554772257

theorem tailTrace_7682948 : CollatzResearch.WordTrace tailWord_7682948 prefixEnd_7682948 1315015055833170554772257 := by
  unfold tailWord_7682948
  simp only [CollatzResearch.WordTrace]
  refine ⟨140110067284999506949232749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186813423046666009265643665 140110067284999506949232749)
  ·
    refine ⟨52541275231874815105962281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140110067284999506949232749 52541275231874815105962281)
    ·
      refine ⟨39405956423906111329471711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52541275231874815105962281 39405956423906111329471711)
      ·
        refine ⟨59108934635859166994207567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39405956423906111329471711 59108934635859166994207567)
        ·
          refine ⟨88663401953788750491311351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59108934635859166994207567 88663401953788750491311351)
          ·
            refine ⟨132995102930683125736967027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88663401953788750491311351 132995102930683125736967027)
            ·
              refine ⟨199492654396024688605450541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132995102930683125736967027 199492654396024688605450541)
              ·
                refine ⟨74809745398509258227043953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199492654396024688605450541 74809745398509258227043953)
                ·
                  refine ⟨56107309048881943670282965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74809745398509258227043953 56107309048881943670282965)
                  ·
                    refine ⟨1315015055833170554772257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56107309048881943670282965 1315015055833170554772257)
                    ·
                      rfl

theorem cell23_7682948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_7682948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682948 prefixEnd_7682948 := by exact prefixLift 7682948
  have htrace : WordTrace (prefixWord ++ tailWord_7682948) baseStart_7682948 baseEnd_7682948 := by
    simpa [prefixWord, tailWord_7682948, baseEnd_7682948] using wordTrace_append hprefix tailTrace_7682948
  have hstable : (prefixWord ++ tailWord_7682948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682948).length < 2 ^ (prefixWord ++ tailWord_7682948).sum := by decide
  have hdescent : baseEnd_7682948 < baseStart_7682948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682966 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7682966 : Nat := 118140960795 + 7682966 * 2 ^ 59
def prefixEnd_7682966 : Nat := 4983230072969 + 3 ^ 40 * 7682966 * 2
def baseEnd_7682966 : Nat := 3945054410151292593891689

theorem tailTrace_7682966 : CollatzResearch.WordTrace tailWord_7682966 prefixEnd_7682966 3945054410151292593891689 := by
  unfold tailWord_7682966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17513799442745862685788797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186813860722622535315080501 17513799442745862685788797)
  ·
    refine ⟨6567674791029698507170799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17513799442745862685788797 6567674791029698507170799)
    ·
      refine ⟨9851512186544547760756199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6567674791029698507170799 9851512186544547760756199)
      ·
        refine ⟨14777268279816821641134299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9851512186544547760756199 14777268279816821641134299)
        ·
          refine ⟨22165902419725232461701449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14777268279816821641134299 22165902419725232461701449)
          ·
            refine ⟨16624426814793924346276087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22165902419725232461701449 16624426814793924346276087)
            ·
              refine ⟨24936640222190886519414131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16624426814793924346276087 24936640222190886519414131)
              ·
                refine ⟨37404960333286329779121197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24936640222190886519414131 37404960333286329779121197)
                ·
                  refine ⟨14026860124982373667170449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37404960333286329779121197 14026860124982373667170449)
                  ·
                    refine ⟨10520145093736780250377837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14026860124982373667170449 10520145093736780250377837)
                    ·
                      refine ⟨3945054410151292593891689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10520145093736780250377837 3945054410151292593891689)
                      ·
                        rfl

theorem cell23_7682966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7682966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682966 prefixEnd_7682966 := by exact prefixLift 7682966
  have htrace : WordTrace (prefixWord ++ tailWord_7682966) baseStart_7682966 baseEnd_7682966 := by
    simpa [prefixWord, tailWord_7682966, baseEnd_7682966] using wordTrace_append hprefix tailTrace_7682966
  have hstable : (prefixWord ++ tailWord_7682966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682966).length < 2 ^ (prefixWord ++ tailWord_7682966).sum := by decide
  have hdescent : baseEnd_7682966 < baseStart_7682966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7682996 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_7682996 : Nat := 118140960795 + 7682996 * 2 ^ 59
def prefixEnd_7682996 : Nat := 4983230072969 + 3 ^ 40 * 7682996 * 2
def baseEnd_7682996 : Nat := 3945069814570927476516551

theorem tailTrace_7682996 : CollatzResearch.WordTrace tailWord_7682996 prefixEnd_7682996 3945069814570927476516551 := by
  unfold tailWord_7682996
  simp only [CollatzResearch.WordTrace]
  refine ⟨140110942636912559048106421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186814590182550078730808561 140110942636912559048106421)
  ·
    refine ⟨13135400872210552410759977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140110942636912559048106421 13135400872210552410759977)
    ·
      refine ⟨9851550654157914308069983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13135400872210552410759977 9851550654157914308069983)
      ·
        refine ⟨14777325981236871462104975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9851550654157914308069983 14777325981236871462104975)
        ·
          refine ⟨22165988971855307193157463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14777325981236871462104975 22165988971855307193157463)
          ·
            refine ⟨33248983457782960789736195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22165988971855307193157463 33248983457782960789736195)
            ·
              refine ⟨49873475186674441184604293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33248983457782960789736195 49873475186674441184604293)
              ·
                refine ⟨9351276597501457722113305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49873475186674441184604293 9351276597501457722113305)
                ·
                  refine ⟨7013457448126093291584979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9351276597501457722113305 7013457448126093291584979)
                  ·
                    refine ⟨10520186172189139937377469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7013457448126093291584979 10520186172189139937377469)
                    ·
                      refine ⟨3945069814570927476516551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10520186172189139937377469 3945069814570927476516551)
                      ·
                        rfl

theorem cell23_7682996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_7682996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7682996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7682996 prefixEnd_7682996 := by exact prefixLift 7682996
  have htrace : WordTrace (prefixWord ++ tailWord_7682996) baseStart_7682996 baseEnd_7682996 := by
    simpa [prefixWord, tailWord_7682996, baseEnd_7682996] using wordTrace_append hprefix tailTrace_7682996
  have hstable : (prefixWord ++ tailWord_7682996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7682996).length < 2 ^ (prefixWord ++ tailWord_7682996).sum := by decide
  have hdescent : baseEnd_7682996 < baseStart_7682996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7682996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683019 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 2, 2, 2]
def baseStart_7683019 : Nat := 118140960795 + 7683019 * 2 ^ 59
def prefixEnd_7683019 : Nat := 4983230072969 + 3 ^ 40 * 7683019 * 2
def baseEnd_7683019 : Nat := 3945081624625980886528945

theorem tailTrace_7683019 : CollatzResearch.WordTrace tailWord_7683019 prefixEnd_7683019 3945081624625980886528945 := by
  unfold tailWord_7683019
  simp only [CollatzResearch.WordTrace]
  refine ⟨280222724152741793024300111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186815149435161195349533407 280222724152741793024300111)
  ·
    refine ⟨420334086229112689536450167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280222724152741793024300111 420334086229112689536450167)
    ·
      refine ⟨630501129343669034304675251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420334086229112689536450167 630501129343669034304675251)
      ·
        refine ⟨945751694015503551457012877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630501129343669034304675251 945751694015503551457012877)
        ·
          refine ⟨354656885255813831796379829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 945751694015503551457012877 354656885255813831796379829)
          ·
            refine ⟨33249082992732546730910609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 354656885255813831796379829 33249082992732546730910609)
            ·
              refine ⟨24936812244549410048182957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33249082992732546730910609 24936812244549410048182957)
              ·
                refine ⟨9351304591706028768068609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24936812244549410048182957 9351304591706028768068609)
                ·
                  refine ⟨7013478443779521576051457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9351304591706028768068609 7013478443779521576051457)
                  ·
                    refine ⟨5260108832834641182038593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7013478443779521576051457 5260108832834641182038593)
                    ·
                      refine ⟨3945081624625980886528945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260108832834641182038593 3945081624625980886528945)
                      ·
                        rfl

theorem cell23_7683019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 2, 2].length) (baseStart_7683019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683019 prefixEnd_7683019 := by exact prefixLift 7683019
  have htrace : WordTrace (prefixWord ++ tailWord_7683019) baseStart_7683019 baseEnd_7683019 := by
    simpa [prefixWord, tailWord_7683019, baseEnd_7683019] using wordTrace_append hprefix tailTrace_7683019
  have hstable : (prefixWord ++ tailWord_7683019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683019).length < 2 ^ (prefixWord ++ tailWord_7683019).sum := by decide
  have hdescent : baseEnd_7683019 < baseStart_7683019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683070 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7683070 : Nat := 118140960795 + 7683070 * 2 ^ 59
def prefixEnd_7683070 : Nat := 4983230072969 + 3 ^ 40 * 7683070 * 2
def baseEnd_7683070 : Nat := 3945107812139360186991211

theorem tailTrace_7683070 : CollatzResearch.WordTrace tailWord_7683070 prefixEnd_7683070 3945107812139360186991211 := by
  unfold tailWord_7683070
  simp only [CollatzResearch.WordTrace]
  refine ⟨35028073034444628591800833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186816389517038019156271109 35028073034444628591800833)
  ·
    refine ⟨26271054775833471443850625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35028073034444628591800833 26271054775833471443850625)
    ·
      refine ⟨19703291081875103582887969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26271054775833471443850625 19703291081875103582887969)
      ·
        refine ⟨14777468311406327687165977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19703291081875103582887969 14777468311406327687165977)
        ·
          refine ⟨11083101233554745765374483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14777468311406327687165977 11083101233554745765374483)
          ·
            refine ⟨16624651850332118648061725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11083101233554745765374483 16624651850332118648061725)
            ·
              refine ⟨6234244443874544493023147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16624651850332118648061725 6234244443874544493023147)
              ·
                refine ⟨9351366665811816739534721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234244443874544493023147 9351366665811816739534721)
                ·
                  refine ⟨7013524999358862554651041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9351366665811816739534721 7013524999358862554651041)
                  ·
                    refine ⟨5260143749519146915988281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7013524999358862554651041 5260143749519146915988281)
                    ·
                      refine ⟨3945107812139360186991211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260143749519146915988281 3945107812139360186991211)
                      ·
                        rfl

theorem cell23_7683070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7683070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683070 prefixEnd_7683070 := by exact prefixLift 7683070
  have htrace : WordTrace (prefixWord ++ tailWord_7683070) baseStart_7683070 baseEnd_7683070 := by
    simpa [prefixWord, tailWord_7683070, baseEnd_7683070] using wordTrace_append hprefix tailTrace_7683070
  have hstable : (prefixWord ++ tailWord_7683070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683070).length < 2 ^ (prefixWord ++ tailWord_7683070).sum := by decide
  have hdescent : baseEnd_7683070 < baseStart_7683070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683115 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 6]
def baseStart_7683115 : Nat := 118140960795 + 7683115 * 2 ^ 59
def prefixEnd_7683115 : Nat := 4983230072969 + 3 ^ 40 * 7683115 * 2
def baseEnd_7683115 : Nat := 438347879863201390103167

theorem tailTrace_7683115 : CollatzResearch.WordTrace tailWord_7683115 prefixEnd_7683115 438347879863201390103167 := by
  unfold tailWord_7683115
  simp only [CollatzResearch.WordTrace]
  refine ⟨280226225560394001419794799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186817483706929334279863199 280226225560394001419794799)
  ·
    refine ⟨420339338340591002129692199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280226225560394001419794799 420339338340591002129692199)
    ·
      refine ⟨630509007510886503194538299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420339338340591002129692199 630509007510886503194538299)
      ·
        refine ⟨945763511266329754791807449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630509007510886503194538299 945763511266329754791807449)
        ·
          refine ⟨709322633449747316093855587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945763511266329754791807449 709322633449747316093855587)
          ·
            refine ⟨1063983950174620974140783381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709322633449747316093855587 1063983950174620974140783381)
            ·
              refine ⟨49874247664435358162849221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1063983950174620974140783381 49874247664435358162849221)
              ·
                refine ⟨9351421437081629655534229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49874247664435358162849221 9351421437081629655534229)
                ·
                  refine ⟨438347879863201390103167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9351421437081629655534229 438347879863201390103167)
                  ·
                    rfl

theorem cell23_7683115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 6].length) (baseStart_7683115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683115 prefixEnd_7683115 := by exact prefixLift 7683115
  have htrace : WordTrace (prefixWord ++ tailWord_7683115) baseStart_7683115 baseEnd_7683115 := by
    simpa [prefixWord, tailWord_7683115, baseEnd_7683115] using wordTrace_append hprefix tailTrace_7683115
  have hstable : (prefixWord ++ tailWord_7683115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683115).length < 2 ^ (prefixWord ++ tailWord_7683115).sum := by decide
  have hdescent : baseEnd_7683115 < baseStart_7683115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683132 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 6]
def baseStart_7683132 : Nat := 118140960795 + 7683132 * 2 ^ 59
def prefixEnd_7683132 : Nat := 4983230072969 + 3 ^ 40 * 7683132 * 2
def baseEnd_7683132 : Nat := 438348849771104327157325

theorem tailTrace_7683132 : CollatzResearch.WordTrace tailWord_7683132 prefixEnd_7683132 438348849771104327157325 := by
  unfold tailWord_7683132
  simp only [CollatzResearch.WordTrace]
  refine ⟨140113422800666206661581825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186817897067554942215442433 140113422800666206661581825)
  ·
    refine ⟨105085067100499654996186369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140113422800666206661581825 105085067100499654996186369)
    ·
      refine ⟨78813800325374741247139777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105085067100499654996186369 78813800325374741247139777)
      ·
        refine ⟨59110350244031055935354833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78813800325374741247139777 59110350244031055935354833)
        ·
          refine ⟨44332762683023291951516125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59110350244031055935354833 44332762683023291951516125)
          ·
            refine ⟨16624786006133734481818547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44332762683023291951516125 16624786006133734481818547)
            ·
              refine ⟨24937179009200601722727821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16624786006133734481818547 24937179009200601722727821)
              ·
                refine ⟨9351442128450225646022933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24937179009200601722727821 9351442128450225646022933)
                ·
                  refine ⟨438348849771104327157325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9351442128450225646022933 438348849771104327157325)
                  ·
                    rfl

theorem cell23_7683132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_7683132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683132 prefixEnd_7683132 := by exact prefixLift 7683132
  have htrace : WordTrace (prefixWord ++ tailWord_7683132) baseStart_7683132 baseEnd_7683132 := by
    simpa [prefixWord, tailWord_7683132, baseEnd_7683132] using wordTrace_append hprefix tailTrace_7683132
  have hstable : (prefixWord ++ tailWord_7683132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683132).length < 2 ^ (prefixWord ++ tailWord_7683132).sum := by decide
  have hdescent : baseEnd_7683132 < baseStart_7683132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683152 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 1, 5, 2]
def baseStart_7683152 : Nat := 118140960795 + 7683152 * 2 ^ 59
def prefixEnd_7683152 : Nat := 4983230072969 + 3 ^ 40 * 7683152 * 2
def baseEnd_7683152 : Nat := 3945149917553028866165833

theorem tailTrace_7683152 : CollatzResearch.WordTrace tailWord_7683152 prefixEnd_7683152 3945149917553028866165833 := by
  unfold tailWord_7683152
  simp only [CollatzResearch.WordTrace]
  refine ⟨140113787530629978369445855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186818383374173304492594473 140113787530629978369445855)
  ·
    refine ⟨210170681295944967554168783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140113787530629978369445855 210170681295944967554168783)
    ·
      refine ⟨315256021943917451331253175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210170681295944967554168783 315256021943917451331253175)
      ·
        refine ⟨472884032915876176996879763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315256021943917451331253175 472884032915876176996879763)
        ·
          refine ⟨709326049373814265495319645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472884032915876176996879763 709326049373814265495319645)
          ·
            refine ⟨265997268515180349560744867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 709326049373814265495319645 265997268515180349560744867)
            ·
              refine ⟨398995902772770524341117301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265997268515180349560744867 398995902772770524341117301)
              ·
                refine ⟨37405865884947236656979747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398995902772770524341117301 37405865884947236656979747)
                ·
                  refine ⟨56108798827420854985469621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37405865884947236656979747 56108798827420854985469621)
                  ·
                    refine ⟨5260199890070705154887777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56108798827420854985469621 5260199890070705154887777)
                    ·
                      refine ⟨3945149917553028866165833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260199890070705154887777 3945149917553028866165833)
                      ·
                        rfl

theorem cell23_7683152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 5, 2].length) (baseStart_7683152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683152 prefixEnd_7683152 := by exact prefixLift 7683152
  have htrace : WordTrace (prefixWord ++ tailWord_7683152) baseStart_7683152 baseEnd_7683152 := by
    simpa [prefixWord, tailWord_7683152, baseEnd_7683152] using wordTrace_append hprefix tailTrace_7683152
  have hstable : (prefixWord ++ tailWord_7683152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683152).length < 2 ^ (prefixWord ++ tailWord_7683152).sum := by decide
  have hdescent : baseEnd_7683152 < baseStart_7683152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683166 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_7683166 : Nat := 118140960795 + 7683166 * 2 ^ 59
def prefixEnd_7683166 : Nat := 4983230072969 + 3 ^ 40 * 7683166 * 2
def baseEnd_7683166 : Nat := 438350789586910201265641

theorem tailTrace_7683166 : CollatzResearch.WordTrace tailWord_7683166 prefixEnd_7683166 438350789586910201265641 := by
  unfold tailWord_7683166
  simp only [CollatzResearch.WordTrace]
  refine ⟨35028510710401154641237669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186818723788806158086600901 35028510710401154641237669)
  ·
    refine ⟨6567845758200216495232063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35028510710401154641237669 6567845758200216495232063)
    ·
      refine ⟨9851768637300324742848095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6567845758200216495232063 9851768637300324742848095)
      ·
        refine ⟨14777652955950487114272143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9851768637300324742848095 14777652955950487114272143)
        ·
          refine ⟨22166479433925730671408215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14777652955950487114272143 22166479433925730671408215)
          ·
            refine ⟨33249719150888596007112323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22166479433925730671408215 33249719150888596007112323)
            ·
              refine ⟨49874578726332894010668485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33249719150888596007112323 49874578726332894010668485)
              ·
                refine ⟨9351483511187417627000341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49874578726332894010668485 9351483511187417627000341)
                ·
                  refine ⟨438350789586910201265641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9351483511187417627000341 438350789586910201265641)
                  ·
                    rfl

theorem cell23_7683166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_7683166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683166 prefixEnd_7683166 := by exact prefixLift 7683166
  have htrace : WordTrace (prefixWord ++ tailWord_7683166) baseStart_7683166 baseEnd_7683166 := by
    simpa [prefixWord, tailWord_7683166, baseEnd_7683166] using wordTrace_append hprefix tailTrace_7683166
  have hstable : (prefixWord ++ tailWord_7683166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683166).length < 2 ^ (prefixWord ++ tailWord_7683166).sum := by decide
  have hdescent : baseEnd_7683166 < baseStart_7683166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683169 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 2, 3, 2]
def baseStart_7683169 : Nat := 118140960795 + 7683169 * 2 ^ 59
def prefixEnd_7683169 : Nat := 4983230072969 + 3 ^ 40 * 7683169 * 2
def baseEnd_7683169 : Nat := 3945158646724155299653255

theorem tailTrace_7683169 : CollatzResearch.WordTrace tailWord_7683169 prefixEnd_7683169 3945158646724155299653255 := by
  unfold tailWord_7683169
  simp only [CollatzResearch.WordTrace]
  refine ⟨280228195102198368642260561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186818796734798912428173707 280228195102198368642260561)
  ·
    refine ⟨210171146326648776481695421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280228195102198368642260561 210171146326648776481695421)
    ·
      refine ⟨78814179872493291180635783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210171146326648776481695421 78814179872493291180635783)
      ·
        refine ⟨118221269808739936770953675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78814179872493291180635783 118221269808739936770953675)
        ·
          refine ⟨177331904713109905156430513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118221269808739936770953675 177331904713109905156430513)
          ·
            refine ⟨132998928534832428867322885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177331904713109905156430513 132998928534832428867322885)
            ·
              refine ⟨24937299100281080412623041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132998928534832428867322885 24937299100281080412623041)
              ·
                refine ⟨18702974325210810309467281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24937299100281080412623041 18702974325210810309467281)
                ·
                  refine ⟨14027230743908107732100461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18702974325210810309467281 14027230743908107732100461)
                  ·
                    refine ⟨5260211528965540399537673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14027230743908107732100461 5260211528965540399537673)
                    ·
                      refine ⟨3945158646724155299653255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260211528965540399537673 3945158646724155299653255)
                      ·
                        rfl

theorem cell23_7683169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_7683169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683169 prefixEnd_7683169 := by exact prefixLift 7683169
  have htrace : WordTrace (prefixWord ++ tailWord_7683169) baseStart_7683169 baseEnd_7683169 := by
    simpa [prefixWord, tailWord_7683169, baseEnd_7683169] using wordTrace_append hprefix tailTrace_7683169
  have hstable : (prefixWord ++ tailWord_7683169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683169).length < 2 ^ (prefixWord ++ tailWord_7683169).sum := by decide
  have hdescent : baseEnd_7683169 < baseStart_7683169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683170 : List Nat := [3, 3, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_7683170 : Nat := 118140960795 + 7683170 * 2 ^ 59
def prefixEnd_7683170 : Nat := 4983230072969 + 3 ^ 40 * 7683170 * 2
def baseEnd_7683170 : Nat := 1315053053401603265246917

theorem tailTrace_7683170 : CollatzResearch.WordTrace tailWord_7683170 prefixEnd_7683170 1315053053401603265246917 := by
  unfold tailWord_7683170
  simp only [CollatzResearch.WordTrace]
  refine ⟨70057057893798686453261741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186818821050129830542031309 70057057893798686453261741)
  ·
    refine ⟨26271396710174507419973153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70057057893798686453261741 26271396710174507419973153)
    ·
      refine ⟨19703547532630880564979865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26271396710174507419973153 19703547532630880564979865)
      ·
        refine ⟨14777660649473160423734899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19703547532630880564979865 14777660649473160423734899)
        ·
          refine ⟨22166490974209740635602349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14777660649473160423734899 22166490974209740635602349)
          ·
            refine ⟨8312434115328652738350881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22166490974209740635602349 8312434115328652738350881)
            ·
              refine ⟨6234325586496489553763161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8312434115328652738350881 6234325586496489553763161)
              ·
                refine ⟨4675744189872367165322371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6234325586496489553763161 4675744189872367165322371)
                ·
                  refine ⟨7013616284808550747983557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675744189872367165322371 7013616284808550747983557)
                  ·
                    refine ⟨1315053053401603265246917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7013616284808550747983557 1315053053401603265246917)
                    ·
                      rfl

theorem cell23_7683170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_7683170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683170 prefixEnd_7683170 := by exact prefixLift 7683170
  have htrace : WordTrace (prefixWord ++ tailWord_7683170) baseStart_7683170 baseEnd_7683170 := by
    simpa [prefixWord, tailWord_7683170, baseEnd_7683170] using wordTrace_append hprefix tailTrace_7683170
  have hstable : (prefixWord ++ tailWord_7683170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683170).length < 2 ^ (prefixWord ++ tailWord_7683170).sum := by decide
  have hdescent : baseEnd_7683170 < baseStart_7683170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683195 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 6]
def baseStart_7683195 : Nat := 118140960795 + 7683195 * 2 ^ 59
def prefixEnd_7683195 : Nat := 4983230072969 + 3 ^ 40 * 7683195 * 2
def baseEnd_7683195 : Nat := 3945171997221172197928135

theorem tailTrace_7683195 : CollatzResearch.WordTrace tailWord_7683195 prefixEnd_7683195 3945171997221172197928135 := by
  unfold tailWord_7683195
  simp only [CollatzResearch.WordTrace]
  refine ⟨280229143400104175082707039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186819428933402783388471359 280229143400104175082707039)
  ·
    refine ⟨420343715100156262624060559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280229143400104175082707039 420343715100156262624060559)
    ·
      refine ⟨630515572650234393936090839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420343715100156262624060559 630515572650234393936090839)
      ·
        refine ⟨945773358975351590904136259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630515572650234393936090839 945773358975351590904136259)
        ·
          refine ⟨1418660038463027386356204389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945773358975351590904136259 1418660038463027386356204389)
          ·
            refine ⟨265998757211817634941788323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1418660038463027386356204389 265998757211817634941788323)
            ·
              refine ⟨398998135817726452412682485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265998757211817634941788323 398998135817726452412682485)
              ·
                refine ⟨37406075232911854913688983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398998135817726452412682485 37406075232911854913688983)
                ·
                  refine ⟨56109112849367782370533475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37406075232911854913688983 56109112849367782370533475)
                  ·
                    refine ⟨84163669274051673555800213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56109112849367782370533475 84163669274051673555800213)
                    ·
                      refine ⟨3945171997221172197928135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84163669274051673555800213 3945171997221172197928135)
                      ·
                        rfl

theorem cell23_7683195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 6].length) (baseStart_7683195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683195 prefixEnd_7683195 := by exact prefixLift 7683195
  have htrace : WordTrace (prefixWord ++ tailWord_7683195) baseStart_7683195 baseEnd_7683195 := by
    simpa [prefixWord, tailWord_7683195, baseEnd_7683195] using wordTrace_append hprefix tailTrace_7683195
  have hstable : (prefixWord ++ tailWord_7683195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683195).length < 2 ^ (prefixWord ++ tailWord_7683195).sum := by decide
  have hdescent : baseEnd_7683195 < baseStart_7683195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683225 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_7683225 : Nat := 118140960795 + 7683225 * 2 ^ 59
def prefixEnd_7683225 : Nat := 4983230072969 + 3 ^ 40 * 7683225 * 2
def baseEnd_7683225 : Nat := 3945187401640807080552997

theorem tailTrace_7683225 : CollatzResearch.WordTrace tailWord_7683225 prefixEnd_7683225 3945187401640807080552997 := by
  unfold tailWord_7683225
  simp only [CollatzResearch.WordTrace]
  refine ⟨280230237589995490206299129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186820158393330326804199419 280230237589995490206299129)
  ·
    refine ⟨210172678192496617654724347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280230237589995490206299129 210172678192496617654724347)
    ·
      refine ⟨315259017288744926482086521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210172678192496617654724347 315259017288744926482086521)
      ·
        refine ⟨236444262966558694861564891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315259017288744926482086521 236444262966558694861564891)
        ·
          refine ⟨354666394449838042292347337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236444262966558694861564891 354666394449838042292347337)
          ·
            refine ⟨265999795837378531719260503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354666394449838042292347337 265999795837378531719260503)
            ·
              refine ⟨398999693756067797578890755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265999795837378531719260503 398999693756067797578890755)
              ·
                refine ⟨598499540634101696368336133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398999693756067797578890755 598499540634101696368336133)
                ·
                  refine ⟨112218663868894068069063025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 598499540634101696368336133 112218663868894068069063025)
                  ·
                    refine ⟨84163997901670551051797269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112218663868894068069063025 84163997901670551051797269)
                    ·
                      refine ⟨3945187401640807080552997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84163997901670551051797269 3945187401640807080552997)
                      ·
                        rfl

theorem cell23_7683225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_7683225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683225 prefixEnd_7683225 := by exact prefixLift 7683225
  have htrace : WordTrace (prefixWord ++ tailWord_7683225) baseStart_7683225 baseEnd_7683225 := by
    simpa [prefixWord, tailWord_7683225, baseEnd_7683225] using wordTrace_append hprefix tailTrace_7683225
  have hstable : (prefixWord ++ tailWord_7683225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683225).length < 2 ^ (prefixWord ++ tailWord_7683225).sum := by decide
  have hdescent : baseEnd_7683225 < baseStart_7683225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683226 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 2, 4]
def baseStart_7683226 : Nat := 118140960795 + 7683226 * 2 ^ 59
def prefixEnd_7683226 : Nat := 4983230072969 + 3 ^ 40 * 7683226 * 2
def baseEnd_7683226 : Nat := 1315062638373820525546831

theorem tailTrace_7683226 : CollatzResearch.WordTrace tailWord_7683226 prefixEnd_7683226 1315062638373820525546831 := by
  unfold tailWord_7683226
  simp only [CollatzResearch.WordTrace]
  refine ⟨70057568515747966844271383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186820182708661244918057021 70057568515747966844271383)
  ·
    refine ⟨105086352773621950266407075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70057568515747966844271383 105086352773621950266407075)
    ·
      refine ⟨157629529160432925399610613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105086352773621950266407075 157629529160432925399610613)
      ·
        refine ⟨14777768358790586756213495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157629529160432925399610613 14777768358790586756213495)
        ·
          refine ⟨22166652538185880134320243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14777768358790586756213495 22166652538185880134320243)
          ·
            refine ⟨33249978807278820201480365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22166652538185880134320243 33249978807278820201480365)
            ·
              refine ⟨12468742052729557575555137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33249978807278820201480365 12468742052729557575555137)
              ·
                refine ⟨9351556539547168181666353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12468742052729557575555137 9351556539547168181666353)
                ·
                  refine ⟨7013667404660376136249765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9351556539547168181666353 7013667404660376136249765)
                  ·
                    refine ⟨1315062638373820525546831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7013667404660376136249765 1315062638373820525546831)
                    ·
                      rfl

theorem cell23_7683226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_7683226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683226 prefixEnd_7683226 := by exact prefixLift 7683226
  have htrace : WordTrace (prefixWord ++ tailWord_7683226) baseStart_7683226 baseEnd_7683226 := by
    simpa [prefixWord, tailWord_7683226, baseEnd_7683226] using wordTrace_append hprefix tailTrace_7683226
  have hstable : (prefixWord ++ tailWord_7683226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683226).length < 2 ^ (prefixWord ++ tailWord_7683226).sum := by decide
  have hdescent : baseEnd_7683226 < baseStart_7683226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683233 : List Nat := [1, 2, 3, 3, 1, 1, 1, 6, 1, 2, 2]
def baseStart_7683233 : Nat := 118140960795 + 7683233 * 2 ^ 59
def prefixEnd_7683233 : Nat := 4983230072969 + 3 ^ 40 * 7683233 * 2
def baseEnd_7683233 : Nat := 3945191509486043049252961

theorem tailTrace_7683233 : CollatzResearch.WordTrace tailWord_7683233 prefixEnd_7683233 3945191509486043049252961 := by
  unfold tailWord_7683233
  simp only [CollatzResearch.WordTrace]
  refine ⟨280230529373966507572590353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186820352915977671715060235 280230529373966507572590353)
  ·
    refine ⟨210172897030474880679442765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280230529373966507572590353 210172897030474880679442765)
    ·
      refine ⟨78814836386428080254791037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210172897030474880679442765 78814836386428080254791037)
      ·
        refine ⟨29555563644910530095546639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78814836386428080254791037 29555563644910530095546639)
        ·
          refine ⟨44333345467365795143319959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29555563644910530095546639 44333345467365795143319959)
          ·
            refine ⟨66500018201048692714979939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44333345467365795143319959 66500018201048692714979939)
            ·
              refine ⟨99750027301573039072469909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66500018201048692714979939 99750027301573039072469909)
              ·
                refine ⟨4675782529761236206522027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99750027301573039072469909 4675782529761236206522027)
                ·
                  refine ⟨7013673794641854309783041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675782529761236206522027 7013673794641854309783041)
                  ·
                    refine ⟨5260255345981390732337281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7013673794641854309783041 5260255345981390732337281)
                    ·
                      refine ⟨3945191509486043049252961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260255345981390732337281 3945191509486043049252961)
                      ·
                        rfl

theorem cell23_7683233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_7683233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683233 prefixEnd_7683233 := by exact prefixLift 7683233
  have htrace : WordTrace (prefixWord ++ tailWord_7683233) baseStart_7683233 baseEnd_7683233 := by
    simpa [prefixWord, tailWord_7683233, baseEnd_7683233] using wordTrace_append hprefix tailTrace_7683233
  have hstable : (prefixWord ++ tailWord_7683233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683233).length < 2 ^ (prefixWord ++ tailWord_7683233).sum := by decide
  have hdescent : baseEnd_7683233 < baseStart_7683233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683235 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 1, 9]
def baseStart_7683235 : Nat := 118140960795 + 7683235 * 2 ^ 59
def prefixEnd_7683235 : Nat := 4983230072969 + 3 ^ 40 * 7683235 * 2
def baseEnd_7683235 : Nat := 1315064178815784013809317

theorem tailTrace_7683235 : CollatzResearch.WordTrace tailWord_7683235 prefixEnd_7683235 1315064178815784013809317 := by
  unfold tailWord_7683235
  simp only [CollatzResearch.WordTrace]
  refine ⟨280230602319959261914163159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186820401546639507942775439 280230602319959261914163159)
  ·
    refine ⟨420345903479938892871244739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280230602319959261914163159 420345903479938892871244739)
    ·
      refine ⟨630518855219908339306867109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420345903479938892871244739 630518855219908339306867109)
      ·
        refine ⟨118222285353732813620037583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 630518855219908339306867109 118222285353732813620037583)
        ·
          refine ⟨177333428030599220430056375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118222285353732813620037583 177333428030599220430056375)
          ·
            refine ⟨266000142045898830645084563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177333428030599220430056375 266000142045898830645084563)
            ·
              refine ⟨399000213068848245967626845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266000142045898830645084563 399000213068848245967626845)
              ·
                refine ⟨149625079900818092237860067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399000213068848245967626845 149625079900818092237860067)
                ·
                  refine ⟨224437619851227138356790101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149625079900818092237860067 224437619851227138356790101)
                  ·
                    refine ⟨1315064178815784013809317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 224437619851227138356790101 1315064178815784013809317)
                    ·
                      rfl

theorem cell23_7683235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 9].length) (baseStart_7683235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683235 prefixEnd_7683235 := by exact prefixLift 7683235
  have htrace : WordTrace (prefixWord ++ tailWord_7683235) baseStart_7683235 baseEnd_7683235 := by
    simpa [prefixWord, tailWord_7683235, baseEnd_7683235] using wordTrace_append hprefix tailTrace_7683235
  have hstable : (prefixWord ++ tailWord_7683235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683235).length < 2 ^ (prefixWord ++ tailWord_7683235).sum := by decide
  have hdescent : baseEnd_7683235 < baseStart_7683235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683270 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7683270 : Nat := 118140960795 + 7683270 * 2 ^ 59
def prefixEnd_7683270 : Nat := 4983230072969 + 3 ^ 40 * 7683270 * 2
def baseEnd_7683270 : Nat := 3945210508270259404490291

theorem tailTrace_7683270 : CollatzResearch.WordTrace tailWord_7683270 prefixEnd_7683270 3945210508270259404490291 := by
  unfold tailWord_7683270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8757246214838514465365227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186821252583221641927791509 8757246214838514465365227)
  ·
    refine ⟨13135869322257771698047841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8757246214838514465365227 13135869322257771698047841)
    ·
      refine ⟨9851901991693328773535881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13135869322257771698047841 9851901991693328773535881)
      ·
        refine ⟨7388926493769996580151911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9851901991693328773535881 7388926493769996580151911)
        ·
          refine ⟨11083389740654994870227867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7388926493769996580151911 11083389740654994870227867)
          ·
            refine ⟨16625084610982492305341801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11083389740654994870227867 16625084610982492305341801)
            ·
              refine ⟨12468813458236869229006351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16625084610982492305341801 12468813458236869229006351)
              ·
                refine ⟨18703220187355303843509527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12468813458236869229006351 18703220187355303843509527)
                ·
                  refine ⟨28054830281032955765264291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18703220187355303843509527 28054830281032955765264291)
                  ·
                    refine ⟨42082245421549433647896437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28054830281032955765264291 42082245421549433647896437)
                    ·
                      refine ⟨3945210508270259404490291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42082245421549433647896437 3945210508270259404490291)
                      ·
                        rfl

theorem cell23_7683270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7683270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683270 prefixEnd_7683270 := by exact prefixLift 7683270
  have htrace : WordTrace (prefixWord ++ tailWord_7683270) baseStart_7683270 baseEnd_7683270 := by
    simpa [prefixWord, tailWord_7683270, baseEnd_7683270] using wordTrace_append hprefix tailTrace_7683270
  have hstable : (prefixWord ++ tailWord_7683270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683270).length < 2 ^ (prefixWord ++ tailWord_7683270).sum := by decide
  have hdescent : baseEnd_7683270 < baseStart_7683270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683284 : List Nat := [2, 4, 1, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7683284 : Nat := 118140960795 + 7683284 * 2 ^ 59
def prefixEnd_7683284 : Nat := 4983230072969 + 3 ^ 40 * 7683284 * 2
def baseEnd_7683284 : Nat := 3945217696999422349715227

theorem tailTrace_7683284 : CollatzResearch.WordTrace tailWord_7683284 prefixEnd_7683284 3945217696999422349715227 := by
  unfold tailWord_7683284
  simp only [CollatzResearch.WordTrace]
  refine ⟨140116194748390871641348453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186821592997854495521797937 140116194748390871641348453)
  ·
    refine ⟨26271786515323288432752835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140116194748390871641348453 26271786515323288432752835)
    ·
      refine ⟨39407679772984932649129253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26271786515323288432752835 39407679772984932649129253)
      ·
        refine ⟨7388939957434674871711735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39407679772984932649129253 7388939957434674871711735)
        ·
          refine ⟨11083409936152012307567603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7388939957434674871711735 11083409936152012307567603)
          ·
            refine ⟨16625114904228018461351405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11083409936152012307567603 16625114904228018461351405)
            ·
              refine ⟨6234418089085506923006777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16625114904228018461351405 6234418089085506923006777)
              ·
                refine ⟨4675813566814130192255083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6234418089085506923006777 4675813566814130192255083)
                ·
                  refine ⟨7013720350221195288382625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675813566814130192255083 7013720350221195288382625)
                  ·
                    refine ⟨5260290262665896466286969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7013720350221195288382625 5260290262665896466286969)
                    ·
                      refine ⟨3945217696999422349715227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260290262665896466286969 3945217696999422349715227)
                      ·
                        rfl

theorem cell23_7683284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7683284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683284 prefixEnd_7683284 := by exact prefixLift 7683284
  have htrace : WordTrace (prefixWord ++ tailWord_7683284) baseStart_7683284 baseEnd_7683284 := by
    simpa [prefixWord, tailWord_7683284, baseEnd_7683284] using wordTrace_append hprefix tailTrace_7683284
  have hstable : (prefixWord ++ tailWord_7683284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683284).length < 2 ^ (prefixWord ++ tailWord_7683284).sum := by decide
  have hdescent : baseEnd_7683284 < baseStart_7683284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683309 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_7683309 : Nat := 118140960795 + 7683309 * 2 ^ 59
def prefixEnd_7683309 : Nat := 4983230072969 + 3 ^ 40 * 7683309 * 2
def baseEnd_7683309 : Nat := 3945230534015784751902611

theorem tailTrace_7683309 : CollatzResearch.WordTrace tailWord_7683309 prefixEnd_7683309 3945230534015784751902611 := by
  unfold tailWord_7683309
  simp only [CollatzResearch.WordTrace]
  refine ⟨280233301321691172552356981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186822200881127448368237987 280233301321691172552356981)
  ·
    refine ⟨26271871998908547426783467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280233301321691172552356981 26271871998908547426783467)
    ·
      refine ⟨39407807998362821140175201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26271871998908547426783467 39407807998362821140175201)
      ·
        refine ⟨29555855998772115855131401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39407807998362821140175201 29555855998772115855131401)
        ·
          refine ⟨22166891999079086891348551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29555855998772115855131401 22166891999079086891348551)
          ·
            refine ⟨33250337998618630337022827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22166891999079086891348551 33250337998618630337022827)
            ·
              refine ⟨49875506997927945505534241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33250337998618630337022827 49875506997927945505534241)
              ·
                refine ⟨37406630248445959129150681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49875506997927945505534241 37406630248445959129150681)
                ·
                  refine ⟨28054972686334469346863011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37406630248445959129150681 28054972686334469346863011)
                  ·
                    refine ⟨42082459029501704020294517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28054972686334469346863011 42082459029501704020294517)
                    ·
                      refine ⟨3945230534015784751902611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42082459029501704020294517 3945230534015784751902611)
                      ·
                        rfl

theorem cell23_7683309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_7683309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683309 prefixEnd_7683309 := by exact prefixLift 7683309
  have htrace : WordTrace (prefixWord ++ tailWord_7683309) baseStart_7683309 baseEnd_7683309 := by
    simpa [prefixWord, tailWord_7683309, baseEnd_7683309] using wordTrace_append hprefix tailTrace_7683309
  have hstable : (prefixWord ++ tailWord_7683309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683309).length < 2 ^ (prefixWord ++ tailWord_7683309).sum := by decide
  have hdescent : baseEnd_7683309 < baseStart_7683309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683379 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 4]
def baseStart_7683379 : Nat := 118140960795 + 7683379 * 2 ^ 59
def prefixEnd_7683379 : Nat := 4983230072969 + 3 ^ 40 * 7683379 * 2
def baseEnd_7683379 : Nat := 3945266477661599478027289

theorem tailTrace_7683379 : CollatzResearch.WordTrace tailWord_7683379 prefixEnd_7683379 3945266477661599478027289 := by
  unfold tailWord_7683379
  simp only [CollatzResearch.WordTrace]
  refine ⟨280235854431437574507405191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186823902954291716338270127 280235854431437574507405191)
  ·
    refine ⟨420353781647156361761107787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280235854431437574507405191 420353781647156361761107787)
    ·
      refine ⟨630530672470734542641661681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420353781647156361761107787 630530672470734542641661681)
      ·
        refine ⟨472898004353050906981246261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630530672470734542641661681 472898004353050906981246261)
        ·
          refine ⟨44334187908098522529491837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 472898004353050906981246261 44334187908098522529491837)
          ·
            refine ⟨16625320465536945948559439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44334187908098522529491837 16625320465536945948559439)
            ·
              refine ⟨24937980698305418922839159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16625320465536945948559439 24937980698305418922839159)
              ·
                refine ⟨37406971047458128384258739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24937980698305418922839159 37406971047458128384258739)
                ·
                  refine ⟨56110456571187192576388109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37406971047458128384258739 56110456571187192576388109)
                  ·
                    refine ⟨21041421214195197216145541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56110456571187192576388109 21041421214195197216145541)
                    ·
                      refine ⟨3945266477661599478027289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21041421214195197216145541 3945266477661599478027289)
                      ·
                        rfl

theorem cell23_7683379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_7683379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683379 prefixEnd_7683379 := by exact prefixLift 7683379
  have htrace : WordTrace (prefixWord ++ tailWord_7683379) baseStart_7683379 baseEnd_7683379 := by
    simpa [prefixWord, tailWord_7683379, baseEnd_7683379] using wordTrace_append hprefix tailTrace_7683379
  have hstable : (prefixWord ++ tailWord_7683379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683379).length < 2 ^ (prefixWord ++ tailWord_7683379).sum := by decide
  have hdescent : baseEnd_7683379 < baseStart_7683379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683392 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_7683392 : Nat := 118140960795 + 7683392 * 2 ^ 59
def prefixEnd_7683392 : Nat := 4983230072969 + 3 ^ 40 * 7683392 * 2
def baseEnd_7683392 : Nat := 3945273152910107927164729

theorem tailTrace_7683392 : CollatzResearch.WordTrace tailWord_7683392 prefixEnd_7683392 3945273152910107927164729 := by
  unfold tailWord_7683392
  simp only [CollatzResearch.WordTrace]
  refine ⟨140118164290195238863814215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186824219053593651818418953 140118164290195238863814215)
  ·
    refine ⟨210177246435292858295721323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140118164290195238863814215 210177246435292858295721323)
    ·
      refine ⟨315265869652939287443581985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210177246435292858295721323 315265869652939287443581985)
      ·
        refine ⟨236449402239704465582686489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315265869652939287443581985 236449402239704465582686489)
        ·
          refine ⟨177337051679778349187014867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236449402239704465582686489 177337051679778349187014867)
          ·
            refine ⟨266005577519667523780522301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177337051679778349187014867 266005577519667523780522301)
            ·
              refine ⟨99752091569875321417695863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266005577519667523780522301 99752091569875321417695863)
              ·
                refine ⟨149628137354812982126543795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99752091569875321417695863 149628137354812982126543795)
                ·
                  refine ⟨224442206032219473189815693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149628137354812982126543795 224442206032219473189815693)
                  ·
                    refine ⟨84165827262082302446180885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224442206032219473189815693 84165827262082302446180885)
                    ·
                      refine ⟨3945273152910107927164729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84165827262082302446180885 3945273152910107927164729)
                      ·
                        rfl

theorem cell23_7683392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_7683392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683392 prefixEnd_7683392 := by exact prefixLift 7683392
  have htrace : WordTrace (prefixWord ++ tailWord_7683392) baseStart_7683392 baseEnd_7683392 := by
    simpa [prefixWord, tailWord_7683392, baseEnd_7683392] using wordTrace_append hprefix tailTrace_7683392
  have hstable : (prefixWord ++ tailWord_7683392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683392).length < 2 ^ (prefixWord ++ tailWord_7683392).sum := by decide
  have hdescent : baseEnd_7683392 < baseStart_7683392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683406 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_7683406 : Nat := 118140960795 + 7683406 * 2 ^ 59
def prefixEnd_7683406 : Nat := 4983230072969 + 3 ^ 40 * 7683406 * 2
def baseEnd_7683406 : Nat := 1315093447213090290796555

theorem tailTrace_7683406 : CollatzResearch.WordTrace tailWord_7683406 prefixEnd_7683406 1315093447213090290796555 := by
  unfold tailWord_7683406
  simp only [CollatzResearch.WordTrace]
  refine ⟨35029604900292469764829759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186824559468226505412425381 35029604900292469764829759)
  ·
    refine ⟨52544407350438704647244639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35029604900292469764829759 52544407350438704647244639)
    ·
      refine ⟨78816611025658056970866959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52544407350438704647244639 78816611025658056970866959)
      ·
        refine ⟨118224916538487085456300439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78816611025658056970866959 118224916538487085456300439)
        ·
          refine ⟨177337374807730628184450659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118224916538487085456300439 177337374807730628184450659)
          ·
            refine ⟨266006062211595942276675989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177337374807730628184450659 266006062211595942276675989)
            ·
              refine ⟨12469034166168559794219187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 266006062211595942276675989 12469034166168559794219187)
              ·
                refine ⟨18703551249252839691328781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12469034166168559794219187 18703551249252839691328781)
                ·
                  refine ⟨7013831718469814884248293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18703551249252839691328781 7013831718469814884248293)
                  ·
                    refine ⟨1315093447213090290796555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7013831718469814884248293 1315093447213090290796555)
                    ·
                      rfl

theorem cell23_7683406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_7683406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683406 prefixEnd_7683406 := by exact prefixLift 7683406
  have htrace : WordTrace (prefixWord ++ tailWord_7683406) baseStart_7683406 baseEnd_7683406 := by
    simpa [prefixWord, tailWord_7683406, baseEnd_7683406] using wordTrace_append hprefix tailTrace_7683406
  have hstable : (prefixWord ++ tailWord_7683406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683406).length < 2 ^ (prefixWord ++ tailWord_7683406).sum := by decide
  have hdescent : baseEnd_7683406 < baseStart_7683406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683429 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 2, 5, 3]
def baseStart_7683429 : Nat := 118140960795 + 7683429 * 2 ^ 59
def prefixEnd_7683429 : Nat := 4983230072969 + 3 ^ 40 * 7683429 * 2
def baseEnd_7683429 : Nat := 3945292151694324282402059

theorem tailTrace_7683429 : CollatzResearch.WordTrace tailWord_7683429 prefixEnd_7683429 3945292151694324282402059 := by
  unfold tailWord_7683429
  simp only [CollatzResearch.WordTrace]
  refine ⟨280237678081256433046725341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186825118720837622031150227 280237678081256433046725341)
  ·
    refine ⟨105089129280471162392522003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280237678081256433046725341 105089129280471162392522003)
    ·
      refine ⟨157633693920706743588783005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105089129280471162392522003 157633693920706743588783005)
      ·
        refine ⟨59112635220265028845793627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157633693920706743588783005 59112635220265028845793627)
        ·
          refine ⟨88668952830397543268690441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59112635220265028845793627 88668952830397543268690441)
          ·
            refine ⟨66501714622798157451517831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88668952830397543268690441 66501714622798157451517831)
            ·
              refine ⟨99752571934197236177276747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66501714622798157451517831 99752571934197236177276747)
              ·
                refine ⟨149628857901295854265915121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99752571934197236177276747 149628857901295854265915121)
                ·
                  refine ⟨112221643425971890699436341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149628857901295854265915121 112221643425971890699436341)
                  ·
                    refine ⟨10520779071184864753072157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112221643425971890699436341 10520779071184864753072157)
                    ·
                      refine ⟨3945292151694324282402059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10520779071184864753072157 3945292151694324282402059)
                      ·
                        rfl

theorem cell23_7683429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_7683429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683429 prefixEnd_7683429 := by exact prefixLift 7683429
  have htrace : WordTrace (prefixWord ++ tailWord_7683429) baseStart_7683429 baseEnd_7683429 := by
    simpa [prefixWord, tailWord_7683429, baseEnd_7683429] using wordTrace_append hprefix tailTrace_7683429
  have hstable : (prefixWord ++ tailWord_7683429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683429).length < 2 ^ (prefixWord ++ tailWord_7683429).sum := by decide
  have hdescent : baseEnd_7683429 < baseStart_7683429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683457 : List Nat := [1, 2, 4, 3, 2, 1, 3, 2, 1, 4]
def baseStart_7683457 : Nat := 118140960795 + 7683457 * 2 ^ 59
def prefixEnd_7683457 : Nat := 4983230072969 + 3 ^ 40 * 7683457 * 2
def baseEnd_7683457 : Nat := 1315102176384216724283977

theorem tailTrace_7683457 : CollatzResearch.WordTrace tailWord_7683457 prefixEnd_7683457 1315102176384216724283977 := by
  unfold tailWord_7683457
  simp only [CollatzResearch.WordTrace]
  refine ⟨280238699325154993828744625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186825799550103329219163083 280238699325154993828744625)
  ·
    refine ⟨210179024493866245371558469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280238699325154993828744625 210179024493866245371558469)
    ·
      refine ⟨39408567092599921007167213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210179024493866245371558469 39408567092599921007167213)
      ·
        refine ⟨14778212659724970377687705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39408567092599921007167213 14778212659724970377687705)
        ·
          refine ⟨11083659494793727783265779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14778212659724970377687705 11083659494793727783265779)
          ·
            refine ⟨16625489242190591674898669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11083659494793727783265779 16625489242190591674898669)
            ·
              refine ⟨6234558465821471878087001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16625489242190591674898669 6234558465821471878087001)
              ·
                refine ⟨4675918849366103908565251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6234558465821471878087001 4675918849366103908565251)
                ·
                  refine ⟨7013878274049155862847877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675918849366103908565251 7013878274049155862847877)
                  ·
                    refine ⟨1315102176384216724283977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7013878274049155862847877 1315102176384216724283977)
                    ·
                      rfl

theorem cell23_7683457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_7683457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683457 prefixEnd_7683457 := by exact prefixLift 7683457
  have htrace : WordTrace (prefixWord ++ tailWord_7683457) baseStart_7683457 baseEnd_7683457 := by
    simpa [prefixWord, tailWord_7683457, baseEnd_7683457] using wordTrace_append hprefix tailTrace_7683457
  have hstable : (prefixWord ++ tailWord_7683457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683457).length < 2 ^ (prefixWord ++ tailWord_7683457).sum := by decide
  have hdescent : baseEnd_7683457 < baseStart_7683457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683463 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_7683463 : Nat := 118140960795 + 7683463 * 2 ^ 59
def prefixEnd_7683463 : Nat := 4983230072969 + 3 ^ 40 * 7683463 * 2
def baseEnd_7683463 : Nat := 3945309610036577149376903

theorem tailTrace_7683463 : CollatzResearch.WordTrace tailWord_7683463 prefixEnd_7683463 3945309610036577149376903 := by
  unfold tailWord_7683463
  simp only [CollatzResearch.WordTrace]
  refine ⟨280238918163133256853463043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186825945442088837902308695 280238918163133256853463043)
  ·
    refine ⟨420358377244699885280194565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280238918163133256853463043 420358377244699885280194565)
    ·
      refine ⟨78817195733381228490036481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420358377244699885280194565 78817195733381228490036481)
      ·
        refine ⟨59112896800035921367527361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78817195733381228490036481 59112896800035921367527361)
        ·
          refine ⟨44334672600026941025645521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59112896800035921367527361 44334672600026941025645521)
          ·
            refine ⟨33251004450020205769234141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44334672600026941025645521 33251004450020205769234141)
            ·
              refine ⟨12469126668757577163462803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33251004450020205769234141 12469126668757577163462803)
              ·
                refine ⟨18703690003136365745194205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12469126668757577163462803 18703690003136365745194205)
                ·
                  refine ⟨7013883751176137154447827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18703690003136365745194205 7013883751176137154447827)
                  ·
                    refine ⟨10520825626764205731671741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7013883751176137154447827 10520825626764205731671741)
                    ·
                      refine ⟨3945309610036577149376903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10520825626764205731671741 3945309610036577149376903)
                      ·
                        rfl

theorem cell23_7683463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_7683463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683463 prefixEnd_7683463 := by exact prefixLift 7683463
  have htrace : WordTrace (prefixWord ++ tailWord_7683463) baseStart_7683463 baseEnd_7683463 := by
    simpa [prefixWord, tailWord_7683463, baseEnd_7683463] using wordTrace_append hprefix tailTrace_7683463
  have hstable : (prefixWord ++ tailWord_7683463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683463).length < 2 ^ (prefixWord ++ tailWord_7683463).sum := by decide
  have hdescent : baseEnd_7683463 < baseStart_7683463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683470 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_7683470 : Nat := 118140960795 + 7683470 * 2 ^ 59
def prefixEnd_7683470 : Nat := 4983230072969 + 3 ^ 40 * 7683470 * 2
def baseEnd_7683470 : Nat := 438368133822350957998819

theorem tailTrace_7683470 : CollatzResearch.WordTrace tailWord_7683470 prefixEnd_7683470 438368133822350957998819 := by
  unfold tailWord_7683470
  simp only [CollatzResearch.WordTrace]
  refine ⟨35029896684263487131120983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186826115649405264699311909 35029896684263487131120983)
  ·
    refine ⟨52544845026395230696681475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35029896684263487131120983 52544845026395230696681475)
    ·
      refine ⟨78817267539592846045022213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52544845026395230696681475 78817267539592846045022213)
      ·
        refine ⟨14778237663673658633441665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78817267539592846045022213 14778237663673658633441665)
        ·
          refine ⟨11083678247755243975081249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14778237663673658633441665 11083678247755243975081249)
          ·
            refine ⟨8312758685816432981310937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11083678247755243975081249 8312758685816432981310937)
            ·
              refine ⟨6234569014362324735983203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8312758685816432981310937 6234569014362324735983203)
              ·
                refine ⟨9351853521543487103974805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234569014362324735983203 9351853521543487103974805)
                ·
                  refine ⟨438368133822350957998819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9351853521543487103974805 438368133822350957998819)
                  ·
                    rfl

theorem cell23_7683470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_7683470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683470 prefixEnd_7683470 := by exact prefixLift 7683470
  have htrace : WordTrace (prefixWord ++ tailWord_7683470) baseStart_7683470 baseEnd_7683470 := by
    simpa [prefixWord, tailWord_7683470, baseEnd_7683470] using wordTrace_append hprefix tailTrace_7683470
  have hstable : (prefixWord ++ tailWord_7683470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683470).length < 2 ^ (prefixWord ++ tailWord_7683470).sum := by decide
  have hdescent : baseEnd_7683470 < baseStart_7683470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683479 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 1, 6]
def baseStart_7683479 : Nat := 118140960795 + 7683479 * 2 ^ 59
def prefixEnd_7683479 : Nat := 4983230072969 + 3 ^ 40 * 7683479 * 2
def baseEnd_7683479 : Nat := 1315105941909016362258943

theorem tailTrace_7683479 : CollatzResearch.WordTrace tailWord_7683479 prefixEnd_7683479 1315105941909016362258943 := by
  unfold tailWord_7683479
  simp only [CollatzResearch.WordTrace]
  refine ⟨280239501731075291586045491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186826334487383527724030327 280239501731075291586045491)
  ·
    refine ⟨420359252596612937379068237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280239501731075291586045491 420359252596612937379068237)
    ·
      refine ⟨157634719723729851517150589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420359252596612937379068237 157634719723729851517150589)
      ·
        refine ⟨59113019896398694318931471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157634719723729851517150589 59113019896398694318931471)
        ·
          refine ⟨88669529844598041478397207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59113019896398694318931471 88669529844598041478397207)
          ·
            refine ⟨133004294766897062217595811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88669529844598041478397207 133004294766897062217595811)
            ·
              refine ⟨199506442150345593326393717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133004294766897062217595811 199506442150345593326393717)
              ·
                refine ⟨18703728951594899374349411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199506442150345593326393717 18703728951594899374349411)
                ·
                  refine ⟨28055593427392349061524117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18703728951594899374349411 28055593427392349061524117)
                  ·
                    refine ⟨1315105941909016362258943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28055593427392349061524117 1315105941909016362258943)
                    ·
                      rfl

theorem cell23_7683479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_7683479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683479 prefixEnd_7683479 := by exact prefixLift 7683479
  have htrace : WordTrace (prefixWord ++ tailWord_7683479) baseStart_7683479 baseEnd_7683479 := by
    simpa [prefixWord, tailWord_7683479, baseEnd_7683479] using wordTrace_append hprefix tailTrace_7683479
  have hstable : (prefixWord ++ tailWord_7683479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683479).length < 2 ^ (prefixWord ++ tailWord_7683479).sum := by decide
  have hdescent : baseEnd_7683479 < baseStart_7683479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683490 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_7683490 : Nat := 118140960795 + 7683490 * 2 ^ 59
def prefixEnd_7683490 : Nat := 4983230072969 + 3 ^ 40 * 7683490 * 2
def baseEnd_7683490 : Nat := 3945323474014248543739279

theorem tailTrace_7683490 : CollatzResearch.WordTrace tailWord_7683490 prefixEnd_7683490 3945323474014248543739279 := by
  unfold tailWord_7683490
  simp only [CollatzResearch.WordTrace]
  refine ⟨70059975733508860116173981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186826601956023626976463949 70059975733508860116173981)
  ·
    refine ⟨26272490900065822543565243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70059975733508860116173981 26272490900065822543565243)
    ·
      refine ⟨39408736350098733815347865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26272490900065822543565243 39408736350098733815347865)
      ·
        refine ⟨29556552262574050361510899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39408736350098733815347865 29556552262574050361510899)
        ·
          refine ⟨44334828393861075542266349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29556552262574050361510899 44334828393861075542266349)
          ·
            refine ⟨16625560647697903328349881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44334828393861075542266349 16625560647697903328349881)
            ·
              refine ⟨12469170485773427496262411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16625560647697903328349881 12469170485773427496262411)
              ·
                refine ⟨18703755728660141244393617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12469170485773427496262411 18703755728660141244393617)
                ·
                  refine ⟨14027816796495105933295213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18703755728660141244393617 14027816796495105933295213)
                  ·
                    refine ⟨5260431298685664724985705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14027816796495105933295213 5260431298685664724985705)
                    ·
                      refine ⟨3945323474014248543739279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260431298685664724985705 3945323474014248543739279)
                      ·
                        rfl

theorem cell23_7683490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_7683490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683490 prefixEnd_7683490 := by exact prefixLift 7683490
  have htrace : WordTrace (prefixWord ++ tailWord_7683490) baseStart_7683490 baseEnd_7683490 := by
    simpa [prefixWord, tailWord_7683490, baseEnd_7683490] using wordTrace_append hprefix tailTrace_7683490
  have hstable : (prefixWord ++ tailWord_7683490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683490).length < 2 ^ (prefixWord ++ tailWord_7683490).sum := by decide
  have hdescent : baseEnd_7683490 < baseStart_7683490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683509 : List Nat := [1, 3, 3, 2, 2, 12]
def baseStart_7683509 : Nat := 118140960795 + 7683509 * 2 ^ 59
def prefixEnd_7683509 : Nat := 4983230072969 + 3 ^ 40 * 7683509 * 2
def baseEnd_7683509 : Nat := 16235939218710633618937

theorem tailTrace_7683509 : CollatzResearch.WordTrace tailWord_7683509 prefixEnd_7683509 16235939218710633618937 := by
  unfold tailWord_7683509
  simp only [CollatzResearch.WordTrace]
  refine ⟨280240595920966606709637581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186827063947311071139758387 280240595920966606709637581)
  ·
    refine ⟨105090223470362477516114093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280240595920966606709637581 105090223470362477516114093)
    ·
      refine ⟨39408833801385929068542785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105090223470362477516114093 39408833801385929068542785)
      ·
        refine ⟨29556625351039446801407089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39408833801385929068542785 29556625351039446801407089)
        ·
          refine ⟨22167469013279585101055317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29556625351039446801407089 22167469013279585101055317)
          ·
            refine ⟨16235939218710633618937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22167469013279585101055317 16235939218710633618937)
            ·
              rfl

theorem cell23_7683509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 12].length) (baseStart_7683509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683509 prefixEnd_7683509 := by exact prefixLift 7683509
  have htrace : WordTrace (prefixWord ++ tailWord_7683509) baseStart_7683509 baseEnd_7683509 := by
    simpa [prefixWord, tailWord_7683509, baseEnd_7683509] using wordTrace_append hprefix tailTrace_7683509
  have hstable : (prefixWord ++ tailWord_7683509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683509).length < 2 ^ (prefixWord ++ tailWord_7683509).sum := by decide
  have hdescent : baseEnd_7683509 < baseStart_7683509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683557 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 1, 2, 3]
def baseStart_7683557 : Nat := 118140960795 + 7683557 * 2 ^ 59
def prefixEnd_7683557 : Nat := 4983230072969 + 3 ^ 40 * 7683557 * 2
def baseEnd_7683557 : Nat := 3945357877218099781601471

theorem tailTrace_7683557 : CollatzResearch.WordTrace tailWord_7683557 prefixEnd_7683557 3945357877218099781601471 := by
  unfold tailWord_7683557
  simp only [CollatzResearch.WordTrace]
  refine ⟨280242346624792710907384925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186828231083195140604923283 280242346624792710907384925)
  ·
    refine ⟨105090879984297266590269347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280242346624792710907384925 105090879984297266590269347)
    ·
      refine ⟨157636319976445899885404021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105090879984297266590269347 157636319976445899885404021)
      ·
        refine ⟨14778404997791803114256627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157636319976445899885404021 14778404997791803114256627)
        ·
          refine ⟨22167607496687704671384941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14778404997791803114256627 22167607496687704671384941)
          ·
            refine ⟨8312852811257889251769353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22167607496687704671384941 8312852811257889251769353)
            ·
              refine ⟨6234639608443416938827015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8312852811257889251769353 6234639608443416938827015)
              ·
                refine ⟨9351959412665125408240523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234639608443416938827015 9351959412665125408240523)
                ·
                  refine ⟨14027939118997688112360785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9351959412665125408240523 14027939118997688112360785)
                  ·
                    refine ⟨10520954339248266084270589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14027939118997688112360785 10520954339248266084270589)
                    ·
                      refine ⟨3945357877218099781601471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10520954339248266084270589 3945357877218099781601471)
                      ·
                        rfl

theorem cell23_7683557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_7683557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683557 prefixEnd_7683557 := by exact prefixLift 7683557
  have htrace : WordTrace (prefixWord ++ tailWord_7683557) baseStart_7683557 baseEnd_7683557 := by
    simpa [prefixWord, tailWord_7683557, baseEnd_7683557] using wordTrace_append hprefix tailTrace_7683557
  have hstable : (prefixWord ++ tailWord_7683557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683557).length < 2 ^ (prefixWord ++ tailWord_7683557).sum := by decide
  have hdescent : baseEnd_7683557 < baseStart_7683557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683570 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_7683570 : Nat := 118140960795 + 7683570 * 2 ^ 59
def prefixEnd_7683570 : Nat := 4983230072969 + 3 ^ 40 * 7683570 * 2
def baseEnd_7683570 : Nat := 3945364552466608230738911

theorem tailTrace_7683570 : CollatzResearch.WordTrace tailWord_7683570 prefixEnd_7683570 3945364552466608230738911 := by
  unfold tailWord_7683570
  simp only [CollatzResearch.WordTrace]
  refine ⟨70060705193436403531902041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186828547182497076085072109 70060705193436403531902041)
  ·
    refine ⟨52545528895077302648926531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70060705193436403531902041 52545528895077302648926531)
    ·
      refine ⟨78818293342615953973389797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52545528895077302648926531 78818293342615953973389797)
      ·
        refine ⟨14778430001740491370010587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78818293342615953973389797 14778430001740491370010587)
        ·
          refine ⟨22167645002610737055015881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14778430001740491370010587 22167645002610737055015881)
          ·
            refine ⟨16625733751958052791261911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22167645002610737055015881 16625733751958052791261911)
            ·
              refine ⟨24938600627937079186892867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16625733751958052791261911 24938600627937079186892867)
              ·
                refine ⟨37407900941905618780339301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24938600627937079186892867 37407900941905618780339301)
                ·
                  refine ⟨7013981426607303521313619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37407900941905618780339301 7013981426607303521313619)
                  ·
                    refine ⟨10520972139910955281970429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7013981426607303521313619 10520972139910955281970429)
                    ·
                      refine ⟨3945364552466608230738911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10520972139910955281970429 3945364552466608230738911)
                      ·
                        rfl

theorem cell23_7683570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_7683570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683570 prefixEnd_7683570 := by exact prefixLift 7683570
  have htrace : WordTrace (prefixWord ++ tailWord_7683570) baseStart_7683570 baseEnd_7683570 := by
    simpa [prefixWord, tailWord_7683570, baseEnd_7683570] using wordTrace_append hprefix tailTrace_7683570
  have hstable : (prefixWord ++ tailWord_7683570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683570).length < 2 ^ (prefixWord ++ tailWord_7683570).sum := by decide
  have hdescent : baseEnd_7683570 < baseStart_7683570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683579 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 5]
def baseStart_7683579 : Nat := 118140960795 + 7683579 * 2 ^ 59
def prefixEnd_7683579 : Nat := 4983230072969 + 3 ^ 40 * 7683579 * 2
def baseEnd_7683579 : Nat := 3945369173792498695526369

theorem tailTrace_7683579 : CollatzResearch.WordTrace tailWord_7683579 prefixEnd_7683579 3945369173792498695526369 := by
  unfold tailWord_7683579
  simp only [CollatzResearch.WordTrace]
  refine ⟨280243149030713008664685791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186828766020475339109790527 280243149030713008664685791)
  ·
    refine ⟨420364723546069512997028687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280243149030713008664685791 420364723546069512997028687)
    ·
      refine ⟨630547085319104269495543031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420364723546069512997028687 630547085319104269495543031)
      ·
        refine ⟨945820627978656404243314547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630547085319104269495543031 945820627978656404243314547)
        ·
          refine ⟨1418730941967984606364971821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945820627978656404243314547 1418730941967984606364971821)
          ·
            refine ⟨532024103237994227386864433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1418730941967984606364971821 532024103237994227386864433)
            ·
              refine ⟨399018077428495670540148325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532024103237994227386864433 399018077428495670540148325)
              ·
                refine ⟨74815889517842938226277811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399018077428495670540148325 74815889517842938226277811)
                ·
                  refine ⟨112223834276764407339416717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74815889517842938226277811 112223834276764407339416717)
                  ·
                    refine ⟨42083937853786652752281269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112223834276764407339416717 42083937853786652752281269)
                    ·
                      refine ⟨3945369173792498695526369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42083937853786652752281269 3945369173792498695526369)
                      ·
                        rfl

theorem cell23_7683579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_7683579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683579 prefixEnd_7683579 := by exact prefixLift 7683579
  have htrace : WordTrace (prefixWord ++ tailWord_7683579) baseStart_7683579 baseEnd_7683579 := by
    simpa [prefixWord, tailWord_7683579, baseEnd_7683579] using wordTrace_append hprefix tailTrace_7683579
  have hstable : (prefixWord ++ tailWord_7683579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683579).length < 2 ^ (prefixWord ++ tailWord_7683579).sum := by decide
  have hdescent : baseEnd_7683579 < baseStart_7683579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683609 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_7683609 : Nat := 118140960795 + 7683609 * 2 ^ 59
def prefixEnd_7683609 : Nat := 4983230072969 + 3 ^ 40 * 7683609 * 2
def baseEnd_7683609 : Nat := 3945384578212133578151231

theorem tailTrace_7683609 : CollatzResearch.WordTrace tailWord_7683609 prefixEnd_7683609 3945384578212133578151231 := by
  unfold tailWord_7683609
  simp only [CollatzResearch.WordTrace]
  refine ⟨280244243220604323788277881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186829495480402882525518587 280244243220604323788277881)
  ·
    refine ⟨210183182415453242841208411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280244243220604323788277881 210183182415453242841208411)
    ·
      refine ⟨315274773623179864261812617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210183182415453242841208411 315274773623179864261812617)
      ·
        refine ⟨236456080217384898196359463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315274773623179864261812617 236456080217384898196359463)
        ·
          refine ⟨354684120326077347294539195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236456080217384898196359463 354684120326077347294539195)
          ·
            refine ⟨532026180489116020941808793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354684120326077347294539195 532026180489116020941808793)
            ·
              refine ⟨399019635366837015706356595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532026180489116020941808793 399019635366837015706356595)
              ·
                refine ⟨598529453050255523559534893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399019635366837015706356595 598529453050255523559534893)
                ·
                  refine ⟨224448544893845821334825585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598529453050255523559534893 224448544893845821334825585)
                  ·
                    refine ⟨168336408670384366001119189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 224448544893845821334825585 168336408670384366001119189)
                    ·
                      refine ⟨3945384578212133578151231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168336408670384366001119189 3945384578212133578151231)
                      ·
                        rfl

theorem cell23_7683609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_7683609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683609 prefixEnd_7683609 := by exact prefixLift 7683609
  have htrace : WordTrace (prefixWord ++ tailWord_7683609) baseStart_7683609 baseEnd_7683609 := by
    simpa [prefixWord, tailWord_7683609, baseEnd_7683609] using wordTrace_append hprefix tailTrace_7683609
  have hstable : (prefixWord ++ tailWord_7683609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683609).length < 2 ^ (prefixWord ++ tailWord_7683609).sum := by decide
  have hdescent : baseEnd_7683609 < baseStart_7683609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683626 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_7683626 : Nat := 118140960795 + 7683626 * 2 ^ 59
def prefixEnd_7683626 : Nat := 4983230072969 + 3 ^ 40 * 7683626 * 2
def baseEnd_7683626 : Nat := 3945393307383260011638653

theorem tailTrace_7683626 : CollatzResearch.WordTrace tailWord_7683626 prefixEnd_7683626 3945393307383260011638653 := by
  unfold tailWord_7683626
  simp only [CollatzResearch.WordTrace]
  refine ⟨70061215815385683922911683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186829908841028490461097821 70061215815385683922911683)
  ·
    refine ⟨105091823723078525884367525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70061215815385683922911683 105091823723078525884367525)
    ·
      refine ⟨19704716948077223603318911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105091823723078525884367525 19704716948077223603318911)
      ·
        refine ⟨29557075422115835404978367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19704716948077223603318911 29557075422115835404978367)
        ·
          refine ⟨44335613133173753107467551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29557075422115835404978367 44335613133173753107467551)
          ·
            refine ⟨66503419699760629661201327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44335613133173753107467551 66503419699760629661201327)
            ·
              refine ⟨99755129549640944491801991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66503419699760629661201327 99755129549640944491801991)
              ·
                refine ⟨149632694324461416737702987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99755129549640944491801991 149632694324461416737702987)
                ·
                  refine ⟨224449041486692125106554481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149632694324461416737702987 224449041486692125106554481)
                  ·
                    refine ⟨168336781115019093829915861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 224449041486692125106554481 168336781115019093829915861)
                    ·
                      refine ⟨3945393307383260011638653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168336781115019093829915861 3945393307383260011638653)
                      ·
                        rfl

theorem cell23_7683626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_7683626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683626 prefixEnd_7683626 := by exact prefixLift 7683626
  have htrace : WordTrace (prefixWord ++ tailWord_7683626) baseStart_7683626 baseEnd_7683626 := by
    simpa [prefixWord, tailWord_7683626, baseEnd_7683626] using wordTrace_append hprefix tailTrace_7683626
  have hstable : (prefixWord ++ tailWord_7683626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683626).length < 2 ^ (prefixWord ++ tailWord_7683626).sum := by decide
  have hdescent : baseEnd_7683626 < baseStart_7683626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683683 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 4]
def baseStart_7683683 : Nat := 118140960795 + 7683683 * 2 ^ 59
def prefixEnd_7683683 : Nat := 4983230072969 + 3 ^ 40 * 7683683 * 2
def baseEnd_7683683 : Nat := 3945422575780566288625891

theorem tailTrace_7683683 : CollatzResearch.WordTrace tailWord_7683683 prefixEnd_7683683 3945422575780566288625891 := by
  unfold tailWord_7683683
  simp only [CollatzResearch.WordTrace]
  refine ⟨280246942222336234426471703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186831294814890822950981135 280246942222336234426471703)
  ·
    refine ⟨420370413333504351639707555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280246942222336234426471703 420370413333504351639707555)
    ·
      refine ⟨630555620000256527459561333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420370413333504351639707555 630555620000256527459561333)
      ·
        refine ⟨59114589375024049449333875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 630555620000256527459561333 59114589375024049449333875)
        ·
          refine ⟨88671884062536074174000813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59114589375024049449333875 88671884062536074174000813)
          ·
            refine ⟨33251956523451027815250305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88671884062536074174000813 33251956523451027815250305)
            ·
              refine ⟨24938967392588270861437729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33251956523451027815250305 24938967392588270861437729)
              ·
                refine ⟨18704225544441203146078297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24938967392588270861437729 18704225544441203146078297)
                ·
                  refine ⟨14028169158330902359558723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18704225544441203146078297 14028169158330902359558723)
                  ·
                    refine ⟨21042253737496353539338085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14028169158330902359558723 21042253737496353539338085)
                    ·
                      refine ⟨3945422575780566288625891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21042253737496353539338085 3945422575780566288625891)
                      ·
                        rfl

theorem cell23_7683683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_7683683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683683 prefixEnd_7683683 := by exact prefixLift 7683683
  have htrace : WordTrace (prefixWord ++ tailWord_7683683) baseStart_7683683 baseEnd_7683683 := by
    simpa [prefixWord, tailWord_7683683, baseEnd_7683683] using wordTrace_append hprefix tailTrace_7683683
  have hstable : (prefixWord ++ tailWord_7683683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683683).length < 2 ^ (prefixWord ++ tailWord_7683683).sum := by decide
  have hdescent : baseEnd_7683683 < baseStart_7683683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683770 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 1, 5]
def baseStart_7683770 : Nat := 118140960795 + 7683770 * 2 ^ 59
def prefixEnd_7683770 : Nat := 4983230072969 + 3 ^ 40 * 7683770 * 2
def baseEnd_7683770 : Nat := 1315155749532502482745997

theorem tailTrace_7683770 : CollatzResearch.WordTrace tailWord_7683770 prefixEnd_7683770 1315155749532502482745997 := by
  unfold tailWord_7683770
  simp only [CollatzResearch.WordTrace]
  refine ⟨70062528843255262071222191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186833410248680698856592509 70062528843255262071222191)
  ·
    refine ⟨105093793264882893106833287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70062528843255262071222191 105093793264882893106833287)
    ·
      refine ⟨157640689897324339660249931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105093793264882893106833287 157640689897324339660249931)
      ·
        refine ⟨236461034845986509490374897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157640689897324339660249931 236461034845986509490374897)
        ·
          refine ⟨177345776134489882117781173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236461034845986509490374897 177345776134489882117781173)
          ·
            refine ⟨16626166512608426448541985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177345776134489882117781173 16626166512608426448541985)
            ·
              refine ⟨12469624884456319836406489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16626166512608426448541985 12469624884456319836406489)
              ·
                refine ⟨9352218663342239877304867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12469624884456319836406489 9352218663342239877304867)
                ·
                  refine ⟨14028327995013359815957301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9352218663342239877304867 14028327995013359815957301)
                  ·
                    refine ⟨1315155749532502482745997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14028327995013359815957301 1315155749532502482745997)
                    ·
                      rfl

theorem cell23_7683770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_7683770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683770 prefixEnd_7683770 := by exact prefixLift 7683770
  have htrace : WordTrace (prefixWord ++ tailWord_7683770) baseStart_7683770 baseEnd_7683770 := by
    simpa [prefixWord, tailWord_7683770, baseEnd_7683770] using wordTrace_append hprefix tailTrace_7683770
  have hstable : (prefixWord ++ tailWord_7683770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683770).length < 2 ^ (prefixWord ++ tailWord_7683770).sum := by decide
  have hdescent : baseEnd_7683770 < baseStart_7683770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683783 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 6, 4]
def baseStart_7683783 : Nat := 118140960795 + 7683783 * 2 ^ 59
def prefixEnd_7683783 : Nat := 4983230072969 + 3 ^ 40 * 7683783 * 2
def baseEnd_7683783 : Nat := 1315157974615338632458477

theorem tailTrace_7683783 : CollatzResearch.WordTrace tailWord_7683783 prefixEnd_7683783 1315157974615338632458477 := by
  unfold tailWord_7683783
  simp only [CollatzResearch.WordTrace]
  refine ⟨280250589521973951505112003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186833726347982634336741335 280250589521973951505112003)
  ·
    refine ⟨420375884282960927257668005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280250589521973951505112003 420375884282960927257668005)
    ·
      refine ⟨78820478303055173860812751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420375884282960927257668005 78820478303055173860812751)
      ·
        refine ⟨118230717454582760791219127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78820478303055173860812751 118230717454582760791219127)
        ·
          refine ⟨177346076181874141186828691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118230717454582760791219127 177346076181874141186828691)
          ·
            refine ⟨266019114272811211780243037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177346076181874141186828691 266019114272811211780243037)
            ·
              refine ⟨99757167852304204417591139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266019114272811211780243037 99757167852304204417591139)
              ·
                refine ⟨149635751778456306626386709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99757167852304204417591139 149635751778456306626386709)
                ·
                  refine ⟨7014175864615139373111877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149635751778456306626386709 7014175864615139373111877)
                  ·
                    refine ⟨1315157974615338632458477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7014175864615139373111877 1315157974615338632458477)
                    ·
                      rfl

theorem cell23_7683783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_7683783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683783 prefixEnd_7683783 := by exact prefixLift 7683783
  have htrace : WordTrace (prefixWord ++ tailWord_7683783) baseStart_7683783 baseEnd_7683783 := by
    simpa [prefixWord, tailWord_7683783, baseEnd_7683783] using wordTrace_append hprefix tailTrace_7683783
  have hstable : (prefixWord ++ tailWord_7683783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683783).length < 2 ^ (prefixWord ++ tailWord_7683783).sum := by decide
  have hdescent : baseEnd_7683783 < baseStart_7683783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683790 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_7683790 : Nat := 118140960795 + 7683790 * 2 ^ 59
def prefixEnd_7683790 : Nat := 4983230072969 + 3 ^ 40 * 7683790 * 2
def baseEnd_7683790 : Nat := 3945477518210597369987899

theorem tailTrace_7683790 : CollatzResearch.WordTrace tailWord_7683790 prefixEnd_7683790 3945477518210597369987899 := by
  unfold tailWord_7683790
  simp only [CollatzResearch.WordTrace]
  refine ⟨35031355604118573962577103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186833896555299061133744549 35031355604118573962577103)
  ·
    refine ⟨52547033406177860943865655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35031355604118573962577103 52547033406177860943865655)
    ·
      refine ⟨78820550109266791415798483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52547033406177860943865655 78820550109266791415798483)
      ·
        refine ⟨118230825163900187123697725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78820550109266791415798483 118230825163900187123697725)
        ·
          refine ⟨44336559436462570171386647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118230825163900187123697725 44336559436462570171386647)
          ·
            refine ⟨66504839154693855257079971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44336559436462570171386647 66504839154693855257079971)
            ·
              refine ⟨99757258732040782885619957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66504839154693855257079971 99757258732040782885619957)
              ·
                refine ⟨9352243006128823395526871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99757258732040782885619957 9352243006128823395526871)
                ·
                  refine ⟨14028364509193235093290307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9352243006128823395526871 14028364509193235093290307)
                  ·
                    refine ⟨21042546763789852639935461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14028364509193235093290307 21042546763789852639935461)
                    ·
                      refine ⟨3945477518210597369987899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21042546763789852639935461 3945477518210597369987899)
                      ·
                        rfl

theorem cell23_7683790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_7683790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683790 prefixEnd_7683790 := by exact prefixLift 7683790
  have htrace : WordTrace (prefixWord ++ tailWord_7683790) baseStart_7683790 baseEnd_7683790 := by
    simpa [prefixWord, tailWord_7683790, baseEnd_7683790] using wordTrace_append hprefix tailTrace_7683790
  have hstable : (prefixWord ++ tailWord_7683790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683790).length < 2 ^ (prefixWord ++ tailWord_7683790).sum := by decide
  have hdescent : baseEnd_7683790 < baseStart_7683790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683793 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_7683793 : Nat := 118140960795 + 7683793 * 2 ^ 59
def prefixEnd_7683793 : Nat := 4983230072969 + 3 ^ 40 * 7683793 * 2
def baseEnd_7683793 : Nat := 3945479058652560858250385

theorem tailTrace_7683793 : CollatzResearch.WordTrace tailWord_7683793 prefixEnd_7683793 3945479058652560858250385 := by
  unfold tailWord_7683793
  simp only [CollatzResearch.WordTrace]
  refine ⟨280250954251937723212976033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186833969501291815475317355 280250954251937723212976033)
  ·
    refine ⟨210188215688953292409732025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280250954251937723212976033 210188215688953292409732025)
    ·
      refine ⟨157641161766714969307299019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210188215688953292409732025 157641161766714969307299019)
      ·
        refine ⟨236461742650072453960948529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157641161766714969307299019 236461742650072453960948529)
        ·
          refine ⟨177346306987554340470711397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236461742650072453960948529 177346306987554340470711397)
          ·
            refine ⟨33252432560166438838258387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177346306987554340470711397 33252432560166438838258387)
            ·
              refine ⟨49878648840249658257387581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33252432560166438838258387 49878648840249658257387581)
              ·
                refine ⟨18704493315093621846520343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49878648840249658257387581 18704493315093621846520343)
                ·
                  refine ⟨28056739972640432769780515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18704493315093621846520343 28056739972640432769780515)
                  ·
                    refine ⟨42085109958960649154670773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28056739972640432769780515 42085109958960649154670773)
                    ·
                      refine ⟨3945479058652560858250385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42085109958960649154670773 3945479058652560858250385)
                      ·
                        rfl

theorem cell23_7683793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_7683793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683793 prefixEnd_7683793 := by exact prefixLift 7683793
  have htrace : WordTrace (prefixWord ++ tailWord_7683793) baseStart_7683793 baseEnd_7683793 := by
    simpa [prefixWord, tailWord_7683793, baseEnd_7683793] using wordTrace_append hprefix tailTrace_7683793
  have hstable : (prefixWord ++ tailWord_7683793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683793).length < 2 ^ (prefixWord ++ tailWord_7683793).sum := by decide
  have hdescent : baseEnd_7683793 < baseStart_7683793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683800 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 2, 4]
def baseStart_7683800 : Nat := 118140960795 + 7683800 * 2 ^ 59
def prefixEnd_7683800 : Nat := 4983230072969 + 3 ^ 40 * 7683800 * 2
def baseEnd_7683800 : Nat := 1315160884339047443620951

theorem tailTrace_7683800 : CollatzResearch.WordTrace tailWord_7683800 prefixEnd_7683800 1315160884339047443620951 := by
  unfold tailWord_7683800
  simp only [CollatzResearch.WordTrace]
  refine ⟨140125604781456181704240427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186834139708608242272320569 140125604781456181704240427)
  ·
    refine ⟨210188407172184272556360641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140125604781456181704240427 210188407172184272556360641)
    ·
      refine ⟨157641305379138204417270481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210188407172184272556360641 157641305379138204417270481)
      ·
        refine ⟨118230979034353653312952861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157641305379138204417270481 118230979034353653312952861)
        ·
          refine ⟨44336617137882619992357323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118230979034353653312952861 44336617137882619992357323)
          ·
            refine ⟨66504925706823929988535985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44336617137882619992357323 66504925706823929988535985)
            ·
              refine ⟨49878694280117947491401989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66504925706823929988535985 49878694280117947491401989)
              ·
                refine ⟨9352255177522115154637873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49878694280117947491401989 9352255177522115154637873)
                ·
                  refine ⟨7014191383141586365978405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9352255177522115154637873 7014191383141586365978405)
                  ·
                    refine ⟨1315160884339047443620951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7014191383141586365978405 1315160884339047443620951)
                    ·
                      rfl

theorem cell23_7683800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_7683800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683800 prefixEnd_7683800 := by exact prefixLift 7683800
  have htrace : WordTrace (prefixWord ++ tailWord_7683800) baseStart_7683800 baseEnd_7683800 := by
    simpa [prefixWord, tailWord_7683800, baseEnd_7683800] using wordTrace_append hprefix tailTrace_7683800
  have hstable : (prefixWord ++ tailWord_7683800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683800).length < 2 ^ (prefixWord ++ tailWord_7683800).sum := by decide
  have hdescent : baseEnd_7683800 < baseStart_7683800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683813 : List Nat := [1, 3, 1, 4, 1, 1, 4, 8]
def baseStart_7683813 : Nat := 118140960795 + 7683813 * 2 ^ 59
def prefixEnd_7683813 : Nat := 4983230072969 + 3 ^ 40 * 7683813 * 2
def baseEnd_7683813 : Nat := 146129234380209288148159

theorem tailTrace_7683813 : CollatzResearch.WordTrace tailWord_7683813 prefixEnd_7683813 146129234380209288148159 := by
  unfold tailWord_7683813
  simp only [CollatzResearch.WordTrace]
  refine ⟨280251683711865266628704093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186834455807910177752469395 280251683711865266628704093)
  ·
    refine ⟨105094381391949474985764035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280251683711865266628704093 105094381391949474985764035)
    ·
      refine ⟨157641572087924212478646053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105094381391949474985764035 157641572087924212478646053)
      ·
        refine ⟨29557794766485789839746135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157641572087924212478646053 29557794766485789839746135)
        ·
          refine ⟨44336692149728684759619203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29557794766485789839746135 44336692149728684759619203)
          ·
            refine ⟨66505038224593027139428805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44336692149728684759619203 66505038224593027139428805)
            ·
              refine ⟨12469694667111192588642901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66505038224593027139428805 12469694667111192588642901)
              ·
                refine ⟨146129234380209288148159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12469694667111192588642901 146129234380209288148159)
                ·
                  rfl

theorem cell23_7683813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 8].length) (baseStart_7683813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683813 prefixEnd_7683813 := by exact prefixLift 7683813
  have htrace : WordTrace (prefixWord ++ tailWord_7683813) baseStart_7683813 baseEnd_7683813 := by
    simpa [prefixWord, tailWord_7683813, baseEnd_7683813] using wordTrace_append hprefix tailTrace_7683813
  have hstable : (prefixWord ++ tailWord_7683813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683813).length < 2 ^ (prefixWord ++ tailWord_7683813).sum := by decide
  have hdescent : baseEnd_7683813 < baseStart_7683813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683844 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_7683844 : Nat := 118140960795 + 7683844 * 2 ^ 59
def prefixEnd_7683844 : Nat := 4983230072969 + 3 ^ 40 * 7683844 * 2
def baseEnd_7683844 : Nat := 3945505246165940158712651

theorem tailTrace_7683844 : CollatzResearch.WordTrace tailWord_7683844 prefixEnd_7683844 3945505246165940158712651 := by
  unfold tailWord_7683844
  simp only [CollatzResearch.WordTrace]
  refine ⟨140126407187376479461541293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186835209583168639282055057 140126407187376479461541293)
  ·
    refine ⟨52547402695266179798077985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140126407187376479461541293 52547402695266179798077985)
    ·
      refine ⟨39410552021449634848558489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52547402695266179798077985 39410552021449634848558489)
      ·
        refine ⟨29557914016087226136418867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39410552021449634848558489 29557914016087226136418867)
        ·
          refine ⟨44336871024130839204628301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29557914016087226136418867 44336871024130839204628301)
          ·
            refine ⟨16626326634049064701735613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44336871024130839204628301 16626326634049064701735613)
            ·
              refine ⟨6234872487768399263150855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16626326634049064701735613 6234872487768399263150855)
              ·
                refine ⟨9352308731652598894726283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234872487768399263150855 9352308731652598894726283)
                ·
                  refine ⟨14028463097478898342089425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9352308731652598894726283 14028463097478898342089425)
                  ·
                    refine ⟨10521347323109173756567069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14028463097478898342089425 10521347323109173756567069)
                    ·
                      refine ⟨3945505246165940158712651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10521347323109173756567069 3945505246165940158712651)
                      ·
                        rfl

theorem cell23_7683844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_7683844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683844 prefixEnd_7683844 := by exact prefixLift 7683844
  have htrace : WordTrace (prefixWord ++ tailWord_7683844) baseStart_7683844 baseEnd_7683844 := by
    simpa [prefixWord, tailWord_7683844, baseEnd_7683844] using wordTrace_append hprefix tailTrace_7683844
  have hstable : (prefixWord ++ tailWord_7683844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683844).length < 2 ^ (prefixWord ++ tailWord_7683844).sum := by decide
  have hdescent : baseEnd_7683844 < baseStart_7683844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683858 : List Nat := [3, 2, 4, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_7683858 : Nat := 118140960795 + 7683858 * 2 ^ 59
def prefixEnd_7683858 : Nat := 4983230072969 + 3 ^ 40 * 7683858 * 2
def baseEnd_7683858 : Nat := 3945512434895103103937587

theorem tailTrace_7683858 : CollatzResearch.WordTrace tailWord_7683858 prefixEnd_7683858 3945512434895103103937587 := by
  unfold tailWord_7683858
  simp only [CollatzResearch.WordTrace]
  refine ⟨70063331249175559828523057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186835549997801492876061485 70063331249175559828523057)
  ·
    refine ⟨52547498436881669871392293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70063331249175559828523057 52547498436881669871392293)
    ·
      refine ⟨9852655956915313100886055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52547498436881669871392293 9852655956915313100886055)
      ·
        refine ⟨14778983935372969651329083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9852655956915313100886055 14778983935372969651329083)
        ·
          refine ⟨22168475903059454476993625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14778983935372969651329083 22168475903059454476993625)
          ·
            refine ⟨16626356927294590857745219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22168475903059454476993625 16626356927294590857745219)
            ·
              refine ⟨24939535390941886286617829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16626356927294590857745219 24939535390941886286617829)
              ·
                refine ⟨4676162885801603678740843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24939535390941886286617829 4676162885801603678740843)
                ·
                  refine ⟨7014244328702405518111265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676162885801603678740843 7014244328702405518111265)
                  ·
                    refine ⟨5260683246526804138583449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7014244328702405518111265 5260683246526804138583449)
                    ·
                      refine ⟨3945512434895103103937587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260683246526804138583449 3945512434895103103937587)
                      ·
                        rfl

theorem cell23_7683858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_7683858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683858 prefixEnd_7683858 := by exact prefixLift 7683858
  have htrace : WordTrace (prefixWord ++ tailWord_7683858) baseStart_7683858 baseEnd_7683858 := by
    simpa [prefixWord, tailWord_7683858, baseEnd_7683858] using wordTrace_append hprefix tailTrace_7683858
  have hstable : (prefixWord ++ tailWord_7683858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683858).length < 2 ^ (prefixWord ++ tailWord_7683858).sum := by decide
  have hdescent : baseEnd_7683858 < baseStart_7683858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683873 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 1, 8]
def baseStart_7683873 : Nat := 118140960795 + 7683873 * 2 ^ 59
def prefixEnd_7683873 : Nat := 4983230072969 + 3 ^ 40 * 7683873 * 2
def baseEnd_7683873 : Nat := 1315173379034973515083339

theorem tailTrace_7683873 : CollatzResearch.WordTrace tailWord_7683873 prefixEnd_7683873 1315173379034973515083339 := by
  unfold tailWord_7683873
  simp only [CollatzResearch.WordTrace]
  refine ⟨280253872091647896875888273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186835914727765264583925515 280253872091647896875888273)
  ·
    refine ⟨210190404068735922656916205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280253872091647896875888273 210190404068735922656916205)
    ·
      refine ⟨78821401525775970996343577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210190404068735922656916205 78821401525775970996343577)
      ·
        refine ⟨59116051144331978247257683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78821401525775970996343577 59116051144331978247257683)
        ·
          refine ⟨88674076716497967370886525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59116051144331978247257683 88674076716497967370886525)
          ·
            refine ⟨33252778768686737764082447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88674076716497967370886525 33252778768686737764082447)
            ·
              refine ⟨49879168153030106646123671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33252778768686737764082447 49879168153030106646123671)
              ·
                refine ⟨74818752229545159969185507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49879168153030106646123671 74818752229545159969185507)
                ·
                  refine ⟨112228128344317739953778261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74818752229545159969185507 112228128344317739953778261)
                  ·
                    refine ⟨1315173379034973515083339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112228128344317739953778261 1315173379034973515083339)
                    ·
                      rfl

theorem cell23_7683873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_7683873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683873 prefixEnd_7683873 := by exact prefixLift 7683873
  have htrace : WordTrace (prefixWord ++ tailWord_7683873) baseStart_7683873 baseEnd_7683873 := by
    simpa [prefixWord, tailWord_7683873, baseEnd_7683873] using wordTrace_append hprefix tailTrace_7683873
  have hstable : (prefixWord ++ tailWord_7683873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683873).length < 2 ^ (prefixWord ++ tailWord_7683873).sum := by decide
  have hdescent : baseEnd_7683873 < baseStart_7683873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683883 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 3]
def baseStart_7683883 : Nat := 118140960795 + 7683883 * 2 ^ 59
def prefixEnd_7683883 : Nat := 4983230072969 + 3 ^ 40 * 7683883 * 2
def baseEnd_7683883 : Nat := 3945525271911465506124971

theorem tailTrace_7683883 : CollatzResearch.WordTrace tailWord_7683883 prefixEnd_7683883 3945525271911465506124971 := by
  unfold tailWord_7683883
  simp only [CollatzResearch.WordTrace]
  refine ⟨280254236821611668583752303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186836157881074445722501535 280254236821611668583752303)
  ·
    refine ⟨420381355232417502875628455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280254236821611668583752303 420381355232417502875628455)
    ·
      refine ⟨630572032848626254313442683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420381355232417502875628455 630572032848626254313442683)
      ·
        refine ⟨945858049272939381470164025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630572032848626254313442683 945858049272939381470164025)
        ·
          refine ⟨709393536954704536102623019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945858049272939381470164025 709393536954704536102623019)
          ·
            refine ⟨1064090305432056804153934529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709393536954704536102623019 1064090305432056804153934529)
            ·
              refine ⟨798067729074042603115450897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064090305432056804153934529 798067729074042603115450897)
              ·
                refine ⟨598550796805531952336588173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798067729074042603115450897 598550796805531952336588173)
                ·
                  refine ⟨224456548802074482126220565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598550796805531952336588173 224456548802074482126220565)
                  ·
                    refine ⟨10521400725097241349666589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 224456548802074482126220565 10521400725097241349666589)
                    ·
                      refine ⟨3945525271911465506124971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10521400725097241349666589 3945525271911465506124971)
                      ·
                        rfl

theorem cell23_7683883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 3].length) (baseStart_7683883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683883 prefixEnd_7683883 := by exact prefixLift 7683883
  have htrace : WordTrace (prefixWord ++ tailWord_7683883) baseStart_7683883 baseEnd_7683883 := by
    simpa [prefixWord, tailWord_7683883, baseEnd_7683883] using wordTrace_append hprefix tailTrace_7683883
  have hstable : (prefixWord ++ tailWord_7683883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683883).length < 2 ^ (prefixWord ++ tailWord_7683883).sum := by decide
  have hdescent : baseEnd_7683883 < baseStart_7683883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683901 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 1, 3, 2]
def baseStart_7683901 : Nat := 118140960795 + 7683901 * 2 ^ 59
def prefixEnd_7683901 : Nat := 4983230072969 + 3 ^ 40 * 7683901 * 2
def baseEnd_7683901 : Nat := 3945534514563246435699889

theorem tailTrace_7683901 : CollatzResearch.WordTrace tailWord_7683901 prefixEnd_7683901 3945534514563246435699889 := by
  unfold tailWord_7683901
  simp only [CollatzResearch.WordTrace]
  refine ⟨280254893335546457657907557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186836595557030971771938371 280254893335546457657907557)
  ·
    refine ⟨52547792500414960810857667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280254893335546457657907557 52547792500414960810857667)
    ·
      refine ⟨78821688750622441216286501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52547792500414960810857667 78821688750622441216286501)
      ·
        refine ⟨14779066640741707728053719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78821688750622441216286501 14779066640741707728053719)
        ·
          refine ⟨22168599961112561592080579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14779066640741707728053719 22168599961112561592080579)
          ·
            refine ⟨33252899941668842388120869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22168599961112561592080579 33252899941668842388120869)
            ·
              refine ⟨6234918739062907947772663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33252899941668842388120869 6234918739062907947772663)
              ·
                refine ⟨9352378108594361921658995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234918739062907947772663 9352378108594361921658995)
                ·
                  refine ⟨14028567162891542882488493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9352378108594361921658995 14028567162891542882488493)
                  ·
                    refine ⟨5260712686084328580933185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14028567162891542882488493 5260712686084328580933185)
                    ·
                      refine ⟨3945534514563246435699889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260712686084328580933185 3945534514563246435699889)
                      ·
                        rfl

theorem cell23_7683901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_7683901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683901 prefixEnd_7683901 := by exact prefixLift 7683901
  have htrace : WordTrace (prefixWord ++ tailWord_7683901) baseStart_7683901 baseEnd_7683901 := by
    simpa [prefixWord, tailWord_7683901, baseEnd_7683901] using wordTrace_append hprefix tailTrace_7683901
  have hstable : (prefixWord ++ tailWord_7683901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683901).length < 2 ^ (prefixWord ++ tailWord_7683901).sum := by decide
  have hdescent : baseEnd_7683901 < baseStart_7683901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683930 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3]
def baseStart_7683930 : Nat := 118140960795 + 7683930 * 2 ^ 59
def prefixEnd_7683930 : Nat := 4983230072969 + 3 ^ 40 * 7683930 * 2
def baseEnd_7683930 : Nat := 3945549405502226822237255

theorem tailTrace_7683930 : CollatzResearch.WordTrace tailWord_7683930 prefixEnd_7683930 3945549405502226822237255 := by
  unfold tailWord_7683930
  simp only [CollatzResearch.WordTrace]
  refine ⟨70063987763110348902678311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186837300701627597073808829 70063987763110348902678311)
  ·
    refine ⟨105095981644665523354017467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70063987763110348902678311 105095981644665523354017467)
    ·
      refine ⟨157643972466998285031026201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105095981644665523354017467 157643972466998285031026201)
      ·
        refine ⟨118232979350248713773269651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157643972466998285031026201 118232979350248713773269651)
        ·
          refine ⟨177349469025373070659904477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118232979350248713773269651 177349469025373070659904477)
          ·
            refine ⟨66506050884514901497464179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177349469025373070659904477 66506050884514901497464179)
            ·
              refine ⟨99759076326772352246196269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66506050884514901497464179 99759076326772352246196269)
              ·
                refine ⟨37409653622539632092323601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99759076326772352246196269 37409653622539632092323601)
                ·
                  refine ⟨28057240216904724069242701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37409653622539632092323601 28057240216904724069242701)
                  ·
                    refine ⟨10521465081339271525966013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28057240216904724069242701 10521465081339271525966013)
                    ·
                      refine ⟨3945549405502226822237255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10521465081339271525966013 3945549405502226822237255)
                      ·
                        rfl

theorem cell23_7683930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_7683930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683930 prefixEnd_7683930 := by exact prefixLift 7683930
  have htrace : WordTrace (prefixWord ++ tailWord_7683930) baseStart_7683930 baseEnd_7683930 := by
    simpa [prefixWord, tailWord_7683930, baseEnd_7683930] using wordTrace_append hprefix tailTrace_7683930
  have hstable : (prefixWord ++ tailWord_7683930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683930).length < 2 ^ (prefixWord ++ tailWord_7683930).sum := by decide
  have hdescent : baseEnd_7683930 < baseStart_7683930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683982 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7683982 : Nat := 118140960795 + 7683982 * 2 ^ 59
def prefixEnd_7683982 : Nat := 4983230072969 + 3 ^ 40 * 7683982 * 2
def baseEnd_7683982 : Nat := 3945576106496260618787017

theorem tailTrace_7683982 : CollatzResearch.WordTrace tailWord_7683982 prefixEnd_7683982 3945576106496260618787017 := by
  unfold tailWord_7683982
  simp only [CollatzResearch.WordTrace]
  refine ⟨35032230956031626061450775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186838565098835338994404133 35032230956031626061450775)
  ·
    refine ⟨52548346434047439092176163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35032230956031626061450775 52548346434047439092176163)
    ·
      refine ⟨78822519651071158638264245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52548346434047439092176163 78822519651071158638264245)
      ·
        refine ⟨7389611217287921122337273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78822519651071158638264245 7389611217287921122337273)
        ·
          refine ⟨5542208412965940841752955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7389611217287921122337273 5542208412965940841752955)
          ·
            refine ⟨8313312619448911262629433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5542208412965940841752955 8313312619448911262629433)
            ·
              refine ⟨6234984464586683446972075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8313312619448911262629433 6234984464586683446972075)
              ·
                refine ⟨9352476696880025170458113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234984464586683446972075 9352476696880025170458113)
                ·
                  refine ⟨7014357522660018877843585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9352476696880025170458113 7014357522660018877843585)
                  ·
                    refine ⟨5260768141995014158382689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7014357522660018877843585 5260768141995014158382689)
                    ·
                      refine ⟨3945576106496260618787017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260768141995014158382689 3945576106496260618787017)
                      ·
                        rfl

theorem cell23_7683982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7683982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683982 prefixEnd_7683982 := by exact prefixLift 7683982
  have htrace : WordTrace (prefixWord ++ tailWord_7683982) baseStart_7683982 baseEnd_7683982 := by
    simpa [prefixWord, tailWord_7683982, baseEnd_7683982] using wordTrace_append hprefix tailTrace_7683982
  have hstable : (prefixWord ++ tailWord_7683982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683982).length < 2 ^ (prefixWord ++ tailWord_7683982).sum := by decide
  have hdescent : baseEnd_7683982 < baseStart_7683982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7683983 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_7683983 : Nat := 118140960795 + 7683983 * 2 ^ 59
def prefixEnd_7683983 : Nat := 4983230072969 + 3 ^ 40 * 7683983 * 2
def baseEnd_7683983 : Nat := 3945576619976915114874511

theorem tailTrace_7683983 : CollatzResearch.WordTrace tailWord_7683983 prefixEnd_7683983 3945576619976915114874511 := by
  unfold tailWord_7683983
  simp only [CollatzResearch.WordTrace]
  refine ⟨280257884121249385662392603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186838589414166257108261735 280257884121249385662392603)
  ·
    refine ⟨420386826181874078493588905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280257884121249385662392603 420386826181874078493588905)
    ·
      refine ⟨315290119636405558870191679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420386826181874078493588905 315290119636405558870191679)
      ·
        refine ⟨472935179454608338305287519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315290119636405558870191679 472935179454608338305287519)
        ·
          refine ⟨709402769181912507457931279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472935179454608338305287519 709402769181912507457931279)
          ·
            refine ⟨1064104153772868761186896919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709402769181912507457931279 1064104153772868761186896919)
            ·
              refine ⟨1596156230659303141780345379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064104153772868761186896919 1596156230659303141780345379)
              ·
                refine ⟨2394234345988954712670518069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596156230659303141780345379 2394234345988954712670518069)
                ·
                  refine ⟨224459469936464504312861069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2394234345988954712670518069 224459469936464504312861069)
                  ·
                    refine ⟨84172301226174189117322901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224459469936464504312861069 84172301226174189117322901)
                    ·
                      refine ⟨3945576619976915114874511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84172301226174189117322901 3945576619976915114874511)
                      ·
                        rfl

theorem cell23_7683983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_7683983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7683983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7683983 prefixEnd_7683983 := by exact prefixLift 7683983
  have htrace : WordTrace (prefixWord ++ tailWord_7683983) baseStart_7683983 baseEnd_7683983 := by
    simpa [prefixWord, tailWord_7683983, baseEnd_7683983] using wordTrace_append hprefix tailTrace_7683983
  have hstable : (prefixWord ++ tailWord_7683983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7683983).length < 2 ^ (prefixWord ++ tailWord_7683983).sum := by decide
  have hdescent : baseEnd_7683983 < baseStart_7683983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7683983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684047 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 1, 5, 2]
def baseStart_7684047 : Nat := 118140960795 + 7684047 * 2 ^ 59
def prefixEnd_7684047 : Nat := 4983230072969 + 3 ^ 40 * 7684047 * 2
def baseEnd_7684047 : Nat := 3945609482738802864474217

theorem tailTrace_7684047 : CollatzResearch.WordTrace tailWord_7684047 prefixEnd_7684047 3945609482738802864474217 := by
  unfold tailWord_7684047
  simp only [CollatzResearch.WordTrace]
  refine ⟨280260218393017524592722395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186840145595345016395148263 280260218393017524592722395)
  ·
    refine ⟨420390327589526286889083593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280260218393017524592722395 420390327589526286889083593)
    ·
      refine ⟨315292745692144715166812695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420390327589526286889083593 315292745692144715166812695)
      ·
        refine ⟨472939118538217072750219043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315292745692144715166812695 472939118538217072750219043)
        ·
          refine ⟨709408677807325609125328565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472939118538217072750219043 709408677807325609125328565)
          ·
            refine ⟨66507063544436775855499553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 709408677807325609125328565 66507063544436775855499553)
            ·
              refine ⟨49880297658327581891624665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66507063544436775855499553 49880297658327581891624665)
              ·
                refine ⟨37410223243745686418718499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49880297658327581891624665 37410223243745686418718499)
                ·
                  refine ⟨56115334865618529628077749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37410223243745686418718499 56115334865618529628077749)
                  ·
                    refine ⟨5260812643651737152632289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56115334865618529628077749 5260812643651737152632289)
                    ·
                      refine ⟨3945609482738802864474217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260812643651737152632289 3945609482738802864474217)
                      ·
                        rfl

theorem cell23_7684047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 5, 2].length) (baseStart_7684047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684047 prefixEnd_7684047 := by exact prefixLift 7684047
  have htrace : WordTrace (prefixWord ++ tailWord_7684047) baseStart_7684047 baseEnd_7684047 := by
    simpa [prefixWord, tailWord_7684047, baseEnd_7684047] using wordTrace_append hprefix tailTrace_7684047
  have hstable : (prefixWord ++ tailWord_7684047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684047).length < 2 ^ (prefixWord ++ tailWord_7684047).sum := by decide
  have hdescent : baseEnd_7684047 < baseStart_7684047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684090 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_7684090 : Nat := 118140960795 + 7684090 * 2 ^ 59
def prefixEnd_7684090 : Nat := 4983230072969 + 3 ^ 40 * 7684090 * 2
def baseEnd_7684090 : Nat := 3945631562406946196236519

theorem tailTrace_7684090 : CollatzResearch.WordTrace tailWord_7684090 prefixEnd_7684090 3945631562406946196236519 := by
  unfold tailWord_7684090
  simp only [CollatzResearch.WordTrace]
  refine ⟨70065446682965435734134431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186841191154574495291025149 70065446682965435734134431)
  ·
    refine ⟨105098170024448153601201647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70065446682965435734134431 105098170024448153601201647)
    ·
      refine ⟨157647255036672230401802471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105098170024448153601201647 157647255036672230401802471)
      ·
        refine ⟨236470882555008345602703707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157647255036672230401802471 236470882555008345602703707)
        ·
          refine ⟨354706323832512518404055561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236470882555008345602703707 354706323832512518404055561)
          ·
            refine ⟨266029742874384388803041671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354706323832512518404055561 266029742874384388803041671)
            ·
              refine ⟨399044614311576583204562507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266029742874384388803041671 399044614311576583204562507)
              ·
                refine ⟨598566921467364874806843761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399044614311576583204562507 598566921467364874806843761)
                ·
                  refine ⟨448925191100523656105132821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598566921467364874806843761 448925191100523656105132821)
                  ·
                    refine ⟨21043368332837046379928101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 448925191100523656105132821 21043368332837046379928101)
                    ·
                      refine ⟨3945631562406946196236519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21043368332837046379928101 3945631562406946196236519)
                      ·
                        rfl

theorem cell23_7684090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_7684090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684090 prefixEnd_7684090 := by exact prefixLift 7684090
  have htrace : WordTrace (prefixWord ++ tailWord_7684090) baseStart_7684090 baseEnd_7684090 := by
    simpa [prefixWord, tailWord_7684090, baseEnd_7684090] using wordTrace_append hprefix tailTrace_7684090
  have hstable : (prefixWord ++ tailWord_7684090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684090).length < 2 ^ (prefixWord ++ tailWord_7684090).sum := by decide
  have hdescent : baseEnd_7684090 < baseStart_7684090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684097 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_7684097 : Nat := 118140960795 + 7684097 * 2 ^ 59
def prefixEnd_7684097 : Nat := 4983230072969 + 3 ^ 40 * 7684097 * 2
def baseEnd_7684097 : Nat := 3945635156771527668848987

theorem tailTrace_7684097 : CollatzResearch.WordTrace tailWord_7684097 prefixEnd_7684097 3945635156771527668848987 := by
  unfold tailWord_7684097
  simp only [CollatzResearch.WordTrace]
  refine ⟨280262042042836383132042545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186841361361890922088028363 280262042042836383132042545)
  ·
    refine ⟨210196531532127287349031909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280262042042836383132042545 210196531532127287349031909)
    ·
      refine ⟨39411849662273866377943483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210196531532127287349031909 39411849662273866377943483)
      ·
        refine ⟨59117774493410799566915225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39411849662273866377943483 59117774493410799566915225)
        ·
          refine ⟨44338330870058099675186419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59117774493410799566915225 44338330870058099675186419)
          ·
            refine ⟨66507496305087149512779629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44338330870058099675186419 66507496305087149512779629)
            ·
              refine ⟨24940311114407681067292361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66507496305087149512779629 24940311114407681067292361)
              ·
                refine ⟨18705233335805760800469271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24940311114407681067292361 18705233335805760800469271)
                ·
                  refine ⟨28057850003708641200703907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18705233335805760800469271 28057850003708641200703907)
                  ·
                    refine ⟨42086775005562961801055861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28057850003708641200703907 42086775005562961801055861)
                    ·
                      refine ⟨3945635156771527668848987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42086775005562961801055861 3945635156771527668848987)
                      ·
                        rfl

theorem cell23_7684097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_7684097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684097 prefixEnd_7684097 := by exact prefixLift 7684097
  have htrace : WordTrace (prefixWord ++ tailWord_7684097) baseStart_7684097 baseEnd_7684097 := by
    simpa [prefixWord, tailWord_7684097, baseEnd_7684097] using wordTrace_append hprefix tailTrace_7684097
  have hstable : (prefixWord ++ tailWord_7684097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684097).length < 2 ^ (prefixWord ++ tailWord_7684097).sum := by decide
  have hdescent : baseEnd_7684097 < baseStart_7684097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684117 : List Nat := [1, 3, 2, 1, 5, 1, 1, 9]
def baseStart_7684117 : Nat := 118140960795 + 7684117 * 2 ^ 59
def prefixEnd_7684117 : Nat := 4983230072969 + 3 ^ 40 * 7684117 * 2
def baseEnd_7684117 : Nat := 146135015792022873725885

theorem tailTrace_7684117 : CollatzResearch.WordTrace tailWord_7684117 prefixEnd_7684117 146135015792022873725885 := by
  unfold tailWord_7684117
  simp only [CollatzResearch.WordTrace]
  refine ⟨280262771502763926547770605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186841847668509284365180403 280262771502763926547770605)
  ·
    refine ⟨105098539313536472455413977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280262771502763926547770605 105098539313536472455413977)
    ·
      refine ⟨78823904485152354341560483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105098539313536472455413977 78823904485152354341560483)
      ·
        refine ⟨118235856727728531512340725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78823904485152354341560483 118235856727728531512340725)
        ·
          refine ⟨11084611568224549829281943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118235856727728531512340725 11084611568224549829281943)
          ·
            refine ⟨16626917352336824743922915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11084611568224549829281943 16626917352336824743922915)
            ·
              refine ⟨24940376028505237115884373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16626917352336824743922915 24940376028505237115884373)
              ·
                refine ⟨146135015792022873725885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24940376028505237115884373 146135015792022873725885)
                ·
                  rfl

theorem cell23_7684117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 9].length) (baseStart_7684117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684117 prefixEnd_7684117 := by exact prefixLift 7684117
  have htrace : WordTrace (prefixWord ++ tailWord_7684117) baseStart_7684117 baseEnd_7684117 := by
    simpa [prefixWord, tailWord_7684117, baseEnd_7684117] using wordTrace_append hprefix tailTrace_7684117
  have hstable : (prefixWord ++ tailWord_7684117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684117).length < 2 ^ (prefixWord ++ tailWord_7684117).sum := by decide
  have hdescent : baseEnd_7684117 < baseStart_7684117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684127 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 3]
def baseStart_7684127 : Nat := 118140960795 + 7684127 * 2 ^ 59
def prefixEnd_7684127 : Nat := 4983230072969 + 3 ^ 40 * 7684127 * 2
def baseEnd_7684127 : Nat := 3945650561191162551473849

theorem tailTrace_7684127 : CollatzResearch.WordTrace tailWord_7684127 prefixEnd_7684127 3945650561191162551473849 := by
  unfold tailWord_7684127
  simp only [CollatzResearch.WordTrace]
  refine ⟨280263136232727698255634635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186842090821818465503756423 280263136232727698255634635)
  ·
    refine ⟨420394704349091547383451953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280263136232727698255634635 420394704349091547383451953)
    ·
      refine ⟨315296028261818660537588965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420394704349091547383451953 315296028261818660537588965)
      ·
        refine ⟨59118005299090998850797931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315296028261818660537588965 59118005299090998850797931)
        ·
          refine ⟨88677007948636498276196897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59118005299090998850797931 88677007948636498276196897)
          ·
            refine ⟨66507755961477373707147673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88677007948636498276196897 66507755961477373707147673)
            ·
              refine ⟨49880816971108030280360755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66507755961477373707147673 49880816971108030280360755)
              ·
                refine ⟨74821225456662045420541133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49880816971108030280360755 74821225456662045420541133)
                ·
                  refine ⟨28057959546248267032702925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74821225456662045420541133 28057959546248267032702925)
                  ·
                    refine ⟨10521734829843100137263597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28057959546248267032702925 10521734829843100137263597)
                    ·
                      refine ⟨3945650561191162551473849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10521734829843100137263597 3945650561191162551473849)
                      ·
                        rfl

theorem cell23_7684127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_7684127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684127 prefixEnd_7684127 := by exact prefixLift 7684127
  have htrace : WordTrace (prefixWord ++ tailWord_7684127) baseStart_7684127 baseEnd_7684127 := by
    simpa [prefixWord, tailWord_7684127, baseEnd_7684127] using wordTrace_append hprefix tailTrace_7684127
  have hstable : (prefixWord ++ tailWord_7684127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684127).length < 2 ^ (prefixWord ++ tailWord_7684127).sum := by decide
  have hdescent : baseEnd_7684127 < baseStart_7684127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684137 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 3, 9, 2]
def baseStart_7684137 : Nat := 118140960795 + 7684137 * 2 ^ 59
def prefixEnd_7684137 : Nat := 4983230072969 + 3 ^ 40 * 7684137 * 2
def baseEnd_7684137 : Nat := 3945655695997707512348803

theorem tailTrace_7684137 : CollatzResearch.WordTrace tailWord_7684137 prefixEnd_7684137 3945655695997707512348803 := by
  unfold tailWord_7684137
  simp only [CollatzResearch.WordTrace]
  refine ⟨280263500962691469963498665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186842333975127646642332443 280263500962691469963498665)
  ·
    refine ⟨210197625722018602472623999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280263500962691469963498665 210197625722018602472623999)
    ·
      refine ⟨315296438583027903708935999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210197625722018602472623999 315296438583027903708935999)
      ·
        refine ⟨472944657874541855563403999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315296438583027903708935999 472944657874541855563403999)
        ·
          refine ⟨709416986811812783345105999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472944657874541855563403999 709416986811812783345105999)
          ·
            refine ⟨1064125480217719175017658999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709416986811812783345105999 1064125480217719175017658999)
            ·
              refine ⟨1596188220326578762526488499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064125480217719175017658999 1596188220326578762526488499)
              ·
                refine ⟨2394282330489868143789732749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596188220326578762526488499 2394282330489868143789732749)
                ·
                  refine ⟨897855873933700553921149781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2394282330489868143789732749 897855873933700553921149781)
                  ·
                    refine ⟨5260874261330276683131737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 897855873933700553921149781 5260874261330276683131737)
                    ·
                      refine ⟨3945655695997707512348803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260874261330276683131737 3945655695997707512348803)
                      ·
                        rfl

theorem cell23_7684137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 9, 2].length) (baseStart_7684137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684137 prefixEnd_7684137 := by exact prefixLift 7684137
  have htrace : WordTrace (prefixWord ++ tailWord_7684137) baseStart_7684137 baseEnd_7684137 := by
    simpa [prefixWord, tailWord_7684137, baseEnd_7684137] using wordTrace_append hprefix tailTrace_7684137
  have hstable : (prefixWord ++ tailWord_7684137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684137).length < 2 ^ (prefixWord ++ tailWord_7684137).sum := by decide
  have hdescent : baseEnd_7684137 < baseStart_7684137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684144 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 4, 1, 3]
def baseStart_7684144 : Nat := 118140960795 + 7684144 * 2 ^ 59
def prefixEnd_7684144 : Nat := 4983230072969 + 3 ^ 40 * 7684144 * 2
def baseEnd_7684144 : Nat := 3945659290362288984961271

theorem tailTrace_7684144 : CollatzResearch.WordTrace tailWord_7684144 prefixEnd_7684144 3945659290362288984961271 := by
  unfold tailWord_7684144
  simp only [CollatzResearch.WordTrace]
  refine ⟨140131878136833055079501743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186842504182444073439335657 140131878136833055079501743)
  ·
    refine ⟨210197817205249582619252615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140131878136833055079501743 210197817205249582619252615)
    ·
      refine ⟨315296725807874373928878923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210197817205249582619252615 315296725807874373928878923)
      ·
        refine ⟨472945088711811560893318385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315296725807874373928878923 472945088711811560893318385)
        ·
          refine ⟨354708816533858670669988789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472945088711811560893318385 354708816533858670669988789)
          ·
            refine ⟨33253951550049250375311449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 354708816533858670669988789 33253951550049250375311449)
            ·
              refine ⟨24940463662536937781483587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33253951550049250375311449 24940463662536937781483587)
              ·
                refine ⟨37410695493805406672225381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24940463662536937781483587 37410695493805406672225381)
                ·
                  refine ⟨7014505405088513751042259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37410695493805406672225381 7014505405088513751042259)
                  ·
                    refine ⟨10521758107632770626563389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7014505405088513751042259 10521758107632770626563389)
                    ·
                      refine ⟨3945659290362288984961271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10521758107632770626563389 3945659290362288984961271)
                      ·
                        rfl

theorem cell23_7684144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4, 1, 3].length) (baseStart_7684144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684144 prefixEnd_7684144 := by exact prefixLift 7684144
  have htrace : WordTrace (prefixWord ++ tailWord_7684144) baseStart_7684144 baseEnd_7684144 := by
    simpa [prefixWord, tailWord_7684144, baseEnd_7684144] using wordTrace_append hprefix tailTrace_7684144
  have hstable : (prefixWord ++ tailWord_7684144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684144).length < 2 ^ (prefixWord ++ tailWord_7684144).sum := by decide
  have hdescent : baseEnd_7684144 < baseStart_7684144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684145 : List Nat := [1, 2, 2, 3, 1, 4, 3, 2, 1, 2, 2]
def baseStart_7684145 : Nat := 118140960795 + 7684145 * 2 ^ 59
def prefixEnd_7684145 : Nat := 4983230072969 + 3 ^ 40 * 7684145 * 2
def baseEnd_7684145 : Nat := 3945659803842943481048767

theorem tailTrace_7684145 : CollatzResearch.WordTrace tailWord_7684145 prefixEnd_7684145 3945659803842943481048767 := by
  unfold tailWord_7684145
  simp only [CollatzResearch.WordTrace]
  refine ⟨280263792746662487329789889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186842528497774991553193259 280263792746662487329789889)
  ·
    refine ⟨210197844559996865497342417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280263792746662487329789889 210197844559996865497342417)
    ·
      refine ⟨157648383419997649123006813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210197844559996865497342417 157648383419997649123006813)
      ·
        refine ⟨59118143782499118421127555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157648383419997649123006813 59118143782499118421127555)
        ·
          refine ⟨88677215673748677631691333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59118143782499118421127555 88677215673748677631691333)
          ·
            refine ⟨16626977938827877055942125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88677215673748677631691333 16626977938827877055942125)
            ·
              refine ⟨6235116727060453895978297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16626977938827877055942125 6235116727060453895978297)
              ·
                refine ⟨4676337545295340421983723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6235116727060453895978297 4676337545295340421983723)
                ·
                  refine ⟨7014506317943010632975585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676337545295340421983723 7014506317943010632975585)
                  ·
                    refine ⟨5260879738457257974731689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7014506317943010632975585 5260879738457257974731689)
                    ·
                      refine ⟨3945659803842943481048767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260879738457257974731689 3945659803842943481048767)
                      ·
                        rfl

theorem cell23_7684145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_7684145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684145 prefixEnd_7684145 := by exact prefixLift 7684145
  have htrace : WordTrace (prefixWord ++ tailWord_7684145) baseStart_7684145 baseEnd_7684145 := by
    simpa [prefixWord, tailWord_7684145, baseEnd_7684145] using wordTrace_append hprefix tailTrace_7684145
  have hstable : (prefixWord ++ tailWord_7684145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684145).length < 2 ^ (prefixWord ++ tailWord_7684145).sum := by decide
  have hdescent : baseEnd_7684145 < baseStart_7684145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684154 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2]
def baseStart_7684154 : Nat := 118140960795 + 7684154 * 2 ^ 59
def prefixEnd_7684154 : Nat := 4983230072969 + 3 ^ 40 * 7684154 * 2
def baseEnd_7684154 : Nat := 3945664425168833945836225

theorem tailTrace_7684154 : CollatzResearch.WordTrace tailWord_7684154 prefixEnd_7684154 3945664425168833945836225 := by
  unfold tailWord_7684154
  simp only [CollatzResearch.WordTrace]
  refine ⟨70066030250907470466716879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186842747335753254577911677 70066030250907470466716879)
  ·
    refine ⟨105099045376361205700075319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70066030250907470466716879 105099045376361205700075319)
    ·
      refine ⟨157648568064541808550112979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105099045376361205700075319 157648568064541808550112979)
      ·
        refine ⟨236472852096812712825169469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157648568064541808550112979 236472852096812712825169469)
        ·
          refine ⟨88677319536304767309438551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236472852096812712825169469 88677319536304767309438551)
          ·
            refine ⟨133015979304457150964157827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88677319536304767309438551 133015979304457150964157827)
            ·
              refine ⟨199523968956685726446236741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133015979304457150964157827 199523968956685726446236741)
              ·
                refine ⟨37410744179378573708669389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199523968956685726446236741 37410744179378573708669389)
                ·
                  refine ⟨14029029067266965140751021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37410744179378573708669389 14029029067266965140751021)
                  ·
                    refine ⟨5260885900225111927781633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14029029067266965140751021 5260885900225111927781633)
                    ·
                      refine ⟨3945664425168833945836225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260885900225111927781633 3945664425168833945836225)
                      ·
                        rfl

theorem cell23_7684154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2].length) (baseStart_7684154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684154 prefixEnd_7684154 := by exact prefixLift 7684154
  have htrace : WordTrace (prefixWord ++ tailWord_7684154) baseStart_7684154 baseEnd_7684154 := by
    simpa [prefixWord, tailWord_7684154, baseEnd_7684154] using wordTrace_append hprefix tailTrace_7684154
  have hstable : (prefixWord ++ tailWord_7684154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684154).length < 2 ^ (prefixWord ++ tailWord_7684154).sum := by decide
  have hdescent : baseEnd_7684154 < baseStart_7684154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684184 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 3, 4, 2]
def baseStart_7684184 : Nat := 118140960795 + 7684184 * 2 ^ 59
def prefixEnd_7684184 : Nat := 4983230072969 + 3 ^ 40 * 7684184 * 2
def baseEnd_7684184 : Nat := 3945679829588468828461087

theorem tailTrace_7684184 : CollatzResearch.WordTrace tailWord_7684184 prefixEnd_7684184 3945679829588468828461087 := by
  unfold tailWord_7684184
  simp only [CollatzResearch.WordTrace]
  refine ⟨140132607596760598495229803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186843476795680797993639737 140132607596760598495229803)
  ·
    refine ⟨210198911395140897742844705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140132607596760598495229803 210198911395140897742844705)
    ·
      refine ⟨157649183546355673307133529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210198911395140897742844705 157649183546355673307133529)
      ·
        refine ⟨118236887659766754980350147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157649183546355673307133529 118236887659766754980350147)
        ·
          refine ⟨177355331489650132470525221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118236887659766754980350147 177355331489650132470525221)
          ·
            refine ⟨33254124654309399838223479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177355331489650132470525221 33254124654309399838223479)
            ·
              refine ⟨49881186981464099757335219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33254124654309399838223479 49881186981464099757335219)
              ·
                refine ⟨74821780472196149636002829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49881186981464099757335219 74821780472196149636002829)
                ·
                  refine ⟨28058167677073556113501061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74821780472196149636002829 28058167677073556113501061)
                  ·
                    refine ⟨5260906439451291771281449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28058167677073556113501061 5260906439451291771281449)
                    ·
                      refine ⟨3945679829588468828461087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5260906439451291771281449 3945679829588468828461087)
                      ·
                        rfl

theorem cell23_7684184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_7684184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684184 prefixEnd_7684184 := by exact prefixLift 7684184
  have htrace : WordTrace (prefixWord ++ tailWord_7684184) baseStart_7684184 baseEnd_7684184 := by
    simpa [prefixWord, tailWord_7684184, baseEnd_7684184] using wordTrace_append hprefix tailTrace_7684184
  have hstable : (prefixWord ++ tailWord_7684184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684184).length < 2 ^ (prefixWord ++ tailWord_7684184).sum := by decide
  have hdescent : baseEnd_7684184 < baseStart_7684184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684214 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_7684214 : Nat := 118140960795 + 7684214 * 2 ^ 59
def prefixEnd_7684214 : Nat := 4983230072969 + 3 ^ 40 * 7684214 * 2
def baseEnd_7684214 : Nat := 3945695234008103711085949

theorem tailTrace_7684214 : CollatzResearch.WordTrace tailWord_7684214 prefixEnd_7684214 3945695234008103711085949 := by
  unfold tailWord_7684214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17516644336463282007128231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186844206255608341409367797 17516644336463282007128231)
  ·
    refine ⟨26274966504694923010692347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17516644336463282007128231 26274966504694923010692347)
    ·
      refine ⟨39412449757042384516038521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26274966504694923010692347 39412449757042384516038521)
      ·
        refine ⟨29559337317781788387028891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39412449757042384516038521 29559337317781788387028891)
        ·
          refine ⟨44339005976672682580543337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29559337317781788387028891 44339005976672682580543337)
          ·
            refine ⟨33254254482504511935407503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44339005976672682580543337 33254254482504511935407503)
            ·
              refine ⟨49881381723756767903111255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33254254482504511935407503 49881381723756767903111255)
              ·
                refine ⟨74822072585635151854666883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49881381723756767903111255 74822072585635151854666883)
                ·
                  refine ⟨112233108878452727782000325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74822072585635151854666883 112233108878452727782000325)
                  ·
                    refine ⟨21043707914709886459125061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112233108878452727782000325 21043707914709886459125061)
                    ·
                      refine ⟨3945695234008103711085949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21043707914709886459125061 3945695234008103711085949)
                      ·
                        rfl

theorem cell23_7684214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_7684214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684214 prefixEnd_7684214 := by exact prefixLift 7684214
  have htrace : WordTrace (prefixWord ++ tailWord_7684214) baseStart_7684214 baseEnd_7684214 := by
    simpa [prefixWord, tailWord_7684214, baseEnd_7684214] using wordTrace_append hprefix tailTrace_7684214
  have hstable : (prefixWord ++ tailWord_7684214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684214).length < 2 ^ (prefixWord ++ tailWord_7684214).sum := by decide
  have hdescent : baseEnd_7684214 < baseStart_7684214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684246 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7684246 : Nat := 118140960795 + 7684246 * 2 ^ 59
def prefixEnd_7684246 : Nat := 4983230072969 + 3 ^ 40 * 7684246 * 2
def baseEnd_7684246 : Nat := 3945711665389047585885803

theorem tailTrace_7684246 : CollatzResearch.WordTrace tailWord_7684246 prefixEnd_7684246 3945711665389047585885803 := by
  unfold tailWord_7684246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17516717282456036348701037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186844984346197721052811061 17516717282456036348701037)
  ·
    refine ⟨6568768980921013630762889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17516717282456036348701037 6568768980921013630762889)
    ·
      refine ⟨4926576735690760223072167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6568768980921013630762889 4926576735690760223072167)
      ·
        refine ⟨7389865103536140334608251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4926576735690760223072167 7389865103536140334608251)
        ·
          refine ⟨11084797655304210501912377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7389865103536140334608251 11084797655304210501912377)
          ·
            refine ⟨8313598241478157876434283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11084797655304210501912377 8313598241478157876434283)
            ·
              refine ⟨12470397362217236814651425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8313598241478157876434283 12470397362217236814651425)
              ·
                refine ⟨9352798021662927610988569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12470397362217236814651425 9352798021662927610988569)
                ·
                  refine ⟨7014598516247195708241427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9352798021662927610988569 7014598516247195708241427)
                  ·
                    refine ⟨10521897774370793562362141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7014598516247195708241427 10521897774370793562362141)
                    ·
                      refine ⟨3945711665389047585885803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10521897774370793562362141 3945711665389047585885803)
                      ·
                        rfl

theorem cell23_7684246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7684246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684246 prefixEnd_7684246 := by exact prefixLift 7684246
  have htrace : WordTrace (prefixWord ++ tailWord_7684246) baseStart_7684246 baseEnd_7684246 := by
    simpa [prefixWord, tailWord_7684246, baseEnd_7684246] using wordTrace_append hprefix tailTrace_7684246
  have hstable : (prefixWord ++ tailWord_7684246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684246).length < 2 ^ (prefixWord ++ tailWord_7684246).sum := by decide
  have hdescent : baseEnd_7684246 < baseStart_7684246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684287 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 4]
def baseStart_7684287 : Nat := 118140960795 + 7684287 * 2 ^ 59
def prefixEnd_7684287 : Nat := 4983230072969 + 3 ^ 40 * 7684287 * 2
def baseEnd_7684287 : Nat := 3945732718095881925473113

theorem tailTrace_7684287 : CollatzResearch.WordTrace tailWord_7684287 prefixEnd_7684287 3945732718095881925473113 := by
  unfold tailWord_7684287
  simp only [CollatzResearch.WordTrace]
  refine ⟨280268971912148045581459115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186845981274765363720972743 280268971912148045581459115)
  ·
    refine ⟨420403457868222068372188673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280268971912148045581459115 420403457868222068372188673)
    ·
      refine ⟨315302593401166551279141505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420403457868222068372188673 315302593401166551279141505)
      ·
        refine ⟨236476945050874913459356129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315302593401166551279141505 236476945050874913459356129)
        ·
          refine ⟨177357708788156185094517097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236476945050874913459356129 177357708788156185094517097)
          ·
            refine ⟨133018281591117138820887823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177357708788156185094517097 133018281591117138820887823)
            ·
              refine ⟨199527422386675708231331735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133018281591117138820887823 199527422386675708231331735)
              ·
                refine ⟨299291133580013562346997603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199527422386675708231331735 299291133580013562346997603)
                ·
                  refine ⟨448936700370020343520496405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299291133580013562346997603 448936700370020343520496405)
                  ·
                    refine ⟨21043907829844703602523269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 448936700370020343520496405 21043907829844703602523269)
                    ·
                      refine ⟨3945732718095881925473113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21043907829844703602523269 3945732718095881925473113)
                      ·
                        rfl

theorem cell23_7684287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_7684287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684287 prefixEnd_7684287 := by exact prefixLift 7684287
  have htrace : WordTrace (prefixWord ++ tailWord_7684287) baseStart_7684287 baseEnd_7684287 := by
    simpa [prefixWord, tailWord_7684287, baseEnd_7684287] using wordTrace_append hprefix tailTrace_7684287
  have hstable : (prefixWord ++ tailWord_7684287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684287).length < 2 ^ (prefixWord ++ tailWord_7684287).sum := by decide
  have hdescent : baseEnd_7684287 < baseStart_7684287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684375 : List Nat := [1, 1, 3, 4, 1, 3, 1, 4, 1, 1, 3]
def baseStart_7684375 : Nat := 118140960795 + 7684375 * 2 ^ 59
def prefixEnd_7684375 : Nat := 4983230072969 + 3 ^ 40 * 7684375 * 2
def baseEnd_7684375 : Nat := 3945777904393477581172709

theorem tailTrace_7684375 : CollatzResearch.WordTrace tailWord_7684375 prefixEnd_7684375 3945777904393477581172709 := by
  unfold tailWord_7684375
  simp only [CollatzResearch.WordTrace]
  refine ⟨280272181535829236610662579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186848121023886157740441719 280272181535829236610662579)
  ·
    refine ⟨420408272303743854915993869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280272181535829236610662579 420408272303743854915993869)
    ·
      refine ⟨157653102113903945593497701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420408272303743854915993869 157653102113903945593497701)
      ·
        refine ⟨29559956646356989798780819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157653102113903945593497701 29559956646356989798780819)
        ·
          refine ⟨44339934969535484698171229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29559956646356989798780819 44339934969535484698171229)
          ·
            refine ⟨16627475613575806761814211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44339934969535484698171229 16627475613575806761814211)
            ·
              refine ⟨24941213420363710142721317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16627475613575806761814211 24941213420363710142721317)
              ·
                refine ⟨4676477516318195651760247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24941213420363710142721317 4676477516318195651760247)
                ·
                  refine ⟨7014716274477293477640371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676477516318195651760247 7014716274477293477640371)
                  ·
                    refine ⟨10522074411715940216460557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7014716274477293477640371 10522074411715940216460557)
                    ·
                      refine ⟨3945777904393477581172709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10522074411715940216460557 3945777904393477581172709)
                      ·
                        rfl

theorem cell23_7684375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_7684375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684375 prefixEnd_7684375 := by exact prefixLift 7684375
  have htrace : WordTrace (prefixWord ++ tailWord_7684375) baseStart_7684375 baseEnd_7684375 := by
    simpa [prefixWord, tailWord_7684375, baseEnd_7684375] using wordTrace_append hprefix tailTrace_7684375
  have hstable : (prefixWord ++ tailWord_7684375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684375).length < 2 ^ (prefixWord ++ tailWord_7684375).sum := by decide
  have hdescent : baseEnd_7684375 < baseStart_7684375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684402 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2]
def baseStart_7684402 : Nat := 118140960795 + 7684402 * 2 ^ 59
def prefixEnd_7684402 : Nat := 4983230072969 + 3 ^ 40 * 7684402 * 2
def baseEnd_7684402 : Nat := 3945791768371148975535085

theorem tailTrace_7684402 : CollatzResearch.WordTrace tailWord_7684402 prefixEnd_7684402 3945791768371148975535085 := by
  unfold tailWord_7684402
  simp only [CollatzResearch.WordTrace]
  refine ⟨70068291576682855055473865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186848777537820946814596973 70068291576682855055473865)
  ·
    refine ⟨52551218682512141291605399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70068291576682855055473865 52551218682512141291605399)
    ·
      refine ⟨78826828023768211937408099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52551218682512141291605399 78826828023768211937408099)
      ·
        refine ⟨118240242035652317906112149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78826828023768211937408099 118240242035652317906112149)
        ·
          refine ⟨5542511345421202401849007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118240242035652317906112149 5542511345421202401849007)
          ·
            refine ⟨8313767018131803602773511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5542511345421202401849007 8313767018131803602773511)
            ·
              refine ⟨12470650527197705404160267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8313767018131803602773511 12470650527197705404160267)
              ·
                refine ⟨18705975790796558106240401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12470650527197705404160267 18705975790796558106240401)
                ·
                  refine ⟨14029481843097418579680301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18705975790796558106240401 14029481843097418579680301)
                  ·
                    refine ⟨5261055691161531967380113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14029481843097418579680301 5261055691161531967380113)
                    ·
                      refine ⟨3945791768371148975535085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5261055691161531967380113 3945791768371148975535085)
                      ·
                        rfl

theorem cell23_7684402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_7684402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684402 prefixEnd_7684402 := by exact prefixLift 7684402
  have htrace : WordTrace (prefixWord ++ tailWord_7684402) baseStart_7684402 baseEnd_7684402 := by
    simpa [prefixWord, tailWord_7684402, baseEnd_7684402] using wordTrace_append hprefix tailTrace_7684402
  have hstable : (prefixWord ++ tailWord_7684402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684402).length < 2 ^ (prefixWord ++ tailWord_7684402).sum := by decide
  have hdescent : baseEnd_7684402 < baseStart_7684402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684434 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_7684434 : Nat := 118140960795 + 7684434 * 2 ^ 59
def prefixEnd_7684434 : Nat := 4983230072969 + 3 ^ 40 * 7684434 * 2
def baseEnd_7684434 : Nat := 1315269399917364283444979

theorem tailTrace_7684434 : CollatzResearch.WordTrace tailWord_7684434 prefixEnd_7684434 1315269399917364283444979 := by
  unfold tailWord_7684434
  simp only [CollatzResearch.WordTrace]
  refine ⟨70068583360653872421765089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186849555628410326458040237 70068583360653872421765089)
  ·
    refine ⟨52551437520490404316323817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70068583360653872421765089 52551437520490404316323817)
    ·
      refine ⟨39413578140367803237242863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52551437520490404316323817 39413578140367803237242863)
      ·
        refine ⟨59120367210551704855864295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39413578140367803237242863 59120367210551704855864295)
        ·
          refine ⟨88680550815827557283796443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59120367210551704855864295 88680550815827557283796443)
          ·
            refine ⟨133020826223741335925694665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88680550815827557283796443 133020826223741335925694665)
            ·
              refine ⟨99765619667806001944270999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133020826223741335925694665 99765619667806001944270999)
              ·
                refine ⟨149648429501709002916406499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99765619667806001944270999 149648429501709002916406499)
                ·
                  refine ⟨224472644252563504374609749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149648429501709002916406499 224472644252563504374609749)
                  ·
                    refine ⟨1315269399917364283444979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 224472644252563504374609749 1315269399917364283444979)
                    ·
                      rfl

theorem cell23_7684434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_7684434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684434 prefixEnd_7684434 := by exact prefixLift 7684434
  have htrace : WordTrace (prefixWord ++ tailWord_7684434) baseStart_7684434 baseEnd_7684434 := by
    simpa [prefixWord, tailWord_7684434, baseEnd_7684434] using wordTrace_append hprefix tailTrace_7684434
  have hstable : (prefixWord ++ tailWord_7684434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684434).length < 2 ^ (prefixWord ++ tailWord_7684434).sum := by decide
  have hdescent : baseEnd_7684434 < baseStart_7684434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684505 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 2, 2, 2]
def baseStart_7684505 : Nat := 118140960795 + 7684505 * 2 ^ 59
def prefixEnd_7684505 : Nat := 4983230072969 + 3 ^ 40 * 7684505 * 2
def baseEnd_7684505 : Nat := 3945844656878562072547111

theorem tailTrace_7684505 : CollatzResearch.WordTrace tailWord_7684505 prefixEnd_7684505 3945844656878562072547111 := by
  unfold tailWord_7684505
  simp only [CollatzResearch.WordTrace]
  refine ⟨280276923025358268812894969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186851282016905512541929979 280276923025358268812894969)
  ·
    refine ⟨210207692269018701609671227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280276923025358268812894969 210207692269018701609671227)
    ·
      refine ⟨315311538403528052414506841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210207692269018701609671227 315311538403528052414506841)
      ·
        refine ⟨236483653802646039310880131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315311538403528052414506841 236483653802646039310880131)
        ·
          refine ⟨354725480703969058966320197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236483653802646039310880131 354725480703969058966320197)
          ·
            refine ⟨66511027631994198556185037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354725480703969058966320197 66511027631994198556185037)
            ·
              refine ⟨24941635361997824458569389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66511027631994198556185037 24941635361997824458569389)
              ·
                refine ⟨9353113260749184171963521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24941635361997824458569389 9353113260749184171963521)
                ·
                  refine ⟨7014834945561888128972641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9353113260749184171963521 7014834945561888128972641)
                  ·
                    refine ⟨5261126209171416096729481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7014834945561888128972641 5261126209171416096729481)
                    ·
                      refine ⟨3945844656878562072547111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5261126209171416096729481 3945844656878562072547111)
                      ·
                        rfl

theorem cell23_7684505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 2, 2].length) (baseStart_7684505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684505 prefixEnd_7684505 := by exact prefixLift 7684505
  have htrace : WordTrace (prefixWord ++ tailWord_7684505) baseStart_7684505 baseEnd_7684505 := by
    simpa [prefixWord, tailWord_7684505, baseEnd_7684505] using wordTrace_append hprefix tailTrace_7684505
  have hstable : (prefixWord ++ tailWord_7684505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684505).length < 2 ^ (prefixWord ++ tailWord_7684505).sum := by decide
  have hdescent : baseEnd_7684505 < baseStart_7684505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684509 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_7684509 : Nat := 118140960795 + 7684509 * 2 ^ 59
def prefixEnd_7684509 : Nat := 4983230072969 + 3 ^ 40 * 7684509 * 2
def baseEnd_7684509 : Nat := 3945846710801180056897093

theorem tailTrace_7684509 : CollatzResearch.WordTrace tailWord_7684509 prefixEnd_7684509 3945846710801180056897093 := by
  unfold tailWord_7684509
  simp only [CollatzResearch.WordTrace]
  refine ⟨280277068917343777496040581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186851379278229184997360387 280277068917343777496040581)
  ·
    refine ⟨52551950422001958280507609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280277068917343777496040581 52551950422001958280507609)
    ·
      refine ⟨39413962816501468710380707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52551950422001958280507609 39413962816501468710380707)
      ·
        refine ⟨59120944224752203065571061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39413962816501468710380707 59120944224752203065571061)
        ·
          refine ⟨5542588521070519037397287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59120944224752203065571061 5542588521070519037397287)
          ·
            refine ⟨8313882781605778556095931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5542588521070519037397287 8313882781605778556095931)
            ·
              refine ⟨12470824172408667834143897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8313882781605778556095931 12470824172408667834143897)
              ·
                refine ⟨9353118129306500875607923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12470824172408667834143897 9353118129306500875607923)
                ·
                  refine ⟨14029677193959751313411885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9353118129306500875607923 14029677193959751313411885)
                  ·
                    refine ⟨5261128947734906742529457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14029677193959751313411885 5261128947734906742529457)
                    ·
                      refine ⟨3945846710801180056897093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5261128947734906742529457 3945846710801180056897093)
                      ·
                        rfl

theorem cell23_7684509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_7684509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684509 prefixEnd_7684509 := by exact prefixLift 7684509
  have htrace : WordTrace (prefixWord ++ tailWord_7684509) baseStart_7684509 baseEnd_7684509 := by
    simpa [prefixWord, tailWord_7684509, baseEnd_7684509] using wordTrace_append hprefix tailTrace_7684509
  have hstable : (prefixWord ++ tailWord_7684509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684509).length < 2 ^ (prefixWord ++ tailWord_7684509).sum := by decide
  have hdescent : baseEnd_7684509 < baseStart_7684509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684551 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_7684551 : Nat := 118140960795 + 7684551 * 2 ^ 59
def prefixEnd_7684551 : Nat := 4983230072969 + 3 ^ 40 * 7684551 * 2
def baseEnd_7684551 : Nat := 3945868276988668892571899

theorem tailTrace_7684551 : CollatzResearch.WordTrace tailWord_7684551 prefixEnd_7684551 3945868276988668892571899 := by
  unfold tailWord_7684551
  simp only [CollatzResearch.WordTrace]
  refine ⟨280278600783191618669069507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186852400522127745779379671 280278600783191618669069507)
  ·
    refine ⟨420417901174787428003604261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280278600783191618669069507 420417901174787428003604261)
    ·
      refine ⟨78828356470272642750675799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420417901174787428003604261 78828356470272642750675799)
      ·
        refine ⟨118242534705408964126013699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78828356470272642750675799 118242534705408964126013699)
        ·
          refine ⟨177363802058113446189020549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118242534705408964126013699 177363802058113446189020549)
          ·
            refine ⟨33255712885896271160441353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177363802058113446189020549 33255712885896271160441353)
            ·
              refine ⟨24941784664422203370331015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33255712885896271160441353 24941784664422203370331015)
              ·
                refine ⟨37412676996633305055496523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24941784664422203370331015 37412676996633305055496523)
                ·
                  refine ⟨56119015494949957583244785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37412676996633305055496523 56119015494949957583244785)
                  ·
                    refine ⟨42089261621212468187433589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56119015494949957583244785 42089261621212468187433589)
                    ·
                      refine ⟨3945868276988668892571899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42089261621212468187433589 3945868276988668892571899)
                      ·
                        rfl

theorem cell23_7684551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_7684551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684551 prefixEnd_7684551 := by exact prefixLift 7684551
  have htrace : WordTrace (prefixWord ++ tailWord_7684551) baseStart_7684551 baseEnd_7684551 := by
    simpa [prefixWord, tailWord_7684551, baseEnd_7684551] using wordTrace_append hprefix tailTrace_7684551
  have hstable : (prefixWord ++ tailWord_7684551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684551).length < 2 ^ (prefixWord ++ tailWord_7684551).sum := by decide
  have hdescent : baseEnd_7684551 < baseStart_7684551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684561 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_7684561 : Nat := 118140960795 + 7684561 * 2 ^ 59
def prefixEnd_7684561 : Nat := 4983230072969 + 3 ^ 40 * 7684561 * 2
def baseEnd_7684561 : Nat := 3945873411795213853446853

theorem tailTrace_7684561 : CollatzResearch.WordTrace tailWord_7684561 prefixEnd_7684561 3945873411795213853446853 := by
  unfold tailWord_7684561
  simp only [CollatzResearch.WordTrace]
  refine ⟨280278965513155390376933537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186852643675436926917955691 280278965513155390376933537)
  ·
    refine ⟨210209224134866542782700153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280278965513155390376933537 210209224134866542782700153)
    ·
      refine ⟨157656918101149907087025115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210209224134866542782700153 157656918101149907087025115)
      ·
        refine ⟨236485377151724860630537673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157656918101149907087025115 236485377151724860630537673)
        ·
          refine ⟨177364032863793645472903255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236485377151724860630537673 177364032863793645472903255)
          ·
            refine ⟨266046049295690468209354883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177364032863793645472903255 266046049295690468209354883)
            ·
              refine ⟨399069073943535702314032325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266046049295690468209354883 399069073943535702314032325)
              ·
                refine ⟨74825451364412944183881061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399069073943535702314032325 74825451364412944183881061)
                ·
                  refine ⟨14029772130827427034477699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74825451364412944183881061 14029772130827427034477699)
                  ·
                    refine ⟨21044658196241140551716549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14029772130827427034477699 21044658196241140551716549)
                    ·
                      refine ⟨3945873411795213853446853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21044658196241140551716549 3945873411795213853446853)
                      ·
                        rfl

theorem cell23_7684561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_7684561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684561 prefixEnd_7684561 := by exact prefixLift 7684561
  have htrace : WordTrace (prefixWord ++ tailWord_7684561) baseStart_7684561 baseEnd_7684561 := by
    simpa [prefixWord, tailWord_7684561, baseEnd_7684561] using wordTrace_append hprefix tailTrace_7684561
  have hstable : (prefixWord ++ tailWord_7684561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684561).length < 2 ^ (prefixWord ++ tailWord_7684561).sum := by decide
  have hdescent : baseEnd_7684561 < baseStart_7684561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684605 : List Nat := [1, 4, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_7684605 : Nat := 118140960795 + 7684605 * 2 ^ 59
def prefixEnd_7684605 : Nat := 4983230072969 + 3 ^ 40 * 7684605 * 2
def baseEnd_7684605 : Nat := 1315298668314670560432217

theorem tailTrace_7684605 : CollatzResearch.WordTrace tailWord_7684605 prefixEnd_7684605 1315298668314670560432217 := by
  unfold tailWord_7684605
  simp only [CollatzResearch.WordTrace]
  refine ⟨280280570324995985891535269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186853713549997323927690179 280280570324995985891535269)
  ·
    refine ⟨52552606935936747354662863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280280570324995985891535269 52552606935936747354662863)
    ·
      refine ⟨78828910403905121031994295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52552606935936747354662863 78828910403905121031994295)
      ·
        refine ⟨118243365605857681547991443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78828910403905121031994295 118243365605857681547991443)
        ·
          refine ⟨177365048408786522321987165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118243365605857681547991443 177365048408786522321987165)
          ·
            refine ⟨66511893153294945870745187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177365048408786522321987165 66511893153294945870745187)
            ·
              refine ⟨99767839729942418806117781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66511893153294945870745187 99767839729942418806117781)
              ·
                refine ⟨4676617487341050881536771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99767839729942418806117781 4676617487341050881536771)
                ·
                  refine ⟨7014926231011576322305157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676617487341050881536771 7014926231011576322305157)
                  ·
                    refine ⟨1315298668314670560432217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7014926231011576322305157 1315298668314670560432217)
                    ·
                      rfl

theorem cell23_7684605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_7684605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684605 prefixEnd_7684605 := by exact prefixLift 7684605
  have htrace : WordTrace (prefixWord ++ tailWord_7684605) baseStart_7684605 baseEnd_7684605 := by
    simpa [prefixWord, tailWord_7684605, baseEnd_7684605] using wordTrace_append hprefix tailTrace_7684605
  have hstable : (prefixWord ++ tailWord_7684605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684605).length < 2 ^ (prefixWord ++ tailWord_7684605).sum := by decide
  have hdescent : baseEnd_7684605 < baseStart_7684605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684705 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_7684705 : Nat := 118140960795 + 7684705 * 2 ^ 59
def prefixEnd_7684705 : Nat := 4983230072969 + 3 ^ 40 * 7684705 * 2
def baseEnd_7684705 : Nat := 3945947353009461290046191

theorem tailTrace_7684705 : CollatzResearch.WordTrace tailWord_7684705 prefixEnd_7684705 3945947353009461290046191 := by
  unfold tailWord_7684705
  simp only [CollatzResearch.WordTrace]
  refine ⟨280284217624633702970175569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186856145083089135313450379 280284217624633702970175569)
  ·
    refine ⟨210213163218475277227631677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280284217624633702970175569 210213163218475277227631677)
    ·
      refine ⟨78829936206928228960361879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210213163218475277227631677 78829936206928228960361879)
      ·
        refine ⟨118244904310392343440542819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78829936206928228960361879 118244904310392343440542819)
        ·
          refine ⟨177367356465588515160814229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118244904310392343440542819 177367356465588515160814229)
          ·
            refine ⟨8314094834324461648163167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177367356465588515160814229 8314094834324461648163167)
            ·
              refine ⟨12471142251486692472244751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8314094834324461648163167 12471142251486692472244751)
              ·
                refine ⟨18706713377230038708367127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12471142251486692472244751 18706713377230038708367127)
                ·
                  refine ⟨28060070065845058062550691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18706713377230038708367127 28060070065845058062550691)
                  ·
                    refine ⟨42090105098767587093826037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28060070065845058062550691 42090105098767587093826037)
                    ·
                      refine ⟨3945947353009461290046191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42090105098767587093826037 3945947353009461290046191)
                      ·
                        rfl

theorem cell23_7684705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_7684705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684705 prefixEnd_7684705 := by exact prefixLift 7684705
  have htrace : WordTrace (prefixWord ++ tailWord_7684705) baseStart_7684705 baseEnd_7684705 := by
    simpa [prefixWord, tailWord_7684705, baseEnd_7684705] using wordTrace_append hprefix tailTrace_7684705
  have hstable : (prefixWord ++ tailWord_7684705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684705).length < 2 ^ (prefixWord ++ tailWord_7684705).sum := by decide
  have hdescent : baseEnd_7684705 < baseStart_7684705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684756 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_7684756 : Nat := 118140960795 + 7684756 * 2 ^ 59
def prefixEnd_7684756 : Nat := 4983230072969 + 3 ^ 40 * 7684756 * 2
def baseEnd_7684756 : Nat := 3945973540522840590508457

theorem tailTrace_7684756 : CollatzResearch.WordTrace tailWord_7684756 prefixEnd_7684756 3945973540522840590508457 := by
  unfold tailWord_7684756
  simp only [CollatzResearch.WordTrace]
  refine ⟨140143038873724469340141061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186857385164965959120188081 140143038873724469340141061)
  ·
    refine ⟨26276819788823338001276449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140143038873724469340141061 26276819788823338001276449)
    ·
      refine ⟨19707614841617503500957337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26276819788823338001276449 19707614841617503500957337)
      ·
        refine ⟨14780711131213127625718003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19707614841617503500957337 14780711131213127625718003)
        ·
          refine ⟨22171066696819691438577005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14780711131213127625718003 22171066696819691438577005)
          ·
            refine ⟨8314150011307384289466377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22171066696819691438577005 8314150011307384289466377)
            ·
              refine ⟨6235612508480538217099783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8314150011307384289466377 6235612508480538217099783)
              ·
                refine ⟨9353418762720807325649675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6235612508480538217099783 9353418762720807325649675)
                ·
                  refine ⟨14030128144081210988474513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9353418762720807325649675 14030128144081210988474513)
                  ·
                    refine ⟨10522596108060908241355885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14030128144081210988474513 10522596108060908241355885)
                    ·
                      refine ⟨3945973540522840590508457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10522596108060908241355885 3945973540522840590508457)
                      ·
                        rfl

theorem cell23_7684756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_7684756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684756 prefixEnd_7684756 := by exact prefixLift 7684756
  have htrace : WordTrace (prefixWord ++ tailWord_7684756) baseStart_7684756 baseEnd_7684756 := by
    simpa [prefixWord, tailWord_7684756, baseEnd_7684756] using wordTrace_append hprefix tailTrace_7684756
  have hstable : (prefixWord ++ tailWord_7684756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684756).length < 2 ^ (prefixWord ++ tailWord_7684756).sum := by decide
  have hdescent : baseEnd_7684756 < baseStart_7684756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684845 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_7684845 : Nat := 118140960795 + 7684845 * 2 ^ 59
def prefixEnd_7684845 : Nat := 4983230072969 + 3 ^ 40 * 7684845 * 2
def baseEnd_7684845 : Nat := 1315339746767030247431849

theorem tailTrace_7684845 : CollatzResearch.WordTrace tailWord_7684845 prefixEnd_7684845 1315339746767030247431849 := by
  unfold tailWord_7684845
  simp only [CollatzResearch.WordTrace]
  refine ⟨280289323844126506880271989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186859549229417671253514659 280289323844126506880271989)
  ·
    refine ⟨26277124110386860020025499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280289323844126506880271989 26277124110386860020025499)
    ·
      refine ⟨39415686165580290030038249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26277124110386860020025499 39415686165580290030038249)
      ·
        refine ⟨29561764624185217522528687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39415686165580290030038249 29561764624185217522528687)
        ·
          refine ⟨44342646936277826283793031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29561764624185217522528687 44342646936277826283793031)
          ·
            refine ⟨66513970404416739425689547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44342646936277826283793031 66513970404416739425689547)
            ·
              refine ⟨99770955606625109138534321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66513970404416739425689547 99770955606625109138534321)
              ·
                refine ⟨74828216704968831853900741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99770955606625109138534321 74828216704968831853900741)
                ·
                  refine ⟨14030290632181655972606389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74828216704968831853900741 14030290632181655972606389)
                  ·
                    refine ⟨1315339746767030247431849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14030290632181655972606389 1315339746767030247431849)
                    ·
                      rfl

theorem cell23_7684845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_7684845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684845 prefixEnd_7684845 := by exact prefixLift 7684845
  have htrace : WordTrace (prefixWord ++ tailWord_7684845) baseStart_7684845 baseEnd_7684845 := by
    simpa [prefixWord, tailWord_7684845, baseEnd_7684845] using wordTrace_append hprefix tailTrace_7684845
  have hstable : (prefixWord ++ tailWord_7684845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684845).length < 2 ^ (prefixWord ++ tailWord_7684845).sum := by decide
  have hdescent : baseEnd_7684845 < baseStart_7684845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684858 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_7684858 : Nat := 118140960795 + 7684858 * 2 ^ 59
def prefixEnd_7684858 : Nat := 4983230072969 + 3 ^ 40 * 7684858 * 2
def baseEnd_7684858 : Nat := 1315341971849866397144329

theorem tailTrace_7684858 : CollatzResearch.WordTrace tailWord_7684858 prefixEnd_7684858 1315341971849866397144329 := by
  unfold tailWord_7684858
  simp only [CollatzResearch.WordTrace]
  refine ⟨70072449498269852525123807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186859865328719606733663485 70072449498269852525123807)
  ·
    refine ⟨105108674247404778787685711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70072449498269852525123807 105108674247404778787685711)
    ·
      refine ⟨157663011371107168181528567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105108674247404778787685711 157663011371107168181528567)
      ·
        refine ⟨236494517056660752272292851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157663011371107168181528567 236494517056660752272292851)
        ·
          refine ⟨354741775584991128408439277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236494517056660752272292851 354741775584991128408439277)
          ·
            refine ⟨133028165844371673153164729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354741775584991128408439277 133028165844371673153164729)
            ·
              refine ⟨99771124383278754864873547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133028165844371673153164729 99771124383278754864873547)
              ·
                refine ⟨149656686574918132297310321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99771124383278754864873547 149656686574918132297310321)
                ·
                  refine ⟨112242514931188599222982741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149656686574918132297310321 112242514931188599222982741)
                  ·
                    refine ⟨1315341971849866397144329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112242514931188599222982741 1315341971849866397144329)
                    ·
                      rfl

theorem cell23_7684858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_7684858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684858 prefixEnd_7684858 := by exact prefixLift 7684858
  have htrace : WordTrace (prefixWord ++ tailWord_7684858) baseStart_7684858 baseEnd_7684858 := by
    simpa [prefixWord, tailWord_7684858, baseEnd_7684858] using wordTrace_append hprefix tailTrace_7684858
  have hstable : (prefixWord ++ tailWord_7684858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684858).length < 2 ^ (prefixWord ++ tailWord_7684858).sum := by decide
  have hdescent : baseEnd_7684858 < baseStart_7684858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684862 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7684862 : Nat := 118140960795 + 7684862 * 2 ^ 59
def prefixEnd_7684862 : Nat := 4983230072969 + 3 ^ 40 * 7684862 * 2
def baseEnd_7684862 : Nat := 1315342656490739058594323

theorem tailTrace_7684862 : CollatzResearch.WordTrace tailWord_7684862 prefixEnd_7684862 1315342656490739058594323 := by
  unfold tailWord_7684862
  simp only [CollatzResearch.WordTrace]
  refine ⟨35036242985633114847955105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186859962590043279189093893 35036242985633114847955105)
  ·
    refine ⟨26277182239224836135966329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35036242985633114847955105 26277182239224836135966329)
    ·
      refine ⟨19707886679418627101974747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26277182239224836135966329 19707886679418627101974747)
      ·
        refine ⟨29561830019127940652962121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19707886679418627101974747 29561830019127940652962121)
        ·
          refine ⟨22171372514345955489721591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29561830019127940652962121 22171372514345955489721591)
          ·
            refine ⟨33257058771518933234582387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22171372514345955489721591 33257058771518933234582387)
            ·
              refine ⟨49885588157278399851873581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33257058771518933234582387 49885588157278399851873581)
              ·
                refine ⟨18707095558979399944452593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49885588157278399851873581 18707095558979399944452593)
                ·
                  refine ⟨14030321669234549958339445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18707095558979399944452593 14030321669234549958339445)
                  ·
                    refine ⟨1315342656490739058594323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14030321669234549958339445 1315342656490739058594323)
                    ·
                      rfl

theorem cell23_7684862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7684862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684862 prefixEnd_7684862 := by exact prefixLift 7684862
  have htrace : WordTrace (prefixWord ++ tailWord_7684862) baseStart_7684862 baseEnd_7684862 := by
    simpa [prefixWord, tailWord_7684862, baseEnd_7684862] using wordTrace_append hprefix tailTrace_7684862
  have hstable : (prefixWord ++ tailWord_7684862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684862).length < 2 ^ (prefixWord ++ tailWord_7684862).sum := by decide
  have hdescent : baseEnd_7684862 < baseStart_7684862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684916 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_7684916 : Nat := 118140960795 + 7684916 * 2 ^ 59
def prefixEnd_7684916 : Nat := 4983230072969 + 3 ^ 40 * 7684916 * 2
def baseEnd_7684916 : Nat := 3946055697427559964507721

theorem tailTrace_7684916 : CollatzResearch.WordTrace tailWord_7684916 prefixEnd_7684916 3946055697427559964507721 := by
  unfold tailWord_7684916
  simp only [CollatzResearch.WordTrace]
  refine ⟨140145956713434643003053301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186861275617912857337404401 140145956713434643003053301)
  ·
    refine ⟨13138683441884497781536247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140145956713434643003053301 13138683441884497781536247)
    ·
      refine ⟨19708025162826746672304371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13138683441884497781536247 19708025162826746672304371)
      ·
        refine ⟨29562037744240120008456557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19708025162826746672304371 29562037744240120008456557)
        ·
          refine ⟨11085764154090045003171209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29562037744240120008456557 11085764154090045003171209)
          ·
            refine ⟨8314323115567533752378407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11085764154090045003171209 8314323115567533752378407)
            ·
              refine ⟨12471484673351300628567611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8314323115567533752378407 12471484673351300628567611)
              ·
                refine ⟨18707227010026950942851417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12471484673351300628567611 18707227010026950942851417)
                ·
                  refine ⟨14030420257520213207138563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18707227010026950942851417 14030420257520213207138563)
                  ·
                    refine ⟨21045630386280319810707845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14030420257520213207138563 21045630386280319810707845)
                    ·
                      refine ⟨3946055697427559964507721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21045630386280319810707845 3946055697427559964507721)
                      ·
                        rfl

theorem cell23_7684916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_7684916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684916 prefixEnd_7684916 := by exact prefixLift 7684916
  have htrace : WordTrace (prefixWord ++ tailWord_7684916) baseStart_7684916 baseEnd_7684916 := by
    simpa [prefixWord, tailWord_7684916, baseEnd_7684916] using wordTrace_append hprefix tailTrace_7684916
  have hstable : (prefixWord ++ tailWord_7684916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684916).length < 2 ^ (prefixWord ++ tailWord_7684916).sum := by decide
  have hdescent : baseEnd_7684916 < baseStart_7684916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684949 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_7684949 : Nat := 118140960795 + 7684949 * 2 ^ 59
def prefixEnd_7684949 : Nat := 4983230072969 + 3 ^ 40 * 7684949 * 2
def baseEnd_7684949 : Nat := 3946072642289158335395069

theorem tailTrace_7684949 : CollatzResearch.WordTrace tailWord_7684949 prefixEnd_7684949 3946072642289158335395069 := by
  unfold tailWord_7684949
  simp only [CollatzResearch.WordTrace]
  refine ⟨280293117035749732642057901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186862078023833155094705267 280293117035749732642057901)
  ·
    refine ⟨105109918888406149740771713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280293117035749732642057901 105109918888406149740771713)
    ·
      refine ⟨78832439166304612305578785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105109918888406149740771713 78832439166304612305578785)
      ·
        refine ⟨59124329374728459229184089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78832439166304612305578785 59124329374728459229184089)
        ·
          refine ⟨44343247031046344421888067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59124329374728459229184089 44343247031046344421888067)
          ·
            refine ⟨66514870546569516632832101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44343247031046344421888067 66514870546569516632832101)
            ·
              refine ⟨12471538227481784368656019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66514870546569516632832101 12471538227481784368656019)
              ·
                refine ⟨18707307341222676552984029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12471538227481784368656019 18707307341222676552984029)
                ·
                  refine ⟨7015240252958503707369011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18707307341222676552984029 7015240252958503707369011)
                  ·
                    refine ⟨10522860379437755561053517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7015240252958503707369011 10522860379437755561053517)
                    ·
                      refine ⟨3946072642289158335395069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10522860379437755561053517 3946072642289158335395069)
                      ·
                        rfl

theorem cell23_7684949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_7684949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684949 prefixEnd_7684949 := by exact prefixLift 7684949
  have htrace : WordTrace (prefixWord ++ tailWord_7684949) baseStart_7684949 baseEnd_7684949 := by
    simpa [prefixWord, tailWord_7684949, baseEnd_7684949] using wordTrace_append hprefix tailTrace_7684949
  have hstable : (prefixWord ++ tailWord_7684949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684949).length < 2 ^ (prefixWord ++ tailWord_7684949).sum := by decide
  have hdescent : baseEnd_7684949 < baseStart_7684949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684972 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 2, 6, 2]
def baseStart_7684972 : Nat := 118140960795 + 7684972 * 2 ^ 59
def prefixEnd_7684972 : Nat := 4983230072969 + 3 ^ 40 * 7684972 * 2
def baseEnd_7684972 : Nat := 3946084452344211745407463

theorem tailTrace_7684972 : CollatzResearch.WordTrace tailWord_7684972 prefixEnd_7684972 3946084452344211745407463 := by
  unfold tailWord_7684972
  simp only [CollatzResearch.WordTrace]
  refine ⟨140146977957333203785072585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186862637276444271713430113 140146977957333203785072585)
  ·
    refine ⟨105110233467999902838804439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140146977957333203785072585 105110233467999902838804439)
    ·
      refine ⟨157665350201999854258206659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105110233467999902838804439 157665350201999854258206659)
      ·
        refine ⟨236498025302999781387309989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157665350201999854258206659 236498025302999781387309989)
        ·
          refine ⟨44343379744312459010120623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236498025302999781387309989 44343379744312459010120623)
          ·
            refine ⟨66515069616468688515180935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44343379744312459010120623 66515069616468688515180935)
            ·
              refine ⟨99772604424703032772771403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66515069616468688515180935 99772604424703032772771403)
              ·
                refine ⟨149658906637054549159157105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99772604424703032772771403 149658906637054549159157105)
                ·
                  refine ⟨112244179977790911869367829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149658906637054549159157105 112244179977790911869367829)
                  ·
                    refine ⟨5261445936458948993876617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112244179977790911869367829 5261445936458948993876617)
                    ·
                      refine ⟨3946084452344211745407463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5261445936458948993876617 3946084452344211745407463)
                      ·
                        rfl

theorem cell23_7684972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 6, 2].length) (baseStart_7684972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684972 prefixEnd_7684972 := by exact prefixLift 7684972
  have htrace : WordTrace (prefixWord ++ tailWord_7684972) baseStart_7684972 baseEnd_7684972 := by
    simpa [prefixWord, tailWord_7684972, baseEnd_7684972] using wordTrace_append hprefix tailTrace_7684972
  have hstable : (prefixWord ++ tailWord_7684972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684972).length < 2 ^ (prefixWord ++ tailWord_7684972).sum := by decide
  have hdescent : baseEnd_7684972 < baseStart_7684972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684975 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 3]
def baseStart_7684975 : Nat := 118140960795 + 7684975 * 2 ^ 59
def prefixEnd_7684975 : Nat := 4983230072969 + 3 ^ 40 * 7684975 * 2
def baseEnd_7684975 : Nat := 3946085992786175233669949

theorem tailTrace_7684975 : CollatzResearch.WordTrace tailWord_7684975 prefixEnd_7684975 3946085992786175233669949 := by
  unfold tailWord_7684975
  simp only [CollatzResearch.WordTrace]
  refine ⟨280294065333655539082504379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186862710222437026055002919 280294065333655539082504379)
  ·
    refine ⟨420441098000483308623756569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280294065333655539082504379 420441098000483308623756569)
    ·
      refine ⟨315330823500362481467817427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420441098000483308623756569 315330823500362481467817427)
      ·
        refine ⟨472996235250543722201726141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315330823500362481467817427 472996235250543722201726141)
        ·
          refine ⟨177373588218953895825647303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472996235250543722201726141 177373588218953895825647303)
          ·
            refine ⟨266060382328430843738470955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177373588218953895825647303 266060382328430843738470955)
            ·
              refine ⟨399090573492646265607706433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266060382328430843738470955 399090573492646265607706433)
              ·
                refine ⟨299317930119484699205779825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399090573492646265607706433 299317930119484699205779825)
                ·
                  refine ⟨224488447589613524404334869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299317930119484699205779825 224488447589613524404334869)
                  ·
                    refine ⟨10522895980763133956453197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 224488447589613524404334869 10522895980763133956453197)
                    ·
                      refine ⟨3946085992786175233669949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10522895980763133956453197 3946085992786175233669949)
                      ·
                        rfl

theorem cell23_7684975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 3].length) (baseStart_7684975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684975 prefixEnd_7684975 := by exact prefixLift 7684975
  have htrace : WordTrace (prefixWord ++ tailWord_7684975) baseStart_7684975 baseEnd_7684975 := by
    simpa [prefixWord, tailWord_7684975, baseEnd_7684975] using wordTrace_append hprefix tailTrace_7684975
  have hstable : (prefixWord ++ tailWord_7684975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684975).length < 2 ^ (prefixWord ++ tailWord_7684975).sum := by decide
  have hdescent : baseEnd_7684975 < baseStart_7684975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7684989 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 5, 2, 2]
def baseStart_7684989 : Nat := 118140960795 + 7684989 * 2 ^ 59
def prefixEnd_7684989 : Nat := 4983230072969 + 3 ^ 40 * 7684989 * 2
def baseEnd_7684989 : Nat := 3946093181515338178894885

theorem tailTrace_7684989 : CollatzResearch.WordTrace tailWord_7684989 prefixEnd_7684989 3946093181515338178894885 := by
  unfold tailWord_7684989
  simp only [CollatzResearch.WordTrace]
  refine ⟨280294575955604819473514021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186863050637069879649009347 280294575955604819473514021)
  ·
    refine ⟨52555232991675903651283879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280294575955604819473514021 52555232991675903651283879)
    ·
      refine ⟨78832849487513855476925819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52555232991675903651283879 78832849487513855476925819)
      ·
        refine ⟨118249274231270783215388729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78832849487513855476925819 118249274231270783215388729)
        ·
          refine ⟨88686955673453087411541547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118249274231270783215388729 88686955673453087411541547)
          ·
            refine ⟨133030433510179631117312321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88686955673453087411541547 133030433510179631117312321)
            ·
              refine ⟨99772825132634723337984241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133030433510179631117312321 99772825132634723337984241)
              ·
                refine ⟨74829618849476042503488181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99772825132634723337984241 74829618849476042503488181)
                ·
                  refine ⟨7015276767138378984702017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74829618849476042503488181 7015276767138378984702017)
                  ·
                    refine ⟨5261457575353784238526513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7015276767138378984702017 5261457575353784238526513)
                    ·
                      refine ⟨3946093181515338178894885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5261457575353784238526513 3946093181515338178894885)
                      ·
                        rfl

theorem cell23_7684989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_7684989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7684989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7684989 prefixEnd_7684989 := by exact prefixLift 7684989
  have htrace : WordTrace (prefixWord ++ tailWord_7684989) baseStart_7684989 baseEnd_7684989 := by
    simpa [prefixWord, tailWord_7684989, baseEnd_7684989] using wordTrace_append hprefix tailTrace_7684989
  have hstable : (prefixWord ++ tailWord_7684989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7684989).length < 2 ^ (prefixWord ++ tailWord_7684989).sum := by decide
  have hdescent : baseEnd_7684989 < baseStart_7684989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7684989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685002 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_7685002 : Nat := 118140960795 + 7685002 * 2 ^ 59
def prefixEnd_7685002 : Nat := 4983230072969 + 3 ^ 40 * 7685002 * 2
def baseEnd_7685002 : Nat := 3946099856763846628032325

theorem tailTrace_7685002 : CollatzResearch.WordTrace tailWord_7685002 prefixEnd_7685002 3946099856763846628032325 := by
  unfold tailWord_7685002
  simp only [CollatzResearch.WordTrace]
  refine ⟨70073762526139430673434315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186863366736371815129158173 70073762526139430673434315)
  ·
    refine ⟨105110643789209146010151473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70073762526139430673434315 105110643789209146010151473)
    ·
      refine ⟨78832982841906859507613605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105110643789209146010151473 78832982841906859507613605)
      ·
        refine ⟨14781184282857536157677551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78832982841906859507613605 14781184282857536157677551)
        ·
          refine ⟨22171776424286304236516327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14781184282857536157677551 22171776424286304236516327)
          ·
            refine ⟨33257664636429456354774491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22171776424286304236516327 33257664636429456354774491)
            ·
              refine ⟨49886496954644184532161737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33257664636429456354774491 49886496954644184532161737)
              ·
                refine ⟨37414872715983138399121303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49886496954644184532161737 37414872715983138399121303)
                ·
                  refine ⟨56122309073974707598681955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37414872715983138399121303 56122309073974707598681955)
                  ·
                    refine ⟨84183463610962061398022933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56122309073974707598681955 84183463610962061398022933)
                    ·
                      refine ⟨3946099856763846628032325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84183463610962061398022933 3946099856763846628032325)
                      ·
                        rfl

theorem cell23_7685002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_7685002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685002 prefixEnd_7685002 := by exact prefixLift 7685002
  have htrace : WordTrace (prefixWord ++ tailWord_7685002) baseStart_7685002 baseEnd_7685002 := by
    simpa [prefixWord, tailWord_7685002, baseEnd_7685002] using wordTrace_append hprefix tailTrace_7685002
  have hstable : (prefixWord ++ tailWord_7685002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685002).length < 2 ^ (prefixWord ++ tailWord_7685002).sum := by decide
  have hdescent : baseEnd_7685002 < baseStart_7685002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685012 : List Nat := [2, 4, 2, 1, 1, 1, 4, 8]
def baseStart_7685012 : Nat := 118140960795 + 7685012 * 2 ^ 59
def prefixEnd_7685012 : Nat := 4983230072969 + 3 ^ 40 * 7685012 * 2
def baseEnd_7685012 : Nat := 146152036724829318107677

theorem tailTrace_7685012 : CollatzResearch.WordTrace tailWord_7685012 prefixEnd_7685012 146152036724829318107677 := by
  unfold tailWord_7685012
  simp only [CollatzResearch.WordTrace]
  refine ⟨140147707417260747200800645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186863609889680996267734193 140147707417260747200800645)
  ·
    refine ⟨26277695140736390100150121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140147707417260747200800645 26277695140736390100150121)
    ·
      refine ⟨19708271355552292575112591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26277695140736390100150121 19708271355552292575112591)
      ·
        refine ⟨29562407033328438862668887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19708271355552292575112591 29562407033328438862668887)
        ·
          refine ⟨44343610549992658294003331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29562407033328438862668887 44343610549992658294003331)
          ·
            refine ⟨66515415824988987441004997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44343610549992658294003331 66515415824988987441004997)
            ·
              refine ⟨12471640467185435145188437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66515415824988987441004997 12471640467185435145188437)
              ·
                refine ⟨146152036724829318107677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12471640467185435145188437 146152036724829318107677)
                ·
                  rfl

theorem cell23_7685012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 8].length) (baseStart_7685012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685012 prefixEnd_7685012 := by exact prefixLift 7685012
  have htrace : WordTrace (prefixWord ++ tailWord_7685012) baseStart_7685012 baseEnd_7685012 := by
    simpa [prefixWord, tailWord_7685012, baseEnd_7685012] using wordTrace_append hprefix tailTrace_7685012
  have hstable : (prefixWord ++ tailWord_7685012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685012).length < 2 ^ (prefixWord ++ tailWord_7685012).sum := by decide
  have hdescent : baseEnd_7685012 < baseStart_7685012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685015 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_7685015 : Nat := 118140960795 + 7685015 * 2 ^ 59
def prefixEnd_7685015 : Nat := 4983230072969 + 3 ^ 40 * 7685015 * 2
def baseEnd_7685015 : Nat := 3946106532012355077169765

theorem tailTrace_7685015 : CollatzResearch.WordTrace tailWord_7685015 prefixEnd_7685015 3946106532012355077169765 := by
  unfold tailWord_7685015
  simp only [CollatzResearch.WordTrace]
  refine ⟨280295524253510625913960499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186863682835673750609306999 280295524253510625913960499)
  ·
    refine ⟨420443286380265938870940749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280295524253510625913960499 420443286380265938870940749)
    ·
      refine ⟨157666232392599727076602781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420443286380265938870940749 157666232392599727076602781)
      ·
        refine ⟨59124837147224897653726043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157666232392599727076602781 59124837147224897653726043)
        ·
          refine ⟨88687255720837346480589065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59124837147224897653726043 88687255720837346480589065)
          ·
            refine ⟨66515441790628009860441799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88687255720837346480589065 66515441790628009860441799)
            ·
              refine ⟨99773162685942014790662699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66515441790628009860441799 99773162685942014790662699)
              ·
                refine ⟨149659744028913022185994049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99773162685942014790662699 149659744028913022185994049)
                ·
                  refine ⟨112244808021684766639495537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149659744028913022185994049 112244808021684766639495537)
                  ·
                    refine ⟨84183606016263574979621653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112244808021684766639495537 84183606016263574979621653)
                    ·
                      refine ⟨3946106532012355077169765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84183606016263574979621653 3946106532012355077169765)
                      ·
                        rfl

theorem cell23_7685015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_7685015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685015 prefixEnd_7685015 := by exact prefixLift 7685015
  have htrace : WordTrace (prefixWord ++ tailWord_7685015) baseStart_7685015 baseEnd_7685015 := by
    simpa [prefixWord, tailWord_7685015, baseEnd_7685015] using wordTrace_append hprefix tailTrace_7685015
  have hstable : (prefixWord ++ tailWord_7685015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685015).length < 2 ^ (prefixWord ++ tailWord_7685015).sum := by decide
  have hdescent : baseEnd_7685015 < baseStart_7685015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685026 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_7685026 : Nat := 118140960795 + 7685026 * 2 ^ 59
def prefixEnd_7685026 : Nat := 4983230072969 + 3 ^ 40 * 7685026 * 2
def baseEnd_7685026 : Nat := 3946112180299554534132215

theorem tailTrace_7685026 : CollatzResearch.WordTrace tailWord_7685026 prefixEnd_7685026 3946112180299554534132215 := by
  unfold tailWord_7685026
  simp only [CollatzResearch.WordTrace]
  refine ⟨70073981364117693698152733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186863950304313849861740621 70073981364117693698152733)
  ·
    refine ⟨26277743011544135136807275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70073981364117693698152733 26277743011544135136807275)
    ·
      refine ⟨39416614517316202705210913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26277743011544135136807275 39416614517316202705210913)
      ·
        refine ⟨29562460887987152028908185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39416614517316202705210913 29562460887987152028908185)
        ·
          refine ⟨22171845665990364021681139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29562460887987152028908185 22171845665990364021681139)
          ·
            refine ⟨33257768498985546032521709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22171845665990364021681139 33257768498985546032521709)
            ·
              refine ⟨12471663187119579762195641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33257768498985546032521709 12471663187119579762195641)
              ·
                refine ⟨9353747390339684821646731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12471663187119579762195641 9353747390339684821646731)
                ·
                  refine ⟨14030621085509527232470097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9353747390339684821646731 14030621085509527232470097)
                  ·
                    refine ⟨10522965814132145424352573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14030621085509527232470097 10522965814132145424352573)
                    ·
                      refine ⟨3946112180299554534132215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10522965814132145424352573 3946112180299554534132215)
                      ·
                        rfl

theorem cell23_7685026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_7685026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685026 prefixEnd_7685026 := by exact prefixLift 7685026
  have htrace : WordTrace (prefixWord ++ tailWord_7685026) baseStart_7685026 baseEnd_7685026 := by
    simpa [prefixWord, tailWord_7685026, baseEnd_7685026] using wordTrace_append hprefix tailTrace_7685026
  have hstable : (prefixWord ++ tailWord_7685026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685026).length < 2 ^ (prefixWord ++ tailWord_7685026).sum := by decide
  have hdescent : baseEnd_7685026 < baseStart_7685026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685046 : List Nat := [5, 1, 4, 1, 1, 11]
def baseStart_7685046 : Nat := 118140960795 + 7685046 * 2 ^ 59
def prefixEnd_7685046 : Nat := 4983230072969 + 3 ^ 40 * 7685046 * 2
def baseEnd_7685046 : Nat := 16239187036677549201161

theorem tailTrace_7685046 : CollatzResearch.WordTrace tailWord_7685046 prefixEnd_7685046 16239187036677549201161 := by
  unfold tailWord_7685046
  simp only [CollatzResearch.WordTrace]
  refine ⟨17518540932274894888021187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186864436610932212138892661 17518540932274894888021187)
  ·
    refine ⟨26277811398412342332031781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17518540932274894888021187 26277811398412342332031781)
    ·
      refine ⟨4927089637202314187255959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26277811398412342332031781 4927089637202314187255959)
      ·
        refine ⟨7390634455803471280883939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927089637202314187255959 7390634455803471280883939)
        ·
          refine ⟨11085951683705206921325909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7390634455803471280883939 11085951683705206921325909)
          ·
            refine ⟨16239187036677549201161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11085951683705206921325909 16239187036677549201161)
            ·
              rfl

theorem cell23_7685046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 11].length) (baseStart_7685046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685046 prefixEnd_7685046 := by exact prefixLift 7685046
  have htrace : WordTrace (prefixWord ++ tailWord_7685046) baseStart_7685046 baseEnd_7685046 := by
    simpa [prefixWord, tailWord_7685046, baseEnd_7685046] using wordTrace_append hprefix tailTrace_7685046
  have hstable : (prefixWord ++ tailWord_7685046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685046).length < 2 ^ (prefixWord ++ tailWord_7685046).sum := by decide
  have hdescent : baseEnd_7685046 < baseStart_7685046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685056 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 2, 1, 3]
def baseStart_7685056 : Nat := 118140960795 + 7685056 * 2 ^ 59
def prefixEnd_7685056 : Nat := 4983230072969 + 3 ^ 40 * 7685056 * 2
def baseEnd_7685056 : Nat := 3946127584719189416757077

theorem tailTrace_7685056 : CollatzResearch.WordTrace tailWord_7685056 prefixEnd_7685056 3946127584719189416757077 := by
  unfold tailWord_7685056
  simp only [CollatzResearch.WordTrace]
  refine ⟨140148509823181044958101511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186864679764241393277468681 140148509823181044958101511)
  ·
    refine ⟨210222764734771567437152267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140148509823181044958101511 210222764734771567437152267)
    ·
      refine ⟨315334147102157351155728401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210222764734771567437152267 315334147102157351155728401)
      ·
        refine ⟨236500610326618013366796301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315334147102157351155728401 236500610326618013366796301)
        ·
          refine ⟨88687728872481755012548613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236500610326618013366796301 88687728872481755012548613)
          ·
            refine ⟨16628949163590329064852865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88687728872481755012548613 16628949163590329064852865)
            ·
              refine ⟨12471711872692746798639649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16628949163590329064852865 12471711872692746798639649)
              ·
                refine ⟨9353783904519560098979737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12471711872692746798639649 9353783904519560098979737)
                ·
                  refine ⟨7015337928389670074234803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9353783904519560098979737 7015337928389670074234803)
                  ·
                    refine ⟨10523006892584505111352205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7015337928389670074234803 10523006892584505111352205)
                    ·
                      refine ⟨3946127584719189416757077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10523006892584505111352205 3946127584719189416757077)
                      ·
                        rfl

theorem cell23_7685056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_7685056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685056 prefixEnd_7685056 := by exact prefixLift 7685056
  have htrace : WordTrace (prefixWord ++ tailWord_7685056) baseStart_7685056 baseEnd_7685056 := by
    simpa [prefixWord, tailWord_7685056, baseEnd_7685056] using wordTrace_append hprefix tailTrace_7685056
  have hstable : (prefixWord ++ tailWord_7685056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685056).length < 2 ^ (prefixWord ++ tailWord_7685056).sum := by decide
  have hdescent : baseEnd_7685056 < baseStart_7685056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685130 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2]
def baseStart_7685130 : Nat := 118140960795 + 7685130 * 2 ^ 59
def prefixEnd_7685130 : Nat := 4983230072969 + 3 ^ 40 * 7685130 * 2
def baseEnd_7685130 : Nat := 3946165582287622127231737

theorem tailTrace_7685130 : CollatzResearch.WordTrace tailWord_7685130 prefixEnd_7685130 3946165582287622127231737 := by
  unfold tailWord_7685130
  simp only [CollatzResearch.WordTrace]
  refine ⟨70074929662023500138599211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186866479098729333702931229 70074929662023500138599211)
  ·
    refine ⟨105112394493035250207898817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70074929662023500138599211 105112394493035250207898817)
    ·
      refine ⟨78834295869776437655924113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105112394493035250207898817 78834295869776437655924113)
      ·
        refine ⟨59125721902332328241943085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78834295869776437655924113 59125721902332328241943085)
        ·
          refine ⟨22172145713374623090728657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59125721902332328241943085 22172145713374623090728657)
          ·
            refine ⟨16629109285030967318046493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22172145713374623090728657 16629109285030967318046493)
            ·
              refine ⟨6235915981886612744267435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16629109285030967318046493 6235915981886612744267435)
              ·
                refine ⟨9353873972829919116401153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6235915981886612744267435 9353873972829919116401153)
                ·
                  refine ⟨7015405479622439337300865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9353873972829919116401153 7015405479622439337300865)
                  ·
                    refine ⟨5261554109716829502975649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7015405479622439337300865 5261554109716829502975649)
                    ·
                      refine ⟨3946165582287622127231737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5261554109716829502975649 3946165582287622127231737)
                      ·
                        rfl

theorem cell23_7685130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_7685130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685130 prefixEnd_7685130 := by exact prefixLift 7685130
  have htrace : WordTrace (prefixWord ++ tailWord_7685130) baseStart_7685130 baseEnd_7685130 := by
    simpa [prefixWord, tailWord_7685130, baseEnd_7685130] using wordTrace_append hprefix tailTrace_7685130
  have hstable : (prefixWord ++ tailWord_7685130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685130).length < 2 ^ (prefixWord ++ tailWord_7685130).sum := by decide
  have hdescent : baseEnd_7685130 < baseStart_7685130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685132 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_7685132 : Nat := 118140960795 + 7685132 * 2 ^ 59
def prefixEnd_7685132 : Nat := 4983230072969 + 3 ^ 40 * 7685132 * 2
def baseEnd_7685132 : Nat := 1315388869749643706468909

theorem tailTrace_7685132 : CollatzResearch.WordTrace tailWord_7685132 prefixEnd_7685132 1315388869749643706468909 := by
  unfold tailWord_7685132
  simp only [CollatzResearch.WordTrace]
  refine ⟨140149895797043377447984825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186866527729391169930646433 140149895797043377447984825)
  ·
    refine ⟨105112421847782533085988619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140149895797043377447984825 105112421847782533085988619)
    ·
      refine ⟨157668632771673799628982929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105112421847782533085988619 157668632771673799628982929)
      ·
        refine ⟨118251474578755349721737197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157668632771673799628982929 118251474578755349721737197)
        ·
          refine ⟨44344302967033256145651449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118251474578755349721737197 44344302967033256145651449)
          ·
            refine ⟨33258227225274942109238587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44344302967033256145651449 33258227225274942109238587)
            ·
              refine ⟨49887340837912413163857881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33258227225274942109238587 49887340837912413163857881)
              ·
                refine ⟨37415505628434309872893411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49887340837912413163857881 37415505628434309872893411)
                ·
                  refine ⟨56123258442651464809340117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37415505628434309872893411 56123258442651464809340117)
                  ·
                    refine ⟨1315388869749643706468909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56123258442651464809340117 1315388869749643706468909)
                    ·
                      rfl

theorem cell23_7685132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_7685132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685132 prefixEnd_7685132 := by exact prefixLift 7685132
  have htrace : WordTrace (prefixWord ++ tailWord_7685132) baseStart_7685132 baseEnd_7685132 := by
    simpa [prefixWord, tailWord_7685132, baseEnd_7685132] using wordTrace_append hprefix tailTrace_7685132
  have hstable : (prefixWord ++ tailWord_7685132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685132).length < 2 ^ (prefixWord ++ tailWord_7685132).sum := by decide
  have hdescent : baseEnd_7685132 < baseStart_7685132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685169 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_7685169 : Nat := 118140960795 + 7685169 * 2 ^ 59
def prefixEnd_7685169 : Nat := 4983230072969 + 3 ^ 40 * 7685169 * 2
def baseEnd_7685169 : Nat := 3946185608033147474644057

theorem tailTrace_7685169 : CollatzResearch.WordTrace tailWord_7685169 prefixEnd_7685169 3946185608033147474644057 := by
  unfold tailWord_7685169
  simp only [CollatzResearch.WordTrace]
  refine ⟨280301141094952710215066561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186867427396635140143377707 280301141094952710215066561)
  ·
    refine ⟨210225855821214532661299921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280301141094952710215066561 210225855821214532661299921)
    ·
      refine ⟨157669391865910899495974941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210225855821214532661299921 157669391865910899495974941)
      ·
        refine ⟨59126021949716587310990603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157669391865910899495974941 59126021949716587310990603)
        ·
          refine ⟨88689032924574880966485905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59126021949716587310990603 88689032924574880966485905)
          ·
            refine ⟨66516774693431160724864429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88689032924574880966485905 66516774693431160724864429)
            ·
              refine ⟨24943790510036685271824161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66516774693431160724864429 24943790510036685271824161)
              ·
                refine ⟨18707842882527513953868121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24943790510036685271824161 18707842882527513953868121)
                ·
                  refine ⟨14030882161895635465401091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18707842882527513953868121 14030882161895635465401091)
                  ·
                    refine ⟨21046323242843453198101637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14030882161895635465401091 21046323242843453198101637)
                    ·
                      refine ⟨3946185608033147474644057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21046323242843453198101637 3946185608033147474644057)
                      ·
                        rfl

theorem cell23_7685169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_7685169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685169 prefixEnd_7685169 := by exact prefixLift 7685169
  have htrace : WordTrace (prefixWord ++ tailWord_7685169) baseStart_7685169 baseEnd_7685169 := by
    simpa [prefixWord, tailWord_7685169, baseEnd_7685169] using wordTrace_append hprefix tailTrace_7685169
  have hstable : (prefixWord ++ tailWord_7685169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685169).length < 2 ^ (prefixWord ++ tailWord_7685169).sum := by decide
  have hdescent : baseEnd_7685169 < baseStart_7685169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685226 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 6]
def baseStart_7685226 : Nat := 118140960795 + 7685226 * 2 ^ 59
def prefixEnd_7685226 : Nat := 4983230072969 + 3 ^ 40 * 7685226 * 2
def baseEnd_7685226 : Nat := 438468319603383750181255

theorem tailTrace_7685226 : CollatzResearch.WordTrace tailWord_7685226 prefixEnd_7685226 438468319603383750181255 := by
  unfold tailWord_7685226
  simp only [CollatzResearch.WordTrace]
  refine ⟨70075805013936552237472883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186868813370497472633261021 70075805013936552237472883)
  ·
    refine ⟨105113707520904828356209325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70075805013936552237472883 105113707520904828356209325)
    ·
      refine ⟨39417640320339310633578497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105113707520904828356209325 39417640320339310633578497)
      ·
        refine ⟨29563230240254482975183873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39417640320339310633578497 29563230240254482975183873)
        ·
          refine ⟨22172422680190862231387905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29563230240254482975183873 22172422680190862231387905)
          ·
            refine ⟨16629317010143146673540929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22172422680190862231387905 16629317010143146673540929)
            ·
              refine ⟨12471987757607360005155697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16629317010143146673540929 12471987757607360005155697)
              ·
                refine ⟨9353990818205520003866773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12471987757607360005155697 9353990818205520003866773)
                ·
                  refine ⟨438468319603383750181255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9353990818205520003866773 438468319603383750181255)
                  ·
                    rfl

theorem cell23_7685226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_7685226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685226 prefixEnd_7685226 := by exact prefixLift 7685226
  have htrace : WordTrace (prefixWord ++ tailWord_7685226) baseStart_7685226 baseEnd_7685226 := by
    simpa [prefixWord, tailWord_7685226, baseEnd_7685226] using wordTrace_append hprefix tailTrace_7685226
  have hstable : (prefixWord ++ tailWord_7685226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685226).length < 2 ^ (prefixWord ++ tailWord_7685226).sum := by decide
  have hdescent : baseEnd_7685226 < baseStart_7685226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685230 : List Nat := [4, 1, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_7685230 : Nat := 118140960795 + 7685230 * 2 ^ 59
def prefixEnd_7685230 : Nat := 4983230072969 + 3 ^ 40 * 7685230 * 2
def baseEnd_7685230 : Nat := 1315405643451023911993759

theorem tailTrace_7685230 : CollatzResearch.WordTrace tailWord_7685230 prefixEnd_7685230 1315405643451023911993759 := by
  unfold tailWord_7685230
  simp only [CollatzResearch.WordTrace]
  refine ⟨35037920743466464704129643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186868910631821145088691429 35037920743466464704129643)
  ·
    refine ⟨52556881115199697056194465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35037920743466464704129643 52556881115199697056194465)
    ·
      refine ⟨39417660836399772792145849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52556881115199697056194465 39417660836399772792145849)
      ·
        refine ⟨29563245627299829594109387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39417660836399772792145849 29563245627299829594109387)
        ·
          refine ⟨44344868440949744391164081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29563245627299829594109387 44344868440949744391164081)
          ·
            refine ⟨33258651330712308293373061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44344868440949744391164081 33258651330712308293373061)
            ·
              refine ⟨6235997124508557805007449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33258651330712308293373061 6235997124508557805007449)
              ·
                refine ⟨4676997843381418353755587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6235997124508557805007449 4676997843381418353755587)
                ·
                  refine ⟨7015496765072127530633381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676997843381418353755587 7015496765072127530633381)
                  ·
                    refine ⟨1315405643451023911993759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7015496765072127530633381 1315405643451023911993759)
                    ·
                      rfl

theorem cell23_7685230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_7685230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685230 prefixEnd_7685230 := by exact prefixLift 7685230
  have htrace : WordTrace (prefixWord ++ tailWord_7685230) baseStart_7685230 baseEnd_7685230 := by
    simpa [prefixWord, tailWord_7685230, baseEnd_7685230] using wordTrace_append hprefix tailTrace_7685230
  have hstable : (prefixWord ++ tailWord_7685230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685230).length < 2 ^ (prefixWord ++ tailWord_7685230).sum := by decide
  have hdescent : baseEnd_7685230 < baseStart_7685230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685253 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 3, 1, 3]
def baseStart_7685253 : Nat := 118140960795 + 7685253 * 2 ^ 59
def prefixEnd_7685253 : Nat := 4983230072969 + 3 ^ 40 * 7685253 * 2
def baseEnd_7685253 : Nat := 3946228740408125145993671

theorem tailTrace_7685253 : CollatzResearch.WordTrace tailWord_7685253 prefixEnd_7685253 3946228740408125145993671 := by
  unfold tailWord_7685253
  simp only [CollatzResearch.WordTrace]
  refine ⟨280304204826648392561124413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186869469884432261707416275 280304204826648392561124413)
  ·
    refine ⟨105114076809993147210421655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280304204826648392561124413 105114076809993147210421655)
    ·
      refine ⟨157671115214989720815632483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105114076809993147210421655 157671115214989720815632483)
      ·
        refine ⟨236506672822484581223448725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157671115214989720815632483 236506672822484581223448725)
        ·
          refine ⟨11086250288553964744849159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 236506672822484581223448725 11086250288553964744849159)
          ·
            refine ⟨16629375432830947117273739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11086250288553964744849159 16629375432830947117273739)
            ·
              refine ⟨24944063149246420675910609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16629375432830947117273739 24944063149246420675910609)
              ·
                refine ⟨18708047361934815506932957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24944063149246420675910609 18708047361934815506932957)
                ·
                  refine ⟨7015517760725555815099859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18708047361934815506932957 7015517760725555815099859)
                  ·
                    refine ⟨10523276641088333722649789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7015517760725555815099859 10523276641088333722649789)
                    ·
                      refine ⟨3946228740408125145993671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10523276641088333722649789 3946228740408125145993671)
                      ·
                        rfl

theorem cell23_7685253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_7685253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685253 prefixEnd_7685253 := by exact prefixLift 7685253
  have htrace : WordTrace (prefixWord ++ tailWord_7685253) baseStart_7685253 baseEnd_7685253 := by
    simpa [prefixWord, tailWord_7685253, baseEnd_7685253] using wordTrace_append hprefix tailTrace_7685253
  have hstable : (prefixWord ++ tailWord_7685253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685253).length < 2 ^ (prefixWord ++ tailWord_7685253).sum := by decide
  have hdescent : baseEnd_7685253 < baseStart_7685253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685303 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 2, 4]
def baseStart_7685303 : Nat := 118140960795 + 7685303 * 2 ^ 59
def prefixEnd_7685303 : Nat := 4983230072969 + 3 ^ 40 * 7685303 * 2
def baseEnd_7685303 : Nat := 1315418138146949983456147

theorem tailTrace_7685303 : CollatzResearch.WordTrace tailWord_7685303 prefixEnd_7685303 1315418138146949983456147 := by
  unfold tailWord_7685303
  simp only [CollatzResearch.WordTrace]
  refine ⟨280306028476467251100444563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186870685650978167400296375 280306028476467251100444563)
  ·
    refine ⟨420459042714700876650666845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280306028476467251100444563 420459042714700876650666845)
    ·
      refine ⟨157672141018012828744000067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420459042714700876650666845 157672141018012828744000067)
      ·
        refine ⟨236508211527019243116000101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157672141018012828744000067 236508211527019243116000101)
        ·
          refine ⟨44345289661316108084250019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236508211527019243116000101 44345289661316108084250019)
          ·
            refine ⟨66517934491974162126375029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44345289661316108084250019 66517934491974162126375029)
            ·
              refine ⟨6236056358622577699347659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66517934491974162126375029 6236056358622577699347659)
              ·
                refine ⟨9354084537933866549021489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6236056358622577699347659 9354084537933866549021489)
                ·
                  refine ⟨7015563403450399911766117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9354084537933866549021489 7015563403450399911766117)
                  ·
                    refine ⟨1315418138146949983456147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7015563403450399911766117 1315418138146949983456147)
                    ·
                      rfl

theorem cell23_7685303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_7685303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685303 prefixEnd_7685303 := by exact prefixLift 7685303
  have htrace : WordTrace (prefixWord ++ tailWord_7685303) baseStart_7685303 baseEnd_7685303 := by
    simpa [prefixWord, tailWord_7685303, baseEnd_7685303] using wordTrace_append hprefix tailTrace_7685303
  have hstable : (prefixWord ++ tailWord_7685303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685303).length < 2 ^ (prefixWord ++ tailWord_7685303).sum := by decide
  have hdescent : baseEnd_7685303 < baseStart_7685303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685310 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_7685310 : Nat := 118140960795 + 7685310 * 2 ^ 59
def prefixEnd_7685310 : Nat := 4983230072969 + 3 ^ 40 * 7685310 * 2
def baseEnd_7685310 : Nat := 3946258008805431422980909

theorem tailTrace_7685310 : CollatzResearch.WordTrace tailWord_7685310 prefixEnd_7685310 3946258008805431422980909 := by
  unfold tailWord_7685310
  simp only [CollatzResearch.WordTrace]
  refine ⟨35038285473430236411993673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186870855858294594197299589 35038285473430236411993673)
  ·
    refine ⟨26278714105072677308995255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35038285473430236411993673 26278714105072677308995255)
    ·
      refine ⟨39418071157609015963492883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26278714105072677308995255 39418071157609015963492883)
      ·
        refine ⟨59127106736413523945239325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39418071157609015963492883 59127106736413523945239325)
        ·
          refine ⟨22172665026155071479464747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59127106736413523945239325 22172665026155071479464747)
          ·
            refine ⟨33258997539232607219197121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22172665026155071479464747 33258997539232607219197121)
            ·
              refine ⟨24944248154424455414397841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33258997539232607219197121 24944248154424455414397841)
              ·
                refine ⟨18708186115818341560798381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24944248154424455414397841 18708186115818341560798381)
                ·
                  refine ⟨7015569793431878085299393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18708186115818341560798381 7015569793431878085299393)
                  ·
                    refine ⟨5261677345073908563974545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7015569793431878085299393 5261677345073908563974545)
                    ·
                      refine ⟨3946258008805431422980909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5261677345073908563974545 3946258008805431422980909)
                      ·
                        rfl

theorem cell23_7685310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_7685310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685310 prefixEnd_7685310 := by exact prefixLift 7685310
  have htrace : WordTrace (prefixWord ++ tailWord_7685310) baseStart_7685310 baseEnd_7685310 := by
    simpa [prefixWord, tailWord_7685310, baseEnd_7685310] using wordTrace_append hprefix tailTrace_7685310
  have hstable : (prefixWord ++ tailWord_7685310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685310).length < 2 ^ (prefixWord ++ tailWord_7685310).sum := by decide
  have hdescent : baseEnd_7685310 < baseStart_7685310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685316 : List Nat := [2, 3, 3, 1, 3, 1, 1, 9]
def baseStart_7685316 : Nat := 118140960795 + 7685316 * 2 ^ 59
def prefixEnd_7685316 : Nat := 4983230072969 + 3 ^ 40 * 7685316 * 2
def baseEnd_7685316 : Nat := 146157818136642903685403

theorem tailTrace_7685316 : CollatzResearch.WordTrace tailWord_7685316 prefixEnd_7685316 146157818136642903685403 := by
  unfold tailWord_7685316
  simp only [CollatzResearch.WordTrace]
  refine ⟨140153251312710077160333901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186871001750280102880445201 140153251312710077160333901)
  ·
    refine ⟨52557469242266278935125213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140153251312710077160333901 52557469242266278935125213)
    ·
      refine ⟨19709050965849854600671955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52557469242266278935125213 19709050965849854600671955)
      ·
        refine ⟨29563576448774781901007933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19709050965849854600671955 29563576448774781901007933)
        ·
          refine ⟨11086341168290543212877975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29563576448774781901007933 11086341168290543212877975)
          ·
            refine ⟨16629511752435814819316963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11086341168290543212877975 16629511752435814819316963)
            ·
              refine ⟨24944267628653722228975445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16629511752435814819316963 24944267628653722228975445)
              ·
                refine ⟨146157818136642903685403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24944267628653722228975445 146157818136642903685403)
                ·
                  rfl

theorem cell23_7685316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 9].length) (baseStart_7685316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685316 prefixEnd_7685316 := by exact prefixLift 7685316
  have htrace : WordTrace (prefixWord ++ tailWord_7685316) baseStart_7685316 baseEnd_7685316 := by
    simpa [prefixWord, tailWord_7685316, baseEnd_7685316] using wordTrace_append hprefix tailTrace_7685316
  have hstable : (prefixWord ++ tailWord_7685316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685316).length < 2 ^ (prefixWord ++ tailWord_7685316).sum := by decide
  have hdescent : baseEnd_7685316 < baseStart_7685316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685369 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 5]
def baseStart_7685369 : Nat := 118140960795 + 7685369 * 2 ^ 59
def prefixEnd_7685369 : Nat := 4983230072969 + 3 ^ 40 * 7685369 * 2
def baseEnd_7685369 : Nat := 3946288304164046692143137

theorem tailTrace_7685369 : CollatzResearch.WordTrace tailWord_7685369 prefixEnd_7685369 3946288304164046692143137 := by
  unfold tailWord_7685369
  simp only [CollatzResearch.WordTrace]
  refine ⟨280308435694228144372347161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186872290462818762914898107 280308435694228144372347161)
  ·
    refine ⟨210231326770671108279260371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280308435694228144372347161 210231326770671108279260371)
    ·
      refine ⟨315346990156006662418890557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210231326770671108279260371 315346990156006662418890557)
      ·
        refine ⟨118255121308502498407083959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315346990156006662418890557 118255121308502498407083959)
        ·
          refine ⟨177382681962753747610625939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118255121308502498407083959 177382681962753747610625939)
          ·
            refine ⟨266074022944130621415938909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177382681962753747610625939 266074022944130621415938909)
            ·
              refine ⟨99777758604048983030977091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266074022944130621415938909 99777758604048983030977091)
              ·
                refine ⟨149666637906073474546465637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99777758604048983030977091 149666637906073474546465637)
                ·
                  refine ⟨28062494607388776477462307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149666637906073474546465637 28062494607388776477462307)
                  ·
                    refine ⟨42093741911083164716193461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28062494607388776477462307 42093741911083164716193461)
                    ·
                      refine ⟨3946288304164046692143137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42093741911083164716193461 3946288304164046692143137)
                      ·
                        rfl

theorem cell23_7685369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_7685369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685369 prefixEnd_7685369 := by exact prefixLift 7685369
  have htrace : WordTrace (prefixWord ++ tailWord_7685369) baseStart_7685369 baseEnd_7685369 := by
    simpa [prefixWord, tailWord_7685369, baseEnd_7685369] using wordTrace_append hprefix tailTrace_7685369
  have hstable : (prefixWord ++ tailWord_7685369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685369).length < 2 ^ (prefixWord ++ tailWord_7685369).sum := by decide
  have hdescent : baseEnd_7685369 < baseStart_7685369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685394 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7685394 : Nat := 118140960795 + 7685394 * 2 ^ 59
def prefixEnd_7685394 : Nat := 4983230072969 + 3 ^ 40 * 7685394 * 2
def baseEnd_7685394 : Nat := 3946301141180409094330523

theorem tailTrace_7685394 : CollatzResearch.WordTrace tailWord_7685394 prefixEnd_7685394 3946301141180409094330523 := by
  unfold tailWord_7685394
  simp only [CollatzResearch.WordTrace]
  refine ⟨70077336879784393410501809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186872898346091715761338157 70077336879784393410501809)
  ·
    refine ⟨52558002659838295057876357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70077336879784393410501809 52558002659838295057876357)
    ·
      refine ⟨9854625498719680323351817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52558002659838295057876357 9854625498719680323351817)
      ·
        refine ⟨7390969124039760242513863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9854625498719680323351817 7390969124039760242513863)
        ·
          refine ⟨11086453686059640363770795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7390969124039760242513863 11086453686059640363770795)
          ·
            refine ⟨16629680529089460545656193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11086453686059640363770795 16629680529089460545656193)
            ·
              refine ⟨12472260396817095409242145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16629680529089460545656193 12472260396817095409242145)
              ·
                refine ⟨9354195297612821556931609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12472260396817095409242145 9354195297612821556931609)
                ·
                  refine ⟨7015646473209616167698707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9354195297612821556931609 7015646473209616167698707)
                  ·
                    refine ⟨10523469709814424251548061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7015646473209616167698707 10523469709814424251548061)
                    ·
                      refine ⟨3946301141180409094330523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10523469709814424251548061 3946301141180409094330523)
                      ·
                        rfl

theorem cell23_7685394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7685394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685394 prefixEnd_7685394 := by exact prefixLift 7685394
  have htrace : WordTrace (prefixWord ++ tailWord_7685394) baseStart_7685394 baseEnd_7685394 := by
    simpa [prefixWord, tailWord_7685394, baseEnd_7685394] using wordTrace_append hprefix tailTrace_7685394
  have hstable : (prefixWord ++ tailWord_7685394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685394).length < 2 ^ (prefixWord ++ tailWord_7685394).sum := by decide
  have hdescent : baseEnd_7685394 < baseStart_7685394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685400 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 2, 2, 2]
def baseStart_7685400 : Nat := 118140960795 + 7685400 * 2 ^ 59
def prefixEnd_7685400 : Nat := 4983230072969 + 3 ^ 40 * 7685400 * 2
def baseEnd_7685400 : Nat := 3946304222064336070855495

theorem tailTrace_7685400 : CollatzResearch.WordTrace tailWord_7685400 prefixEnd_7685400 3946304222064336070855495 := by
  unfold tailWord_7685400
  simp only [CollatzResearch.WordTrace]
  refine ⟨140154783178557918333362827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186873044238077224444483769 140154783178557918333362827)
  ·
    refine ⟨210232174767836877500044241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140154783178557918333362827 210232174767836877500044241)
    ·
      refine ⟨157674131075877658125033181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210232174767836877500044241 157674131075877658125033181)
      ·
        refine ⟨59127799153454121796887443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157674131075877658125033181 59127799153454121796887443)
        ·
          refine ⟨88691698730181182695331165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59127799153454121796887443 88691698730181182695331165)
          ·
            refine ⟨33259387023817943510749187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88691698730181182695331165 33259387023817943510749187)
            ·
              refine ⟨49889080535726915266123781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33259387023817943510749187 49889080535726915266123781)
              ·
                refine ⟨9354202600448796612398209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49889080535726915266123781 9354202600448796612398209)
                ·
                  refine ⟨7015651950336597459298657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9354202600448796612398209 7015651950336597459298657)
                  ·
                    refine ⟨5261738962752448094473993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7015651950336597459298657 5261738962752448094473993)
                    ·
                      refine ⟨3946304222064336070855495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5261738962752448094473993 3946304222064336070855495)
                      ·
                        rfl

theorem cell23_7685400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_7685400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685400 prefixEnd_7685400 := by exact prefixLift 7685400
  have htrace : WordTrace (prefixWord ++ tailWord_7685400) baseStart_7685400 baseEnd_7685400 := by
    simpa [prefixWord, tailWord_7685400, baseEnd_7685400] using wordTrace_append hprefix tailTrace_7685400
  have hstable : (prefixWord ++ tailWord_7685400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685400).length < 2 ^ (prefixWord ++ tailWord_7685400).sum := by decide
  have hdescent : baseEnd_7685400 < baseStart_7685400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685409 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7685409 : Nat := 118140960795 + 7685409 * 2 ^ 59
def prefixEnd_7685409 : Nat := 4983230072969 + 3 ^ 40 * 7685409 * 2
def baseEnd_7685409 : Nat := 3946308843390226535642953

theorem tailTrace_7685409 : CollatzResearch.WordTrace tailWord_7685409 prefixEnd_7685409 3946308843390226535642953 := by
  unfold tailWord_7685409
  simp only [CollatzResearch.WordTrace]
  refine ⟨280309894614083231203803281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186873263076055487469202187 280309894614083231203803281)
  ·
    refine ⟨210232420960562423402852461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280309894614083231203803281 210232420960562423402852461)
    ·
      refine ⟨78837157860210908776069673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210232420960562423402852461 78837157860210908776069673)
      ·
        refine ⟨59127868395158181582052255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78837157860210908776069673 59127868395158181582052255)
        ·
          refine ⟨88691802592737272373078383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59127868395158181582052255 88691802592737272373078383)
          ·
            refine ⟨133037703889105908559617575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88691802592737272373078383 133037703889105908559617575)
            ·
              refine ⟨199556555833658862839426363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133037703889105908559617575 199556555833658862839426363)
              ·
                refine ⟨299334833750488294259139545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199556555833658862839426363 299334833750488294259139545)
                ·
                  refine ⟨224501125312866220694354659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299334833750488294259139545 224501125312866220694354659)
                  ·
                    refine ⟨336751687969299331041531989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 224501125312866220694354659 336751687969299331041531989)
                    ·
                      refine ⟨3946308843390226535642953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 336751687969299331041531989 3946308843390226535642953)
                      ·
                        rfl

theorem cell23_7685409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7685409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685409 prefixEnd_7685409 := by exact prefixLift 7685409
  have htrace : WordTrace (prefixWord ++ tailWord_7685409) baseStart_7685409 baseEnd_7685409 := by
    simpa [prefixWord, tailWord_7685409, baseEnd_7685409] using wordTrace_append hprefix tailTrace_7685409
  have hstable : (prefixWord ++ tailWord_7685409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685409).length < 2 ^ (prefixWord ++ tailWord_7685409).sum := by decide
  have hdescent : baseEnd_7685409 < baseStart_7685409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685436 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_7685436 : Nat := 118140960795 + 7685436 * 2 ^ 59
def prefixEnd_7685436 : Nat := 4983230072969 + 3 ^ 40 * 7685436 * 2
def baseEnd_7685436 : Nat := 1315440902455965976668443

theorem tailTrace_7685436 : CollatzResearch.WordTrace tailWord_7685436 prefixEnd_7685436 1315440902455965976668443 := by
  unfold tailWord_7685436
  simp only [CollatzResearch.WordTrace]
  refine ⟨140155439692492707407518081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186873919589990276543357441 140155439692492707407518081)
  ·
    refine ⟨105116579769369530555638561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140155439692492707407518081 105116579769369530555638561)
    ·
      refine ⟨78837434827027147916728921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105116579769369530555638561 78837434827027147916728921)
      ·
        refine ⟨59128076120270360937546691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78837434827027147916728921 59128076120270360937546691)
        ·
          refine ⟨88692114180405541406320037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59128076120270360937546691 88692114180405541406320037)
          ·
            refine ⟨16629771408826039013685007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88692114180405541406320037 16629771408826039013685007)
            ·
              refine ⟨24944657113239058520527511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16629771408826039013685007 24944657113239058520527511)
              ·
                refine ⟨37416985669858587780791267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24944657113239058520527511 37416985669858587780791267)
                ·
                  refine ⟨56125478504787881671186901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37416985669858587780791267 56125478504787881671186901)
                  ·
                    refine ⟨1315440902455965976668443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56125478504787881671186901 1315440902455965976668443)
                    ·
                      rfl

theorem cell23_7685436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_7685436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685436 prefixEnd_7685436 := by exact prefixLift 7685436
  have htrace : WordTrace (prefixWord ++ tailWord_7685436) baseStart_7685436 baseEnd_7685436 := by
    simpa [prefixWord, tailWord_7685436, baseEnd_7685436] using wordTrace_append hprefix tailTrace_7685436
  have hstable : (prefixWord ++ tailWord_7685436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685436).length < 2 ^ (prefixWord ++ tailWord_7685436).sum := by decide
  have hdescent : baseEnd_7685436 < baseStart_7685436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685456 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 4]
def baseStart_7685456 : Nat := 118140960795 + 7685456 * 2 ^ 59
def prefixEnd_7685456 : Nat := 4983230072969 + 3 ^ 40 * 7685456 * 2
def baseEnd_7685456 : Nat := 3946332976980987851755237

theorem tailTrace_7685456 : CollatzResearch.WordTrace tailWord_7685456 prefixEnd_7685456 3946332976980987851755237 := by
  unfold tailWord_7685456
  simp only [CollatzResearch.WordTrace]
  refine ⟨140155804422456479115382111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186874405896608638820509481 140155804422456479115382111)
  ·
    refine ⟨210233706633684718673073167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140155804422456479115382111 210233706633684718673073167)
    ·
      refine ⟨315350559950527078009609751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210233706633684718673073167 315350559950527078009609751)
      ·
        refine ⟨473025839925790617014414627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315350559950527078009609751 473025839925790617014414627)
        ·
          refine ⟨709538759888685925521621941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473025839925790617014414627 709538759888685925521621941)
          ·
            refine ⟨66519258739564305517652057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 709538759888685925521621941 66519258739564305517652057)
            ·
              refine ⟨49889444054673229138239043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66519258739564305517652057 49889444054673229138239043)
              ·
                refine ⟨74834166082009843707358565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49889444054673229138239043 74834166082009843707358565)
                ·
                  refine ⟨14031406140376845695129731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74834166082009843707358565 14031406140376845695129731)
                  ·
                    refine ⟨21047109210565268542694597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14031406140376845695129731 21047109210565268542694597)
                    ·
                      refine ⟨3946332976980987851755237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21047109210565268542694597 3946332976980987851755237)
                      ·
                        rfl

theorem cell23_7685456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_7685456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685456 prefixEnd_7685456 := by exact prefixLift 7685456
  have htrace : WordTrace (prefixWord ++ tailWord_7685456) baseStart_7685456 baseEnd_7685456 := by
    simpa [prefixWord, tailWord_7685456, baseEnd_7685456] using wordTrace_append hprefix tailTrace_7685456
  have hstable : (prefixWord ++ tailWord_7685456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685456).length < 2 ^ (prefixWord ++ tailWord_7685456).sum := by decide
  have hdescent : baseEnd_7685456 < baseStart_7685456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685543 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 3, 5]
def baseStart_7685543 : Nat := 118140960795 + 7685543 * 2 ^ 59
def prefixEnd_7685543 : Nat := 4983230072969 + 3 ^ 40 * 7685543 * 2
def baseEnd_7685543 : Nat := 1315459216599309670455779

theorem tailTrace_7685543 : CollatzResearch.WordTrace tailWord_7685543 prefixEnd_7685543 1315459216599309670455779 := by
  unfold tailWord_7685543
  simp only [CollatzResearch.WordTrace]
  refine ⟨280314781995597772089181283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186876521330398514726120855 280314781995597772089181283)
  ·
    refine ⟨420472172993396658133771925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280314781995597772089181283 420472172993396658133771925)
    ·
      refine ⟨19709633109065468350020559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 420472172993396658133771925 19709633109065468350020559)
      ·
        refine ⟨29564449663598202525030839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19709633109065468350020559 29564449663598202525030839)
        ·
          refine ⟨44346674495397303787546259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29564449663598202525030839 44346674495397303787546259)
          ·
            refine ⟨66520011743095955681319389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44346674495397303787546259 66520011743095955681319389)
            ·
              refine ⟨24945004403660983380494771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66520011743095955681319389 24945004403660983380494771)
              ·
                refine ⟨37417506605491475070742157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24945004403660983380494771 37417506605491475070742157)
                ·
                  refine ⟨14031564977059303151528309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37417506605491475070742157 14031564977059303151528309)
                  ·
                    refine ⟨1315459216599309670455779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14031564977059303151528309 1315459216599309670455779)
                    ·
                      rfl

theorem cell23_7685543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_7685543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685543 prefixEnd_7685543 := by exact prefixLift 7685543
  have htrace : WordTrace (prefixWord ++ tailWord_7685543) baseStart_7685543 baseEnd_7685543 := by
    simpa [prefixWord, tailWord_7685543, baseEnd_7685543] using wordTrace_append hprefix tailTrace_7685543
  have hstable : (prefixWord ++ tailWord_7685543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685543).length < 2 ^ (prefixWord ++ tailWord_7685543).sum := by decide
  have hdescent : baseEnd_7685543 < baseStart_7685543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685583 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 3]
def baseStart_7685583 : Nat := 118140960795 + 7685583 * 2 ^ 59
def prefixEnd_7685583 : Nat := 4983230072969 + 3 ^ 40 * 7685583 * 2
def baseEnd_7685583 : Nat := 3946398189024108854867153

theorem tailTrace_7685583 : CollatzResearch.WordTrace tailWord_7685583 prefixEnd_7685583 3946398189024108854867153 := by
  unfold tailWord_7685583
  simp only [CollatzResearch.WordTrace]
  refine ⟨280316240915452858920637403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186877493943635239280424935 280316240915452858920637403)
  ·
    refine ⟨420474361373179288380956105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280316240915452858920637403 420474361373179288380956105)
    ·
      refine ⟨315355771029884466285717079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420474361373179288380956105 315355771029884466285717079)
      ·
        refine ⟨473033656544826699428575619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315355771029884466285717079 473033656544826699428575619)
        ·
          refine ⟨709550484817240049142863429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473033656544826699428575619 709550484817240049142863429)
          ·
            refine ⟨133040715903232509214286893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 709550484817240049142863429 133040715903232509214286893)
            ·
              refine ⟨49890268463712190955357585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133040715903232509214286893 49890268463712190955357585)
              ·
                refine ⟨37417701347784143216518189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49890268463712190955357585 37417701347784143216518189)
                ·
                  refine ⟨14031638005419053706194321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37417701347784143216518189 14031638005419053706194321)
                  ·
                    refine ⟨10523728504064290279645741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14031638005419053706194321 10523728504064290279645741)
                    ·
                      refine ⟨3946398189024108854867153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10523728504064290279645741 3946398189024108854867153)
                      ·
                        rfl

theorem cell23_7685583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 3].length) (baseStart_7685583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685583 prefixEnd_7685583 := by exact prefixLift 7685583
  have htrace : WordTrace (prefixWord ++ tailWord_7685583) baseStart_7685583 baseEnd_7685583 := by
    simpa [prefixWord, tailWord_7685583, baseEnd_7685583] using wordTrace_append hprefix tailTrace_7685583
  have hstable : (prefixWord ++ tailWord_7685583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685583).length < 2 ^ (prefixWord ++ tailWord_7685583).sum := by decide
  have hdescent : baseEnd_7685583 < baseStart_7685583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685590 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_7685590 : Nat := 118140960795 + 7685590 * 2 ^ 59
def prefixEnd_7685590 : Nat := 4983230072969 + 3 ^ 40 * 7685590 * 2
def baseEnd_7685590 : Nat := 1315467261129563442493207

theorem tailTrace_7685590 : CollatzResearch.WordTrace tailWord_7685590 prefixEnd_7685590 1315467261129563442493207 := by
  unfold tailWord_7685590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17519781014151718694758889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186877664150951666077428149 17519781014151718694758889)
  ·
    refine ⟨13139835760613789021069167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17519781014151718694758889 13139835760613789021069167)
    ·
      refine ⟨19709753640920683531603751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13139835760613789021069167 19709753640920683531603751)
      ·
        refine ⟨29564630461381025297405627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19709753640920683531603751 29564630461381025297405627)
        ·
          refine ⟨44346945692071537946108441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29564630461381025297405627 44346945692071537946108441)
          ·
            refine ⟨33260209269053653459581331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44346945692071537946108441 33260209269053653459581331)
            ·
              refine ⟨49890313903580480189371997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33260209269053653459581331 49890313903580480189371997)
              ·
                refine ⟨18708867713842680071014499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49890313903580480189371997 18708867713842680071014499)
                ·
                  refine ⟨28063301570764020106521749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18708867713842680071014499 28063301570764020106521749)
                  ·
                    refine ⟨1315467261129563442493207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28063301570764020106521749 1315467261129563442493207)
                    ·
                      rfl

theorem cell23_7685590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_7685590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685590 prefixEnd_7685590 := by exact prefixLift 7685590
  have htrace : WordTrace (prefixWord ++ tailWord_7685590) baseStart_7685590 baseEnd_7685590 := by
    simpa [prefixWord, tailWord_7685590, baseEnd_7685590] using wordTrace_append hprefix tailTrace_7685590
  have hstable : (prefixWord ++ tailWord_7685590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685590).length < 2 ^ (prefixWord ++ tailWord_7685590).sum := by decide
  have hdescent : baseEnd_7685590 < baseStart_7685590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685593 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 4]
def baseStart_7685593 : Nat := 118140960795 + 7685593 * 2 ^ 59
def prefixEnd_7685593 : Nat := 4983230072969 + 3 ^ 40 * 7685593 * 2
def baseEnd_7685593 : Nat := 3946403323830653815742107

theorem tailTrace_7685593 : CollatzResearch.WordTrace tailWord_7685593 prefixEnd_7685593 3946403323830653815742107 := by
  unfold tailWord_7685593
  simp only [CollatzResearch.WordTrace]
  refine ⟨280316605645416630628501433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186877737096944420419000955 280316605645416630628501433)
  ·
    refine ⟨210237454234062472971376075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280316605645416630628501433 210237454234062472971376075)
    ·
      refine ⟨315356181351093709457064113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210237454234062472971376075 315356181351093709457064113)
      ·
        refine ⟨236517136013320282092798085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315356181351093709457064113 236517136013320282092798085)
        ·
          refine ⟨44346963002497552892399641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236517136013320282092798085 44346963002497552892399641)
          ·
            refine ⟨33260222251873164669299731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44346963002497552892399641 33260222251873164669299731)
            ·
              refine ⟨49890333377809747003949597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33260222251873164669299731 49890333377809747003949597)
              ·
                refine ⟨18708875016678655126481099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49890333377809747003949597 18708875016678655126481099)
                ·
                  refine ⟨28063312525017982689721649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18708875016678655126481099 28063312525017982689721649)
                  ·
                    refine ⟨21047484393763487017291237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28063312525017982689721649 21047484393763487017291237)
                    ·
                      refine ⟨3946403323830653815742107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21047484393763487017291237 3946403323830653815742107)
                      ·
                        rfl

theorem cell23_7685593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_7685593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685593 prefixEnd_7685593 := by exact prefixLift 7685593
  have htrace : WordTrace (prefixWord ++ tailWord_7685593) baseStart_7685593 baseEnd_7685593 := by
    simpa [prefixWord, tailWord_7685593, baseEnd_7685593] using wordTrace_append hprefix tailTrace_7685593
  have hstable : (prefixWord ++ tailWord_7685593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685593).length < 2 ^ (prefixWord ++ tailWord_7685593).sum := by decide
  have hdescent : baseEnd_7685593 < baseStart_7685593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685597 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_7685597 : Nat := 118140960795 + 7685597 * 2 ^ 59
def prefixEnd_7685597 : Nat := 4983230072969 + 3 ^ 40 * 7685597 * 2
def baseEnd_7685597 : Nat := 3946405377753271800092089

theorem tailTrace_7685597 : CollatzResearch.WordTrace tailWord_7685597 prefixEnd_7685597 3946405377753271800092089 := by
  unfold tailWord_7685597
  simp only [CollatzResearch.WordTrace]
  refine ⟨280316751537402139311647045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186877834358268092874431363 280316751537402139311647045)
  ·
    refine ⟨52559390913262901120933821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280316751537402139311647045 52559390913262901120933821)
    ·
      refine ⟨19709771592473587920350183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52559390913262901120933821 19709771592473587920350183)
      ·
        refine ⟨29564657388710381880525275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19709771592473587920350183 29564657388710381880525275)
        ·
          refine ⟨44346986083065572820787913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29564657388710381880525275 44346986083065572820787913)
          ·
            refine ⟨33260239562299179615590935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44346986083065572820787913 33260239562299179615590935)
            ·
              refine ⟨49890359343448769423386403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33260239562299179615590935 49890359343448769423386403)
              ·
                refine ⟨74835539015173154135079605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49890359343448769423386403 74835539015173154135079605)
                ·
                  refine ⟨7015831782672483200163713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74835539015173154135079605 7015831782672483200163713)
                  ·
                    refine ⟨5261873837004362400122785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7015831782672483200163713 5261873837004362400122785)
                    ·
                      refine ⟨3946405377753271800092089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5261873837004362400122785 3946405377753271800092089)
                      ·
                        rfl

theorem cell23_7685597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_7685597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685597 prefixEnd_7685597 := by exact prefixLift 7685597
  have htrace : WordTrace (prefixWord ++ tailWord_7685597) baseStart_7685597 baseEnd_7685597 := by
    simpa [prefixWord, tailWord_7685597, baseEnd_7685597] using wordTrace_append hprefix tailTrace_7685597
  have hstable : (prefixWord ++ tailWord_7685597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685597).length < 2 ^ (prefixWord ++ tailWord_7685597).sum := by decide
  have hdescent : baseEnd_7685597 < baseStart_7685597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685617 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 1, 2, 3]
def baseStart_7685617 : Nat := 118140960795 + 7685617 * 2 ^ 59
def prefixEnd_7685617 : Nat := 4983230072969 + 3 ^ 40 * 7685617 * 2
def baseEnd_7685617 : Nat := 3946415647366361721841997

theorem tailTrace_7685617 : CollatzResearch.WordTrace tailWord_7685617 prefixEnd_7685617 3946415647366361721841997 := by
  unfold tailWord_7685617
  simp only [CollatzResearch.WordTrace]
  refine ⟨280317480997329682727375105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186878320664886455151583403 280317480997329682727375105)
  ·
    refine ⟨210238110747997262045531329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280317480997329682727375105 210238110747997262045531329)
    ·
      refine ⟨157678583060997946534148497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210238110747997262045531329 157678583060997946534148497)
      ·
        refine ⟨118258937295748459900611373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157678583060997946534148497 118258937295748459900611373)
        ·
          refine ⟨44347101485905672462729265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118258937295748459900611373 44347101485905672462729265)
          ·
            refine ⟨33260326114429254347046949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44347101485905672462729265 33260326114429254347046949)
            ·
              refine ⟨6236311146455485190071303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33260326114429254347046949 6236311146455485190071303)
              ·
                refine ⟨9354466719683227785106955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6236311146455485190071303 9354466719683227785106955)
                ·
                  refine ⟨14031700079524841677660433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9354466719683227785106955 14031700079524841677660433)
                  ·
                    refine ⟨10523775059643631258245325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14031700079524841677660433 10523775059643631258245325)
                    ·
                      refine ⟨3946415647366361721841997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10523775059643631258245325 3946415647366361721841997)
                      ·
                        rfl

theorem cell23_7685617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_7685617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685617 prefixEnd_7685617 := by exact prefixLift 7685617
  have htrace : WordTrace (prefixWord ++ tailWord_7685617) baseStart_7685617 baseEnd_7685617 := by
    simpa [prefixWord, tailWord_7685617, baseEnd_7685617] using wordTrace_append hprefix tailTrace_7685617
  have hstable : (prefixWord ++ tailWord_7685617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685617).length < 2 ^ (prefixWord ++ tailWord_7685617).sum := by decide
  have hdescent : baseEnd_7685617 < baseStart_7685617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685640 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 5, 3, 2]
def baseStart_7685640 : Nat := 118140960795 + 7685640 * 2 ^ 59
def prefixEnd_7685640 : Nat := 4983230072969 + 3 ^ 40 * 7685640 * 2
def baseEnd_7685640 : Nat := 3946427457421415131854391

theorem tailTrace_7685640 : CollatzResearch.WordTrace tailWord_7685640 prefixEnd_7685640 3946427457421415131854391 := by
  unfold tailWord_7685640
  simp only [CollatzResearch.WordTrace]
  refine ⟨140159159938123178827731187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186878879917497571770308249 140159159938123178827731187)
  ·
    refine ⟨210238739907184768241596781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140159159938123178827731187 210238739907184768241596781)
    ·
      refine ⟨78839527465194288090598793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210238739907184768241596781 78839527465194288090598793)
      ·
        refine ⟨59129645598895716067949095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78839527465194288090598793 59129645598895716067949095)
        ·
          refine ⟨88694468398343574101923643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59129645598895716067949095 88694468398343574101923643)
          ·
            refine ⟨133041702597515361152885465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88694468398343574101923643 133041702597515361152885465)
            ·
              refine ⟨99781276948136520864664099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133041702597515361152885465 99781276948136520864664099)
              ·
                refine ⟨149671915422204781296996149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99781276948136520864664099 149671915422204781296996149)
                ·
                  refine ⟨14031742070831698246593389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149671915422204781296996149 14031742070831698246593389)
                  ·
                    refine ⟨5261903276561886842472521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14031742070831698246593389 5261903276561886842472521)
                    ·
                      refine ⟨3946427457421415131854391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5261903276561886842472521 3946427457421415131854391)
                      ·
                        rfl

theorem cell23_7685640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_7685640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685640 prefixEnd_7685640 := by exact prefixLift 7685640
  have htrace : WordTrace (prefixWord ++ tailWord_7685640) baseStart_7685640 baseEnd_7685640 := by
    simpa [prefixWord, tailWord_7685640, baseEnd_7685640] using wordTrace_append hprefix tailTrace_7685640
  have hstable : (prefixWord ++ tailWord_7685640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685640).length < 2 ^ (prefixWord ++ tailWord_7685640).sum := by decide
  have hdescent : baseEnd_7685640 < baseStart_7685640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685687 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 4, 2, 2]
def baseStart_7685687 : Nat := 118140960795 + 7685687 * 2 ^ 59
def prefixEnd_7685687 : Nat := 4983230072969 + 3 ^ 40 * 7685687 * 2
def baseEnd_7685687 : Nat := 3946451591012176447966675

theorem tailTrace_7685687 : CollatzResearch.WordTrace tailWord_7685687 prefixEnd_7685687 3946451591012176447966675 := by
  unfold tailWord_7685687
  simp only [CollatzResearch.WordTrace]
  refine ⟨280320034107076084682423315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186880022738050723121615543 280320034107076084682423315)
  ·
    refine ⟨420480051160614127023634973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280320034107076084682423315 420480051160614127023634973)
    ·
      refine ⟨157680019185230297633863115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420480051160614127023634973 157680019185230297633863115)
      ·
        refine ⟨236520028777845446450794673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157680019185230297633863115 236520028777845446450794673)
        ·
          refine ⟨177390021583384084838096005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236520028777845446450794673 177390021583384084838096005)
          ·
            refine ⟨33260629046884515907143001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177390021583384084838096005 33260629046884515907143001)
            ·
              refine ⟨24945471785163386930357251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33260629046884515907143001 24945471785163386930357251)
              ·
                refine ⟨37418207677745080395535877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24945471785163386930357251 37418207677745080395535877)
                ·
                  refine ⟨7015913939577202574162977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37418207677745080395535877 7015913939577202574162977)
                  ·
                    refine ⟨5261935454682901930622233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7015913939577202574162977 5261935454682901930622233)
                    ·
                      refine ⟨3946451591012176447966675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5261935454682901930622233 3946451591012176447966675)
                      ·
                        rfl

theorem cell23_7685687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 2, 2].length) (baseStart_7685687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685687 prefixEnd_7685687 := by exact prefixLift 7685687
  have htrace : WordTrace (prefixWord ++ tailWord_7685687) baseStart_7685687 baseEnd_7685687 := by
    simpa [prefixWord, tailWord_7685687, baseEnd_7685687] using wordTrace_append hprefix tailTrace_7685687
  have hstable : (prefixWord ++ tailWord_7685687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685687).length < 2 ^ (prefixWord ++ tailWord_7685687).sum := by decide
  have hdescent : baseEnd_7685687 < baseStart_7685687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685743 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 4]
def baseStart_7685743 : Nat := 118140960795 + 7685743 * 2 ^ 59
def prefixEnd_7685743 : Nat := 4983230072969 + 3 ^ 40 * 7685743 * 2
def baseEnd_7685743 : Nat := 3946480345928828228866417

theorem tailTrace_7685743 : CollatzResearch.WordTrace tailWord_7685743 prefixEnd_7685743 3946480345928828228866417 := by
  unfold tailWord_7685743
  simp only [CollatzResearch.WordTrace]
  refine ⟨280322076594873206246461883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186881384396582137497641255 280322076594873206246461883)
  ·
    refine ⟨420483114892309809369692825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280322076594873206246461883 420483114892309809369692825)
    ·
      refine ⟨315362336169232357027269619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420483114892309809369692825 315362336169232357027269619)
      ·
        refine ⟨473043504253848535540904429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315362336169232357027269619 473043504253848535540904429)
        ·
          refine ⟨177391314095193200827839161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473043504253848535540904429 177391314095193200827839161)
          ·
            refine ⟨133043485571394900620879371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177391314095193200827839161 133043485571394900620879371)
            ·
              refine ⟨199565228357092350931319057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133043485571394900620879371 199565228357092350931319057)
              ·
                refine ⟨149673921267819263198489293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199565228357092350931319057 149673921267819263198489293)
                ·
                  refine ⟨56127720475432223699433485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149673921267819263198489293 56127720475432223699433485)
                  ·
                    refine ⟨21047895178287083887287557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56127720475432223699433485 21047895178287083887287557)
                    ·
                      refine ⟨3946480345928828228866417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21047895178287083887287557 3946480345928828228866417)
                      ·
                        rfl

theorem cell23_7685743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_7685743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685743 prefixEnd_7685743 := by exact prefixLift 7685743
  have htrace : WordTrace (prefixWord ++ tailWord_7685743) baseStart_7685743 baseEnd_7685743 := by
    simpa [prefixWord, tailWord_7685743, baseEnd_7685743] using wordTrace_append hprefix tailTrace_7685743
  have hstable : (prefixWord ++ tailWord_7685743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685743).length < 2 ^ (prefixWord ++ tailWord_7685743).sum := by decide
  have hdescent : baseEnd_7685743 < baseStart_7685743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685744 : List Nat := [2, 1, 1, 1, 6, 3, 2, 2, 5]
def baseStart_7685744 : Nat := 118140960795 + 7685744 * 2 ^ 59
def prefixEnd_7685744 : Nat := 4983230072969 + 3 ^ 40 * 7685744 * 2
def baseEnd_7685744 : Nat := 438497873267720302772657

theorem tailTrace_7685744 : CollatzResearch.WordTrace tailWord_7685744 prefixEnd_7685744 438497873267720302772657 := by
  unfold tailWord_7685744
  simp only [CollatzResearch.WordTrace]
  refine ⟨140161056533934791708624143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186881408711913055611498857 140161056533934791708624143)
  ·
    refine ⟨210241584800902187562936215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140161056533934791708624143 210241584800902187562936215)
    ·
      refine ⟨315362377201353281344404323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210241584800902187562936215 315362377201353281344404323)
      ·
        refine ⟨473043565802029922016606485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315362377201353281344404323 473043565802029922016606485)
        ·
          refine ⟨22173917146970152594528429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 473043565802029922016606485 22173917146970152594528429)
          ·
            refine ⟨8315218930113807222948161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22173917146970152594528429 8315218930113807222948161)
            ·
              refine ⟨6236414197585355417211121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8315218930113807222948161 6236414197585355417211121)
              ·
                refine ⟨4677310648189016562908341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6236414197585355417211121 4677310648189016562908341)
                ·
                  refine ⟨438497873267720302772657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4677310648189016562908341 438497873267720302772657)
                  ·
                    rfl

theorem cell23_7685744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 5].length) (baseStart_7685744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685744 prefixEnd_7685744 := by exact prefixLift 7685744
  have htrace : WordTrace (prefixWord ++ tailWord_7685744) baseStart_7685744 baseEnd_7685744 := by
    simpa [prefixWord, tailWord_7685744, baseEnd_7685744] using wordTrace_append hprefix tailTrace_7685744
  have hstable : (prefixWord ++ tailWord_7685744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685744).length < 2 ^ (prefixWord ++ tailWord_7685744).sum := by decide
  have hdescent : baseEnd_7685744 < baseStart_7685744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685814 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_7685814 : Nat := 118140960795 + 7685814 * 2 ^ 59
def prefixEnd_7685814 : Nat := 4983230072969 + 3 ^ 40 * 7685814 * 2
def baseEnd_7685814 : Nat := 3946516803055297451078591

theorem tailTrace_7685814 : CollatzResearch.WordTrace tailWord_7685814 prefixEnd_7685814 3946516803055297451078591 := by
  unfold tailWord_7685814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17520291636100999085768531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186883110785077323581530997 17520291636100999085768531)
  ·
    refine ⟨26280437454151498628652797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17520291636100999085768531 26280437454151498628652797)
    ·
      refine ⟨9855164045306811985744799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26280437454151498628652797 9855164045306811985744799)
      ·
        refine ⟨14782746067960217978617199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9855164045306811985744799 14782746067960217978617199)
        ·
          refine ⟨22174119101940326967925799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14782746067960217978617199 22174119101940326967925799)
          ·
            refine ⟨33261178652910490451888699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22174119101940326967925799 33261178652910490451888699)
            ·
              refine ⟨49891767979365735677833049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33261178652910490451888699 49891767979365735677833049)
              ·
                refine ⟨37418825984524301758374787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49891767979365735677833049 37418825984524301758374787)
                ·
                  refine ⟨56128238976786452637562181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37418825984524301758374787 56128238976786452637562181)
                  ·
                    refine ⟨10524044808147459869542909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56128238976786452637562181 10524044808147459869542909)
                    ·
                      refine ⟨3946516803055297451078591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10524044808147459869542909 3946516803055297451078591)
                      ·
                        rfl

theorem cell23_7685814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_7685814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685814 prefixEnd_7685814 := by exact prefixLift 7685814
  have htrace : WordTrace (prefixWord ++ tailWord_7685814) baseStart_7685814 baseEnd_7685814 := by
    simpa [prefixWord, tailWord_7685814, baseEnd_7685814] using wordTrace_append hprefix tailTrace_7685814
  have hstable : (prefixWord ++ tailWord_7685814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685814).length < 2 ^ (prefixWord ++ tailWord_7685814).sum := by decide
  have hdescent : baseEnd_7685814 < baseStart_7685814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685884 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 5, 2, 2]
def baseStart_7685884 : Nat := 118140960795 + 7685884 * 2 ^ 59
def prefixEnd_7685884 : Nat := 4983230072969 + 3 ^ 40 * 7685884 * 2
def baseEnd_7685884 : Nat := 3946552746701112177203269

theorem tailTrace_7685884 : CollatzResearch.WordTrace tailWord_7685884 prefixEnd_7685884 3946552746701112177203269 := by
  unfold tailWord_7685884
  simp only [CollatzResearch.WordTrace]
  refine ⟨140163609643681193663672353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186884812858241591551563137 140163609643681193663672353)
  ·
    refine ⟨105122707232760895247754265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140163609643681193663672353 105122707232760895247754265)
    ·
      refine ⟨78842030424570671435815699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105122707232760895247754265 78842030424570671435815699)
      ·
        refine ⟨118263045636856007153723549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78842030424570671435815699 118263045636856007153723549)
        ·
          refine ⟨44348642113821002682646331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118263045636856007153723549 44348642113821002682646331)
          ·
            refine ⟨66522963170731504023969497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44348642113821002682646331 66522963170731504023969497)
            ·
              refine ⟨49892222378048628017977123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66522963170731504023969497 49892222378048628017977123)
              ·
                refine ⟨74838333567072942026965685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49892222378048628017977123 74838333567072942026965685)
                ·
                  refine ⟨7016093771913088315028033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74838333567072942026965685 7016093771913088315028033)
                  ·
                    refine ⟨5262070328934816236271025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7016093771913088315028033 5262070328934816236271025)
                    ·
                      refine ⟨3946552746701112177203269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262070328934816236271025 3946552746701112177203269)
                      ·
                        rfl

theorem cell23_7685884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_7685884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685884 prefixEnd_7685884 := by exact prefixLift 7685884
  have htrace : WordTrace (prefixWord ++ tailWord_7685884) baseStart_7685884 baseEnd_7685884 := by
    simpa [prefixWord, tailWord_7685884, baseEnd_7685884] using wordTrace_append hprefix tailTrace_7685884
  have hstable : (prefixWord ++ tailWord_7685884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685884).length < 2 ^ (prefixWord ++ tailWord_7685884).sum := by decide
  have hdescent : baseEnd_7685884 < baseStart_7685884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685920 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 1, 9]
def baseStart_7685920 : Nat := 118140960795 + 7685920 * 2 ^ 59
def prefixEnd_7685920 : Nat := 4983230072969 + 3 ^ 40 * 7685920 * 2
def baseEnd_7685920 : Nat := 1315523744001558012117701

theorem tailTrace_7685920 : CollatzResearch.WordTrace tailWord_7685920 prefixEnd_7685920 1315523744001558012117701 := by
  unfold tailWord_7685920
  simp only [CollatzResearch.WordTrace]
  refine ⟨140164266157615982737827607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186885688210154643650436809 140164266157615982737827607)
  ·
    refine ⟨210246399236423974106741411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140164266157615982737827607 210246399236423974106741411)
    ·
      refine ⟨315369598854635961160112117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210246399236423974106741411 315369598854635961160112117)
      ·
        refine ⟨29565899892622121358760511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 315369598854635961160112117 29565899892622121358760511)
        ·
          refine ⟨44348849838933182038140767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29565899892622121358760511 44348849838933182038140767)
          ·
            refine ⟨66523274758399773057211151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44348849838933182038140767 66523274758399773057211151)
            ·
              refine ⟨99784912137599659585816727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66523274758399773057211151 99784912137599659585816727)
              ·
                refine ⟨149677368206399489378725091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99784912137599659585816727 149677368206399489378725091)
                ·
                  refine ⟨224516052309599234068087637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149677368206399489378725091 224516052309599234068087637)
                  ·
                    refine ⟨1315523744001558012117701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 224516052309599234068087637 1315523744001558012117701)
                    ·
                      rfl

theorem cell23_7685920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_7685920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685920 prefixEnd_7685920 := by exact prefixLift 7685920
  have htrace : WordTrace (prefixWord ++ tailWord_7685920) baseStart_7685920 baseEnd_7685920 := by
    simpa [prefixWord, tailWord_7685920, baseEnd_7685920] using wordTrace_append hprefix tailTrace_7685920
  have hstable : (prefixWord ++ tailWord_7685920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685920).length < 2 ^ (prefixWord ++ tailWord_7685920).sum := by decide
  have hdescent : baseEnd_7685920 < baseStart_7685920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685944 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 3, 3, 2]
def baseStart_7685944 : Nat := 118140960795 + 7685944 * 2 ^ 59
def prefixEnd_7685944 : Nat := 4983230072969 + 3 ^ 40 * 7685944 * 2
def baseEnd_7685944 : Nat := 3946583555540381942452993

theorem tailTrace_7685944 : CollatzResearch.WordTrace tailWord_7685944 prefixEnd_7685944 3946583555540381942452993 := by
  unfold tailWord_7685944
  simp only [CollatzResearch.WordTrace]
  refine ⟨140164703833572508787264443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186886271778096678383019257 140164703833572508787264443)
  ·
    refine ⟨210247055750358763180896665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140164703833572508787264443 210247055750358763180896665)
    ·
      refine ⟨157685291812769072385672499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210247055750358763180896665 157685291812769072385672499)
      ·
        refine ⟨236527937719153608578508749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157685291812769072385672499 236527937719153608578508749)
        ·
          refine ⟨88697976644682603216940781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236527937719153608578508749 88697976644682603216940781)
          ·
            refine ⟨33261741241755976206352793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88697976644682603216940781 33261741241755976206352793)
            ·
              refine ⟨24946305931316982154764595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33261741241755976206352793 24946305931316982154764595)
              ·
                refine ⟨37419458896975473232146893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24946305931316982154764595 37419458896975473232146893)
                ·
                  refine ⟨14032297086365802462055085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37419458896975473232146893 14032297086365802462055085)
                  ·
                    refine ⟨5262111407387175923270657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14032297086365802462055085 5262111407387175923270657)
                    ·
                      refine ⟨3946583555540381942452993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262111407387175923270657 3946583555540381942452993)
                      ·
                        rfl

theorem cell23_7685944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 3, 2].length) (baseStart_7685944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685944 prefixEnd_7685944 := by exact prefixLift 7685944
  have htrace : WordTrace (prefixWord ++ tailWord_7685944) baseStart_7685944 baseEnd_7685944 := by
    simpa [prefixWord, tailWord_7685944, baseEnd_7685944] using wordTrace_append hprefix tailTrace_7685944
  have hstable : (prefixWord ++ tailWord_7685944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685944).length < 2 ^ (prefixWord ++ tailWord_7685944).sum := by decide
  have hdescent : baseEnd_7685944 < baseStart_7685944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7685997 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 7]
def baseStart_7685997 : Nat := 118140960795 + 7685997 * 2 ^ 59
def prefixEnd_7685997 : Nat := 4983230072969 + 3 ^ 40 * 7685997 * 2
def baseEnd_7685997 : Nat := 438512307779452248343361

theorem tailTrace_7685997 : CollatzResearch.WordTrace tailWord_7685997 prefixEnd_7685997 438512307779452248343361 := by
  unfold tailWord_7685997
  simp only [CollatzResearch.WordTrace]
  refine ⟨280331340735953007626208245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186887560490635338417472163 280331340735953007626208245)
  ·
    refine ⟨26281063193995594464957023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280331340735953007626208245 26281063193995594464957023)
    ·
      refine ⟨39421594790993391697435535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26281063193995594464957023 39421594790993391697435535)
      ·
        refine ⟨59132392186490087546153303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39421594790993391697435535 59132392186490087546153303)
        ·
          refine ⟨88698588279735131319229955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59132392186490087546153303 88698588279735131319229955)
          ·
            refine ⟨133047882419602696978844933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88698588279735131319229955 133047882419602696978844933)
            ·
              refine ⟨24946477953675505683533425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133047882419602696978844933 24946477953675505683533425)
              ·
                refine ⟨18709858465256629262650069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24946477953675505683533425 18709858465256629262650069)
                ·
                  refine ⟨438512307779452248343361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18709858465256629262650069 438512307779452248343361)
                  ·
                    rfl

theorem cell23_7685997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_7685997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7685997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7685997 prefixEnd_7685997 := by exact prefixLift 7685997
  have htrace : WordTrace (prefixWord ++ tailWord_7685997) baseStart_7685997 baseEnd_7685997 := by
    simpa [prefixWord, tailWord_7685997, baseEnd_7685997] using wordTrace_append hprefix tailTrace_7685997
  have hstable : (prefixWord ++ tailWord_7685997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7685997).length < 2 ^ (prefixWord ++ tailWord_7685997).sum := by decide
  have hdescent : baseEnd_7685997 < baseStart_7685997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7685997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686037 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_7686037 : Nat := 118140960795 + 7686037 * 2 ^ 59
def prefixEnd_7686037 : Nat := 4983230072969 + 3 ^ 40 * 7686037 * 2
def baseEnd_7686037 : Nat := 3946631309241250078590065

theorem tailTrace_7686037 : CollatzResearch.WordTrace tailWord_7686037 prefixEnd_7686037 3946631309241250078590065 := by
  unfold tailWord_7686037
  simp only [CollatzResearch.WordTrace]
  refine ⟨280332799655808094457664365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186888533103872062971776243 280332799655808094457664365)
  ·
    refine ⟨105124799870928035421624137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280332799655808094457664365 105124799870928035421624137)
    ·
      refine ⟨78843599903196026566218103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105124799870928035421624137 78843599903196026566218103)
      ·
        refine ⟨118265399854794039849327155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78843599903196026566218103 118265399854794039849327155)
        ·
          refine ⟨177398099782191059773990733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118265399854794039849327155 177398099782191059773990733)
          ·
            refine ⟨66524287418321647415246525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177398099782191059773990733 66524287418321647415246525)
            ·
              refine ⟨24946607781870617780717447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66524287418321647415246525 24946607781870617780717447)
              ·
                refine ⟨37419911672805926671076171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24946607781870617780717447 37419911672805926671076171)
                ·
                  refine ⟨56129867509208890006614257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37419911672805926671076171 56129867509208890006614257)
                  ·
                    refine ⟨42097400631906667504960693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56129867509208890006614257 42097400631906667504960693)
                    ·
                      refine ⟨3946631309241250078590065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42097400631906667504960693 3946631309241250078590065)
                      ·
                        rfl

theorem cell23_7686037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_7686037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686037 prefixEnd_7686037 := by exact prefixLift 7686037
  have htrace : WordTrace (prefixWord ++ tailWord_7686037) baseStart_7686037 baseEnd_7686037 := by
    simpa [prefixWord, tailWord_7686037, baseEnd_7686037] using wordTrace_append hprefix tailTrace_7686037
  have hstable : (prefixWord ++ tailWord_7686037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686037).length < 2 ^ (prefixWord ++ tailWord_7686037).sum := by decide
  have hdescent : baseEnd_7686037 < baseStart_7686037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686091 : List Nat := [1, 1, 1, 1, 3, 4, 3, 4, 1, 4]
def baseStart_7686091 : Nat := 118140960795 + 7686091 * 2 ^ 59
def prefixEnd_7686091 : Nat := 4983230072969 + 3 ^ 40 * 7686091 * 2
def baseEnd_7686091 : Nat := 1315553012398864289104939

theorem tailTrace_7686091 : CollatzResearch.WordTrace tailWord_7686091 prefixEnd_7686091 1315553012398864289104939 := by
  unfold tailWord_7686091
  simp only [CollatzResearch.WordTrace]
  refine ⟨280334769197612461680130127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186889846131741641120086751 280334769197612461680130127)
  ·
    refine ⟨420502153796418692520195191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280334769197612461680130127 420502153796418692520195191)
    ·
      refine ⟨630753230694628038780292787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420502153796418692520195191 630753230694628038780292787)
      ·
        refine ⟨946129846041942058170439181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630753230694628038780292787 946129846041942058170439181)
        ·
          refine ⟨354798692265728271813914693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 946129846041942058170439181 354798692265728271813914693)
          ·
            refine ⟨66524754799824050965109005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354798692265728271813914693 66524754799824050965109005)
            ·
              refine ⟨24946783049934019111915877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66524754799824050965109005 24946783049934019111915877)
              ·
                refine ⟨4677521821862628583484227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24946783049934019111915877 4677521821862628583484227)
                ·
                  refine ⟨7016282732793942875226341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4677521821862628583484227 7016282732793942875226341)
                  ·
                    refine ⟨1315553012398864289104939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7016282732793942875226341 1315553012398864289104939)
                    ·
                      rfl

theorem cell23_7686091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 1, 4].length) (baseStart_7686091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686091 prefixEnd_7686091 := by exact prefixLift 7686091
  have htrace : WordTrace (prefixWord ++ tailWord_7686091) baseStart_7686091 baseEnd_7686091 := by
    simpa [prefixWord, tailWord_7686091, baseEnd_7686091] using wordTrace_append hprefix tailTrace_7686091
  have hstable : (prefixWord ++ tailWord_7686091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686091).length < 2 ^ (prefixWord ++ tailWord_7686091).sum := by decide
  have hdescent : baseEnd_7686091 < baseStart_7686091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686098 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_7686098 : Nat := 118140960795 + 7686098 * 2 ^ 59
def prefixEnd_7686098 : Nat := 4983230072969 + 3 ^ 40 * 7686098 * 2
def baseEnd_7686098 : Nat := 3946662631561174339927285

theorem tailTrace_7686098 : CollatzResearch.WordTrace tailWord_7686098 prefixEnd_7686098 3946662631561174339927285 := by
  unfold tailWord_7686098
  simp only [CollatzResearch.WordTrace]
  refine ⟨70083756127146775468908737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186890016339058067917089965 70083756127146775468908737)
  ·
    refine ⟨52562817095360081601681553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70083756127146775468908737 52562817095360081601681553)
    ·
      refine ⟨39422112821520061201261165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52562817095360081601681553 39422112821520061201261165)
      ·
        refine ⟨14783292308070022950472937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39422112821520061201261165 14783292308070022950472937)
        ·
          refine ⟨11087469231052517212854703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14783292308070022950472937 11087469231052517212854703)
          ·
            refine ⟨16631203846578775819282055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11087469231052517212854703 16631203846578775819282055)
            ·
              refine ⟨24946805769868163728923083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16631203846578775819282055 24946805769868163728923083)
              ·
                refine ⟨37420208654802245593384625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24946805769868163728923083 37420208654802245593384625)
                ·
                  refine ⟨28065156491101684195038469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37420208654802245593384625 28065156491101684195038469)
                  ·
                    refine ⟨5262216842081565786569713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28065156491101684195038469 5262216842081565786569713)
                    ·
                      refine ⟨3946662631561174339927285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262216842081565786569713 3946662631561174339927285)
                      ·
                        rfl

theorem cell23_7686098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_7686098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686098 prefixEnd_7686098 := by exact prefixLift 7686098
  have htrace : WordTrace (prefixWord ++ tailWord_7686098) baseStart_7686098 baseEnd_7686098 := by
    simpa [prefixWord, tailWord_7686098, baseEnd_7686098] using wordTrace_append hprefix tailTrace_7686098
  have hstable : (prefixWord ++ tailWord_7686098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686098).length < 2 ^ (prefixWord ++ tailWord_7686098).sum := by decide
  have hdescent : baseEnd_7686098 < baseStart_7686098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686141 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 2, 3, 2]
def baseStart_7686141 : Nat := 118140960795 + 7686141 * 2 ^ 59
def prefixEnd_7686141 : Nat := 4983230072969 + 3 ^ 40 * 7686141 * 2
def baseEnd_7686141 : Nat := 3946684711229317671689587

theorem tailTrace_7686141 : CollatzResearch.WordTrace tailWord_7686141 prefixEnd_7686141 3946684711229317671689587 := by
  unfold tailWord_7686141
  simp only [CollatzResearch.WordTrace]
  refine ⟨280336592847431320219450277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186891061898287546812966851 280336592847431320219450277)
  ·
    refine ⟨52563111158893372541146927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280336592847431320219450277 52563111158893372541146927)
    ·
      refine ⟨78844666738340058811720391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52563111158893372541146927 78844666738340058811720391)
      ·
        refine ⟨118267000107510088217580587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78844666738340058811720391 118267000107510088217580587)
        ·
          refine ⟨177400500161265132326370881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118267000107510088217580587 177400500161265132326370881)
          ·
            refine ⟨133050375120948849244778161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177400500161265132326370881 133050375120948849244778161)
            ·
              refine ⟨99787781340711636933583621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133050375120948849244778161 99787781340711636933583621)
              ·
                refine ⟨18710209001383431925046929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99787781340711636933583621 18710209001383431925046929)
                ·
                  refine ⟨14032656751037573943785197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18710209001383431925046929 14032656751037573943785197)
                  ·
                    refine ⟨5262246281639090228919449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14032656751037573943785197 5262246281639090228919449)
                    ·
                      refine ⟨3946684711229317671689587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262246281639090228919449 3946684711229317671689587)
                      ·
                        rfl

theorem cell23_7686141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_7686141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686141 prefixEnd_7686141 := by exact prefixLift 7686141
  have htrace : WordTrace (prefixWord ++ tailWord_7686141) baseStart_7686141 baseEnd_7686141 := by
    simpa [prefixWord, tailWord_7686141, baseEnd_7686141] using wordTrace_append hprefix tailTrace_7686141
  have hstable : (prefixWord ++ tailWord_7686141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686141).length < 2 ^ (prefixWord ++ tailWord_7686141).sum := by decide
  have hdescent : baseEnd_7686141 < baseStart_7686141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686147 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 3, 6]
def baseStart_7686147 : Nat := 118140960795 + 7686147 * 2 ^ 59
def prefixEnd_7686147 : Nat := 4983230072969 + 3 ^ 40 * 7686147 * 2
def baseEnd_7686147 : Nat := 1315562597371081549404853

theorem tailTrace_7686147 : CollatzResearch.WordTrace tailWord_7686147 prefixEnd_7686147 1315562597371081549404853 := by
  unfold tailWord_7686147
  simp only [CollatzResearch.WordTrace]
  refine ⟨280336811685409583244168695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186891207790273055496112463 280336811685409583244168695)
  ·
    refine ⟨420505217528114374866253043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280336811685409583244168695 420505217528114374866253043)
    ·
      refine ⟨630757826292171562299379565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420505217528114374866253043 630757826292171562299379565)
      ·
        refine ⟨236534184859564335862267337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 630757826292171562299379565 236534184859564335862267337)
        ·
          refine ⟨177400638644673251896700503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236534184859564335862267337 177400638644673251896700503)
          ·
            refine ⟨266100957967009877845050755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177400638644673251896700503 266100957967009877845050755)
            ·
              refine ⟨399151436950514816767576133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266100957967009877845050755 399151436950514816767576133)
              ·
                refine ⟨74840894428221528143920525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399151436950514816767576133 74840894428221528143920525)
                ·
                  refine ⟨28065335410583073053970197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74840894428221528143920525 28065335410583073053970197)
                  ·
                    refine ⟨1315562597371081549404853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28065335410583073053970197 1315562597371081549404853)
                    ·
                      rfl

theorem cell23_7686147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 6].length) (baseStart_7686147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686147 prefixEnd_7686147 := by exact prefixLift 7686147
  have htrace : WordTrace (prefixWord ++ tailWord_7686147) baseStart_7686147 baseEnd_7686147 := by
    simpa [prefixWord, tailWord_7686147, baseEnd_7686147] using wordTrace_append hprefix tailTrace_7686147
  have hstable : (prefixWord ++ tailWord_7686147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686147).length < 2 ^ (prefixWord ++ tailWord_7686147).sum := by decide
  have hdescent : baseEnd_7686147 < baseStart_7686147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686171 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 5, 2, 2]
def baseStart_7686171 : Nat := 118140960795 + 7686171 * 2 ^ 59
def prefixEnd_7686171 : Nat := 4983230072969 + 3 ^ 40 * 7686171 * 2
def baseEnd_7686171 : Nat := 3946700115648952554314449

theorem tailTrace_7686171 : CollatzResearch.WordTrace tailWord_7686171 prefixEnd_7686171 3946700115648952554314449 := by
  unfold tailWord_7686171
  simp only [CollatzResearch.WordTrace]
  refine ⟨280337687037322635343042367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186891791358215090228694911 280337687037322635343042367)
  ·
    refine ⟨420506530555983953014563551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280337687037322635343042367 420506530555983953014563551)
    ·
      refine ⟨630759795833975929521845327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420506530555983953014563551 630759795833975929521845327)
      ·
        refine ⟨946139693750963894282767991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630759795833975929521845327 946139693750963894282767991)
        ·
          refine ⟨1419209540626445841424151987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946139693750963894282767991 1419209540626445841424151987)
          ·
            refine ⟨2128814310939668762136227981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419209540626445841424151987 2128814310939668762136227981)
            ·
              refine ⟨798305366602375785801085493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2128814310939668762136227981 798305366602375785801085493)
              ·
                refine ⟨74841128118972729918851765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 798305366602375785801085493 74841128118972729918851765)
                ·
                  refine ⟨7016355761153693429892353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74841128118972729918851765 7016355761153693429892353)
                  ·
                    refine ⟨5262266820865270072419265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7016355761153693429892353 5262266820865270072419265)
                    ·
                      refine ⟨3946700115648952554314449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262266820865270072419265 3946700115648952554314449)
                      ·
                        rfl

theorem cell23_7686171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 2, 2].length) (baseStart_7686171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686171 prefixEnd_7686171 := by exact prefixLift 7686171
  have htrace : WordTrace (prefixWord ++ tailWord_7686171) baseStart_7686171 baseEnd_7686171 := by
    simpa [prefixWord, tailWord_7686171, baseEnd_7686171] using wordTrace_append hprefix tailTrace_7686171
  have hstable : (prefixWord ++ tailWord_7686171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686171).length < 2 ^ (prefixWord ++ tailWord_7686171).sum := by decide
  have hdescent : baseEnd_7686171 < baseStart_7686171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686194 : List Nat := [3, 2, 1, 1, 2, 5, 9]
def baseStart_7686194 : Nat := 118140960795 + 7686194 * 2 ^ 59
def prefixEnd_7686194 : Nat := 4983230072969 + 3 ^ 40 * 7686194 * 2
def baseEnd_7686194 : Nat := 48724838588938345238603

theorem tailTrace_7686194 : CollatzResearch.WordTrace tailWord_7686194 prefixEnd_7686194 48724838588938345238603 := by
  unfold tailWord_7686194
  simp only [CollatzResearch.WordTrace]
  refine ⟨70084631479059827567782409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186892350610826206847419757 70084631479059827567782409)
  ·
    refine ⟨52563473609294870675836807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70084631479059827567782409 52563473609294870675836807)
    ·
      refine ⟨78845210413942306013755211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52563473609294870675836807 78845210413942306013755211)
      ·
        refine ⟨118267815620913459020632817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78845210413942306013755211 118267815620913459020632817)
        ·
          refine ⟨88700861715685094265474613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118267815620913459020632817 88700861715685094265474613)
          ·
            refine ⟨8315705785845477587388245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88700861715685094265474613 8315705785845477587388245)
            ·
              refine ⟨48724838588938345238603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8315705785845477587388245 48724838588938345238603)
              ·
                rfl

theorem cell23_7686194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 9].length) (baseStart_7686194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686194 prefixEnd_7686194 := by exact prefixLift 7686194
  have htrace : WordTrace (prefixWord ++ tailWord_7686194) baseStart_7686194 baseEnd_7686194 := by
    simpa [prefixWord, tailWord_7686194, baseEnd_7686194] using wordTrace_append hprefix tailTrace_7686194
  have hstable : (prefixWord ++ tailWord_7686194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686194).length < 2 ^ (prefixWord ++ tailWord_7686194).sum := by decide
  have hdescent : baseEnd_7686194 < baseStart_7686194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686198 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_7686198 : Nat := 118140960795 + 7686198 * 2 ^ 59
def prefixEnd_7686198 : Nat := 4983230072969 + 3 ^ 40 * 7686198 * 2
def baseEnd_7686198 : Nat := 1315571326542207982892275

theorem tailTrace_7686198 : CollatzResearch.WordTrace tailWord_7686198 prefixEnd_7686198 1315571326542207982892275 := by
  unfold tailWord_7686198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17521166988014051184642203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186892447872149879302850165 17521166988014051184642203)
  ·
    refine ⟨26281750482021076776963305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17521166988014051184642203 26281750482021076776963305)
    ·
      refine ⟨19711312861515807582722479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26281750482021076776963305 19711312861515807582722479)
      ·
        refine ⟨29566969292273711374083719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19711312861515807582722479 29566969292273711374083719)
        ·
          refine ⟨44350453938410567061125579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29566969292273711374083719 44350453938410567061125579)
          ·
            refine ⟨66525680907615850591688369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44350453938410567061125579 66525680907615850591688369)
            ·
              refine ⟨49894260680711887943766277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66525680907615850591688369 49894260680711887943766277)
              ·
                refine ⟨9355173877633478989456177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49894260680711887943766277 9355173877633478989456177)
                ·
                  refine ⟨7016380408225109242092133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9355173877633478989456177 7016380408225109242092133)
                  ·
                    refine ⟨1315571326542207982892275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7016380408225109242092133 1315571326542207982892275)
                    ·
                      rfl

theorem cell23_7686198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_7686198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686198 prefixEnd_7686198 := by exact prefixLift 7686198
  have htrace : WordTrace (prefixWord ++ tailWord_7686198) baseStart_7686198 baseEnd_7686198 := by
    simpa [prefixWord, tailWord_7686198, baseEnd_7686198] using wordTrace_append hprefix tailTrace_7686198
  have hstable : (prefixWord ++ tailWord_7686198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686198).length < 2 ^ (prefixWord ++ tailWord_7686198).sum := by decide
  have hdescent : baseEnd_7686198 < baseStart_7686198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686242 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7686242 : Nat := 118140960795 + 7686242 * 2 ^ 59
def prefixEnd_7686242 : Nat := 4983230072969 + 3 ^ 40 * 7686242 * 2
def baseEnd_7686242 : Nat := 3946736572775421776526623

theorem tailTrace_7686242 : CollatzResearch.WordTrace tailWord_7686242 prefixEnd_7686242 3946736572775421776526623 := by
  unfold tailWord_7686242
  simp only [CollatzResearch.WordTrace]
  refine ⟨70085069155016353617219245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186893517746710276312584653 70085069155016353617219245)
  ·
    refine ⟨26281900933131132606457217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70085069155016353617219245 26281900933131132606457217)
    ·
      refine ⟨19711425699848349454842913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26281900933131132606457217 19711425699848349454842913)
      ·
        refine ⟨14783569274886262091132185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19711425699848349454842913 14783569274886262091132185)
        ·
          refine ⟨11087676956164696568349139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14783569274886262091132185 11087676956164696568349139)
          ·
            refine ⟨16631515434247044852523709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11087676956164696568349139 16631515434247044852523709)
            ·
              refine ⟨6236818287842641819696391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16631515434247044852523709 6236818287842641819696391)
              ·
                refine ⟨9355227431763962729544587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6236818287842641819696391 9355227431763962729544587)
                ·
                  refine ⟨14032841147645944094316881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9355227431763962729544587 14032841147645944094316881)
                  ·
                    refine ⟨10524630860734458070737661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14032841147645944094316881 10524630860734458070737661)
                    ·
                      refine ⟨3946736572775421776526623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10524630860734458070737661 3946736572775421776526623)
                      ·
                        rfl

theorem cell23_7686242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7686242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686242 prefixEnd_7686242 := by exact prefixLift 7686242
  have htrace : WordTrace (prefixWord ++ tailWord_7686242) baseStart_7686242 baseEnd_7686242 := by
    simpa [prefixWord, tailWord_7686242, baseEnd_7686242] using wordTrace_append hprefix tailTrace_7686242
  have hstable : (prefixWord ++ tailWord_7686242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686242).length < 2 ^ (prefixWord ++ tailWord_7686242).sum := by decide
  have hdescent : baseEnd_7686242 < baseStart_7686242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686344 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 1, 10]
def baseStart_7686344 : Nat := 118140960795 + 7686344 * 2 ^ 59
def prefixEnd_7686344 : Nat := 4983230072969 + 3 ^ 40 * 7686344 * 2
def baseEnd_7686344 : Nat := 1315596315934060125817051

theorem tailTrace_7686344 : CollatzResearch.WordTrace tailWord_7686344 prefixEnd_7686344 1315596315934060125817051 := by
  unfold tailWord_7686344
  simp only [CollatzResearch.WordTrace]
  refine ⟨140171998432847942944545043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186895997910463923926060057 140171998432847942944545043)
  ·
    refine ⟨210257997649271914416817565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140171998432847942944545043 210257997649271914416817565)
    ·
      refine ⟨78846749118476967906306587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210257997649271914416817565 78846749118476967906306587)
      ·
        refine ⟨118270123677715451859459881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78846749118476967906306587 118270123677715451859459881)
        ·
          refine ⟨88702592758286588894594911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118270123677715451859459881 88702592758286588894594911)
          ·
            refine ⟨133053889137429883341892367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88702592758286588894594911 133053889137429883341892367)
            ·
              refine ⟨199580833706144825012838551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133053889137429883341892367 199580833706144825012838551)
              ·
                refine ⟨299371250559217237519257827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199580833706144825012838551 299371250559217237519257827)
                ·
                  refine ⟨449056875838825856278886741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299371250559217237519257827 449056875838825856278886741)
                  ·
                    refine ⟨1315596315934060125817051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 449056875838825856278886741 1315596315934060125817051)
                    ·
                      rfl

theorem cell23_7686344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_7686344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686344 prefixEnd_7686344 := by exact prefixLift 7686344
  have htrace : WordTrace (prefixWord ++ tailWord_7686344) baseStart_7686344 baseEnd_7686344 := by
    simpa [prefixWord, tailWord_7686344, baseEnd_7686344] using wordTrace_append hprefix tailTrace_7686344
  have hstable : (prefixWord ++ tailWord_7686344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686344).length < 2 ^ (prefixWord ++ tailWord_7686344).sum := by decide
  have hdescent : baseEnd_7686344 < baseStart_7686344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686351 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 4]
def baseStart_7686351 : Nat := 118140960795 + 7686351 * 2 ^ 59
def prefixEnd_7686351 : Nat := 4983230072969 + 3 ^ 40 * 7686351 * 2
def baseEnd_7686351 : Nat := 3946792542166761850063621

theorem tailTrace_7686351 : CollatzResearch.WordTrace tailWord_7686351 prefixEnd_7686351 3946792542166761850063621 := by
  unfold tailWord_7686351
  simp only [CollatzResearch.WordTrace]
  refine ⟨280344252176670526084594907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186896168117780350723063271 280344252176670526084594907)
  ·
    refine ⟨420516378265005789126892361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280344252176670526084594907 420516378265005789126892361)
    ·
      refine ⟨315387283698754341845169271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420516378265005789126892361 315387283698754341845169271)
      ·
        refine ⟨473080925548131512767753907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315387283698754341845169271 473080925548131512767753907)
        ·
          refine ⟨709621388322197269151630861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473080925548131512767753907 709621388322197269151630861)
          ·
            refine ⟨266108020620823975931861573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 709621388322197269151630861 266108020620823975931861573)
            ·
              refine ⟨49895253866404495487224045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266108020620823975931861573 49895253866404495487224045)
              ·
                refine ⟨18710720199901685807709017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49895253866404495487224045 18710720199901685807709017)
                ·
                  refine ⟨14033040149926264355781763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18710720199901685807709017 14033040149926264355781763)
                  ·
                    refine ⟨21049560224889396533672645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14033040149926264355781763 21049560224889396533672645)
                    ·
                      refine ⟨3946792542166761850063621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21049560224889396533672645 3946792542166761850063621)
                      ·
                        rfl

theorem cell23_7686351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_7686351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686351 prefixEnd_7686351 := by exact prefixLift 7686351
  have htrace : WordTrace (prefixWord ++ tailWord_7686351) baseStart_7686351 baseEnd_7686351 := by
    simpa [prefixWord, tailWord_7686351, baseEnd_7686351] using wordTrace_append hprefix tailTrace_7686351
  have hstable : (prefixWord ++ tailWord_7686351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686351).length < 2 ^ (prefixWord ++ tailWord_7686351).sum := by decide
  have hdescent : baseEnd_7686351 < baseStart_7686351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686361 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 5, 4]
def baseStart_7686361 : Nat := 118140960795 + 7686361 * 2 ^ 59
def prefixEnd_7686361 : Nat := 4983230072969 + 3 ^ 40 * 7686361 * 2
def baseEnd_7686361 : Nat := 1315599225657768936979525

theorem tailTrace_7686361 : CollatzResearch.WordTrace tailWord_7686361 prefixEnd_7686361 1315599225657768936979525 := by
  unfold tailWord_7686361
  simp only [CollatzResearch.WordTrace]
  refine ⟨280344616906634297792458937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186896411271089531861639291 280344616906634297792458937)
  ·
    refine ⟨210258462679975723344344203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280344616906634297792458937 210258462679975723344344203)
    ·
      refine ⟨315387694019963585016516305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210258462679975723344344203 315387694019963585016516305)
      ·
        refine ⟨236540770514972688762387229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315387694019963585016516305 236540770514972688762387229)
        ·
          refine ⟨88702788943114758285895211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236540770514972688762387229 88702788943114758285895211)
          ·
            refine ⟨133054183414672137428842817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88702788943114758285895211 133054183414672137428842817)
            ·
              refine ⟨99790637561004103071632113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133054183414672137428842817 99790637561004103071632113)
              ·
                refine ⟨74842978170753077303724085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99790637561004103071632113 74842978170753077303724085)
                ·
                  refine ⟨7016529203508100997224133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74842978170753077303724085 7016529203508100997224133)
                  ·
                    refine ⟨1315599225657768936979525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7016529203508100997224133 1315599225657768936979525)
                    ·
                      rfl

theorem cell23_7686361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 4].length) (baseStart_7686361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686361 prefixEnd_7686361 := by exact prefixLift 7686361
  have htrace : WordTrace (prefixWord ++ tailWord_7686361) baseStart_7686361 baseEnd_7686361 := by
    simpa [prefixWord, tailWord_7686361, baseEnd_7686361] using wordTrace_append hprefix tailTrace_7686361
  have hstable : (prefixWord ++ tailWord_7686361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686361).length < 2 ^ (prefixWord ++ tailWord_7686361).sum := by decide
  have hdescent : baseEnd_7686361 < baseStart_7686361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686428 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_7686428 : Nat := 118140960795 + 7686428 * 2 ^ 59
def prefixEnd_7686428 : Nat := 4983230072969 + 3 ^ 40 * 7686428 * 2
def baseEnd_7686428 : Nat := 3946832080177158048800767

theorem tailTrace_7686428 : CollatzResearch.WordTrace tailWord_7686428 prefixEnd_7686428 3946832080177158048800767 := by
  unfold tailWord_7686428
  simp only [CollatzResearch.WordTrace]
  refine ⟨140173530298695784117573969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186898040398261045490098625 140173530298695784117573969)
  ·
    refine ⟨105130147724021838088180477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140173530298695784117573969 105130147724021838088180477)
    ·
      refine ⟨39423805396508189283067679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105130147724021838088180477 39423805396508189283067679)
      ·
        refine ⟨59135708094762283924601519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39423805396508189283067679 59135708094762283924601519)
        ·
          refine ⟨88703562142143425886902279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59135708094762283924601519 88703562142143425886902279)
          ·
            refine ⟨133055343213215138830353419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88703562142143425886902279 133055343213215138830353419)
            ·
              refine ⟨199583014819822708245530129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133055343213215138830353419 199583014819822708245530129)
              ·
                refine ⟨149687261114867031184147597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199583014819822708245530129 149687261114867031184147597)
                ·
                  refine ⟨56132722918075136694055349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149687261114867031184147597 56132722918075136694055349)
                  ·
                    refine ⟨5262442773569544065067689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56132722918075136694055349 5262442773569544065067689)
                    ·
                      refine ⟨3946832080177158048800767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262442773569544065067689 3946832080177158048800767)
                      ·
                        rfl

theorem cell23_7686428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_7686428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686428 prefixEnd_7686428 := by exact prefixLift 7686428
  have htrace : WordTrace (prefixWord ++ tailWord_7686428) baseStart_7686428 baseEnd_7686428 := by
    simpa [prefixWord, tailWord_7686428, baseEnd_7686428] using wordTrace_append hprefix tailTrace_7686428
  have hstable : (prefixWord ++ tailWord_7686428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686428).length < 2 ^ (prefixWord ++ tailWord_7686428).sum := by decide
  have hdescent : baseEnd_7686428 < baseStart_7686428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686452 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_7686452 : Nat := 118140960795 + 7686452 * 2 ^ 59
def prefixEnd_7686452 : Nat := 4983230072969 + 3 ^ 40 * 7686452 * 2
def baseEnd_7686452 : Nat := 3946844403712865954900657

theorem tailTrace_7686452 : CollatzResearch.WordTrace tailWord_7686452 prefixEnd_7686452 3946844403712865954900657 := by
  unfold tailWord_7686452
  simp only [CollatzResearch.WordTrace]
  refine ⟨140173967974652310167010805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186898623966203080222681073 140173967974652310167010805)
  ·
    refine ⟨13141309497623654078157263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140173967974652310167010805 13141309497623654078157263)
    ·
      refine ⟨19711964246435481117235895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13141309497623654078157263 19711964246435481117235895)
      ·
        refine ⟨29567946369653221675853843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19711964246435481117235895 29567946369653221675853843)
        ·
          refine ⟨44351919554479832513780765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29567946369653221675853843 44351919554479832513780765)
          ·
            refine ⟨16631969832929937192667787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44351919554479832513780765 16631969832929937192667787)
            ·
              refine ⟨24947954749394905789001681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16631969832929937192667787 24947954749394905789001681)
              ·
                refine ⟨18710966062046179341751261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24947954749394905789001681 18710966062046179341751261)
                ·
                  refine ⟨7016612273267317253156723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18710966062046179341751261 7016612273267317253156723)
                  ·
                    refine ⟨10524918409900975879735085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7016612273267317253156723 10524918409900975879735085)
                    ·
                      refine ⟨3946844403712865954900657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10524918409900975879735085 3946844403712865954900657)
                      ·
                        rfl

theorem cell23_7686452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_7686452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686452 prefixEnd_7686452 := by exact prefixLift 7686452
  have htrace : WordTrace (prefixWord ++ tailWord_7686452) baseStart_7686452 baseEnd_7686452 := by
    simpa [prefixWord, tailWord_7686452, baseEnd_7686452] using wordTrace_append hprefix tailTrace_7686452
  have hstable : (prefixWord ++ tailWord_7686452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686452).length < 2 ^ (prefixWord ++ tailWord_7686452).sum := by decide
  have hdescent : baseEnd_7686452 < baseStart_7686452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686458 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_7686458 : Nat := 118140960795 + 7686458 * 2 ^ 59
def prefixEnd_7686458 : Nat := 4983230072969 + 3 ^ 40 * 7686458 * 2
def baseEnd_7686458 : Nat := 3946847484596792931425629

theorem tailTrace_7686458 : CollatzResearch.WordTrace tailWord_7686458 prefixEnd_7686458 3946847484596792931425629 := by
  unfold tailWord_7686458
  simp only [CollatzResearch.WordTrace]
  refine ⟨70087038696820720839685007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186898769858188588905826685 70087038696820720839685007)
  ·
    refine ⟨105130558045231081259527511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70087038696820720839685007 105130558045231081259527511)
    ·
      refine ⟨157695837067846621889291267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105130558045231081259527511 157695837067846621889291267)
      ·
        refine ⟨236543755601769932833936901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157695837067846621889291267 236543755601769932833936901)
        ·
          refine ⟨44351954175331862406363169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236543755601769932833936901 44351954175331862406363169)
          ·
            refine ⟨33263965631498896804772377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44351954175331862406363169 33263965631498896804772377)
            ·
              refine ⟨24947974223624172603579283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33263965631498896804772377 24947974223624172603579283)
              ·
                refine ⟨37421961335436258905368925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24947974223624172603579283 37421961335436258905368925)
                ·
                  refine ⟨14033235500788597089513347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37421961335436258905368925 14033235500788597089513347)
                  ·
                    refine ⟨21049853251182895634270021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14033235500788597089513347 21049853251182895634270021)
                    ·
                      refine ⟨3946847484596792931425629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21049853251182895634270021 3946847484596792931425629)
                      ·
                        rfl

theorem cell23_7686458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_7686458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686458 prefixEnd_7686458 := by exact prefixLift 7686458
  have htrace : WordTrace (prefixWord ++ tailWord_7686458) baseStart_7686458 baseEnd_7686458 := by
    simpa [prefixWord, tailWord_7686458, baseEnd_7686458] using wordTrace_append hprefix tailTrace_7686458
  have hstable : (prefixWord ++ tailWord_7686458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686458).length < 2 ^ (prefixWord ++ tailWord_7686458).sum := by decide
  have hdescent : baseEnd_7686458 < baseStart_7686458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686462 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_7686462 : Nat := 118140960795 + 7686462 * 2 ^ 59
def prefixEnd_7686462 : Nat := 4983230072969 + 3 ^ 40 * 7686462 * 2
def baseEnd_7686462 : Nat := 3946849538519410915775611

theorem tailTrace_7686462 : CollatzResearch.WordTrace tailWord_7686462 prefixEnd_7686462 3946849538519410915775611 := by
  unfold tailWord_7686462
  simp only [CollatzResearch.WordTrace]
  refine ⟨35043537584908549005235705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186898867119512261361257093 35043537584908549005235705)
  ·
    refine ⟨26282653188681411753926779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35043537584908549005235705 26282653188681411753926779)
    ·
      refine ⟨39423979783022117630890169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26282653188681411753926779 39423979783022117630890169)
      ·
        refine ⟨29567984837266588223167627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39423979783022117630890169 29567984837266588223167627)
        ·
          refine ⟨44351977255899882334751441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29567984837266588223167627 44351977255899882334751441)
          ·
            refine ⟨33263982941924911751063581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44351977255899882334751441 33263982941924911751063581)
            ·
              refine ⟨12473993603221841906648843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33263982941924911751063581 12473993603221841906648843)
              ·
                refine ⟨18710990404832762859973265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12473993603221841906648843 18710990404832762859973265)
                ·
                  refine ⟨14033242803624572144979949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18710990404832762859973265 14033242803624572144979949)
                  ·
                    refine ⟨5262466051359214554367481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14033242803624572144979949 5262466051359214554367481)
                    ·
                      refine ⟨3946849538519410915775611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262466051359214554367481 3946849538519410915775611)
                      ·
                        rfl

theorem cell23_7686462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_7686462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686462 prefixEnd_7686462 := by exact prefixLift 7686462
  have htrace : WordTrace (prefixWord ++ tailWord_7686462) baseStart_7686462 baseEnd_7686462 := by
    simpa [prefixWord, tailWord_7686462, baseEnd_7686462] using wordTrace_append hprefix tailTrace_7686462
  have hstable : (prefixWord ++ tailWord_7686462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686462).length < 2 ^ (prefixWord ++ tailWord_7686462).sum := by decide
  have hdescent : baseEnd_7686462 < baseStart_7686462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686478 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_7686478 : Nat := 118140960795 + 7686478 * 2 ^ 59
def prefixEnd_7686478 : Nat := 4983230072969 + 3 ^ 40 * 7686478 * 2
def baseEnd_7686478 : Nat := 3946857754209882853175537

theorem tailTrace_7686478 : CollatzResearch.WordTrace tailWord_7686478 prefixEnd_7686478 3946857754209882853175537 := by
  unfold tailWord_7686478
  simp only [CollatzResearch.WordTrace]
  refine ⟨35043610530901303346808511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186899256164806951182978725 35043610530901303346808511)
  ·
    refine ⟨52565415796351955020212767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35043610530901303346808511 52565415796351955020212767)
    ·
      refine ⟨78848123694527932530319151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52565415796351955020212767 78848123694527932530319151)
      ·
        refine ⟨118272185541791898795478727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78848123694527932530319151 118272185541791898795478727)
        ·
          refine ⟨177408278312687848193218091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118272185541791898795478727 177408278312687848193218091)
          ·
            refine ⟨266112417469031772289827137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177408278312687848193218091 266112417469031772289827137)
            ·
              refine ⟨199584313101773829217370353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266112417469031772289827137 199584313101773829217370353)
              ·
                refine ⟨149688234826330371913027765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199584313101773829217370353 149688234826330371913027765)
                ·
                  refine ⟨14033272014968472366846353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149688234826330371913027765 14033272014968472366846353)
                  ·
                    refine ⟨10524954011226354275134765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14033272014968472366846353 10524954011226354275134765)
                    ·
                      refine ⟨3946857754209882853175537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10524954011226354275134765 3946857754209882853175537)
                      ·
                        rfl

theorem cell23_7686478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_7686478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686478 prefixEnd_7686478 := by exact prefixLift 7686478
  have htrace : WordTrace (prefixWord ++ tailWord_7686478) baseStart_7686478 baseEnd_7686478 := by
    simpa [prefixWord, tailWord_7686478, baseEnd_7686478] using wordTrace_append hprefix tailTrace_7686478
  have hstable : (prefixWord ++ tailWord_7686478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686478).length < 2 ^ (prefixWord ++ tailWord_7686478).sum := by decide
  have hdescent : baseEnd_7686478 < baseStart_7686478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686481 : List Nat := [1, 2, 2, 1, 4, 3, 10]
def baseStart_7686481 : Nat := 118140960795 + 7686481 * 2 ^ 59
def prefixEnd_7686481 : Nat := 4983230072969 + 3 ^ 40 * 7686481 * 2
def baseEnd_7686481 : Nat := 48726657958664769647383

theorem tailTrace_7686481 : CollatzResearch.WordTrace tailWord_7686481 prefixEnd_7686481 48726657958664769647383 := by
  unfold tailWord_7686481
  simp only [CollatzResearch.WordTrace]
  refine ⟨280348993666199558286827297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186899329110799705524551531 280348993666199558286827297)
  ·
    refine ⟨210261745249649668715120473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280348993666199558286827297 210261745249649668715120473)
    ·
      refine ⟨157696308937237251536340355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210261745249649668715120473 157696308937237251536340355)
      ·
        refine ⟨236544463405855877304510533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157696308937237251536340355 236544463405855877304510533)
        ·
          refine ⟨44352086888597976994595725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236544463405855877304510533 44352086888597976994595725)
          ·
            refine ⟨16632032583224241372973397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44352086888597976994595725 16632032583224241372973397)
            ·
              refine ⟨48726657958664769647383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16632032583224241372973397 48726657958664769647383)
              ·
                rfl

theorem cell23_7686481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 10].length) (baseStart_7686481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686481 prefixEnd_7686481 := by exact prefixLift 7686481
  have htrace : WordTrace (prefixWord ++ tailWord_7686481) baseStart_7686481 baseEnd_7686481 := by
    simpa [prefixWord, tailWord_7686481, baseEnd_7686481] using wordTrace_append hprefix tailTrace_7686481
  have hstable : (prefixWord ++ tailWord_7686481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686481).length < 2 ^ (prefixWord ++ tailWord_7686481).sum := by decide
  have hdescent : baseEnd_7686481 < baseStart_7686481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686485 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 4, 4]
def baseStart_7686485 : Nat := 118140960795 + 7686485 * 2 ^ 59
def prefixEnd_7686485 : Nat := 4983230072969 + 3 ^ 40 * 7686485 * 2
def baseEnd_7686485 : Nat := 1315620449524821441929335

theorem tailTrace_7686485 : CollatzResearch.WordTrace tailWord_7686485 prefixEnd_7686485 1315620449524821441929335 := by
  unfold tailWord_7686485
  simp only [CollatzResearch.WordTrace]
  refine ⟨280349139558185066969972909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186899426372123377979981939 280349139558185066969972909)
  ·
    refine ⟨105130927334319400113739841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280349139558185066969972909 105130927334319400113739841)
    ·
      refine ⟨78848195500739550085304881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105130927334319400113739841 78848195500739550085304881)
      ·
        refine ⟨59136146625554662563978661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78848195500739550085304881 59136146625554662563978661)
        ·
          refine ⟨11088027492291499230745999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59136146625554662563978661 11088027492291499230745999)
          ·
            refine ⟨16632041238437248846118999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11088027492291499230745999 16632041238437248846118999)
            ·
              refine ⟨24948061857655873269178499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16632041238437248846118999 24948061857655873269178499)
              ·
                refine ⟨37422092786483809903767749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24948061857655873269178499 37422092786483809903767749)
                ·
                  refine ⟨7016642397465714356956453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37422092786483809903767749 7016642397465714356956453)
                  ·
                    refine ⟨1315620449524821441929335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7016642397465714356956453 1315620449524821441929335)
                    ·
                      rfl

theorem cell23_7686485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_7686485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686485 prefixEnd_7686485 := by exact prefixLift 7686485
  have htrace : WordTrace (prefixWord ++ tailWord_7686485) baseStart_7686485 baseEnd_7686485 := by
    simpa [prefixWord, tailWord_7686485, baseEnd_7686485] using wordTrace_append hprefix tailTrace_7686485
  have hstable : (prefixWord ++ tailWord_7686485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686485).length < 2 ^ (prefixWord ++ tailWord_7686485).sum := by decide
  have hdescent : baseEnd_7686485 < baseStart_7686485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686525 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_7686525 : Nat := 118140960795 + 7686525 * 2 ^ 59
def prefixEnd_7686525 : Nat := 4983230072969 + 3 ^ 40 * 7686525 * 2
def baseEnd_7686525 : Nat := 3946881887800644169287821

theorem tailTrace_7686525 : CollatzResearch.WordTrace tailWord_7686525 prefixEnd_7686525 3946881887800644169287821 := by
  unfold tailWord_7686525
  simp only [CollatzResearch.WordTrace]
  refine ⟨280350598478040153801429029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186900398985360102534286019 280350598478040153801429029)
  ·
    refine ⟨52565737214632528837767943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280350598478040153801429029 52565737214632528837767943)
    ·
      refine ⟨78848605821948793256651915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52565737214632528837767943 78848605821948793256651915)
      ·
        refine ⟨118272908732923189884977873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78848605821948793256651915 118272908732923189884977873)
        ·
          refine ⟨88704681549692392413733405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118272908732923189884977873 88704681549692392413733405)
          ·
            refine ⟨33264255581134647155150027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88704681549692392413733405 33264255581134647155150027)
            ·
              refine ⟨49896383371701970732725041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33264255581134647155150027 49896383371701970732725041)
              ·
                refine ⟨37422287528776478049543781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49896383371701970732725041 37422287528776478049543781)
                ·
                  refine ⟨7016678911645589634289459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37422287528776478049543781 7016678911645589634289459)
                  ·
                    refine ⟨10525018367468384451434189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7016678911645589634289459 10525018367468384451434189)
                    ·
                      refine ⟨3946881887800644169287821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10525018367468384451434189 3946881887800644169287821)
                      ·
                        rfl

theorem cell23_7686525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_7686525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686525 prefixEnd_7686525 := by exact prefixLift 7686525
  have htrace : WordTrace (prefixWord ++ tailWord_7686525) baseStart_7686525 baseEnd_7686525 := by
    simpa [prefixWord, tailWord_7686525, baseEnd_7686525] using wordTrace_append hprefix tailTrace_7686525
  have hstable : (prefixWord ++ tailWord_7686525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686525).length < 2 ^ (prefixWord ++ tailWord_7686525).sum := by decide
  have hdescent : baseEnd_7686525 < baseStart_7686525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686542 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7686542 : Nat := 118140960795 + 7686542 * 2 ^ 59
def prefixEnd_7686542 : Nat := 4983230072969 + 3 ^ 40 * 7686542 * 2
def baseEnd_7686542 : Nat := 3946890616971770602775243

theorem tailTrace_7686542 : CollatzResearch.WordTrace tailWord_7686542 prefixEnd_7686542 3946890616971770602775243 := by
  unfold tailWord_7686542
  simp only [CollatzResearch.WordTrace]
  refine ⟨35043902314872320713099735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186900812345985710469865253 35043902314872320713099735)
  ·
    refine ⟨52565853472308481069649603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35043902314872320713099735 52565853472308481069649603)
    ·
      refine ⟨78848780208462721604474405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52565853472308481069649603 78848780208462721604474405)
      ·
        refine ⟨14784146289086760300838951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78848780208462721604474405 14784146289086760300838951)
        ·
          refine ⟨22176219433630140451258427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14784146289086760300838951 22176219433630140451258427)
          ·
            refine ⟨33264329150445210676887641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22176219433630140451258427 33264329150445210676887641)
            ·
              refine ⟨24948246862833908007665731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33264329150445210676887641 24948246862833908007665731)
              ·
                refine ⟨37422370294250862011498597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24948246862833908007665731 37422370294250862011498597)
                ·
                  refine ⟨7016694430172036627155987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37422370294250862011498597 7016694430172036627155987)
                  ·
                    refine ⟨10525041645258054940733981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7016694430172036627155987 10525041645258054940733981)
                    ·
                      refine ⟨3946890616971770602775243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10525041645258054940733981 3946890616971770602775243)
                      ·
                        rfl

theorem cell23_7686542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7686542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686542 prefixEnd_7686542 := by exact prefixLift 7686542
  have htrace : WordTrace (prefixWord ++ tailWord_7686542) baseStart_7686542 baseEnd_7686542 := by
    simpa [prefixWord, tailWord_7686542, baseEnd_7686542] using wordTrace_append hprefix tailTrace_7686542
  have hstable : (prefixWord ++ tailWord_7686542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686542).length < 2 ^ (prefixWord ++ tailWord_7686542).sum := by decide
  have hdescent : baseEnd_7686542 < baseStart_7686542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686565 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 1, 4, 2]
def baseStart_7686565 : Nat := 118140960795 + 7686565 * 2 ^ 59
def prefixEnd_7686565 : Nat := 4983230072969 + 3 ^ 40 * 7686565 * 2
def baseEnd_7686565 : Nat := 3946902427026824012787637

theorem tailTrace_7686565 : CollatzResearch.WordTrace tailWord_7686565 prefixEnd_7686565 3946902427026824012787637 := by
  unfold tailWord_7686565
  simp only [CollatzResearch.WordTrace]
  refine ⟨280352057397895240632885149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186901371598596827088590099 280352057397895240632885149)
  ·
    refine ⟨105132021524210715237331931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280352057397895240632885149 105132021524210715237331931)
    ·
      refine ⟨157698032286316072855997897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105132021524210715237331931 157698032286316072855997897)
      ·
        refine ⟨118273524214737054641998423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157698032286316072855997897 118273524214737054641998423)
        ·
          refine ⟨177410286322105581962997635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118273524214737054641998423 177410286322105581962997635)
          ·
            refine ⟨266115429483158372944496453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177410286322105581962997635 266115429483158372944496453)
            ·
              refine ⟨49896643028092194927093085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266115429483158372944496453 49896643028092194927093085)
              ·
                refine ⟨18711241135534573097659907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49896643028092194927093085 18711241135534573097659907)
                ·
                  refine ⟨28066861703301859646489861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18711241135534573097659907 28066861703301859646489861)
                  ·
                    refine ⟨5262536569369098683716849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28066861703301859646489861 5262536569369098683716849)
                    ·
                      refine ⟨3946902427026824012787637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262536569369098683716849 3946902427026824012787637)
                      ·
                        rfl

theorem cell23_7686565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_7686565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686565 prefixEnd_7686565 := by exact prefixLift 7686565
  have htrace : WordTrace (prefixWord ++ tailWord_7686565) baseStart_7686565 baseEnd_7686565 := by
    simpa [prefixWord, tailWord_7686565, baseEnd_7686565] using wordTrace_append hprefix tailTrace_7686565
  have hstable : (prefixWord ++ tailWord_7686565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686565).length < 2 ^ (prefixWord ++ tailWord_7686565).sum := by decide
  have hdescent : baseEnd_7686565 < baseStart_7686565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686593 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7686593 : Nat := 118140960795 + 7686593 * 2 ^ 59
def prefixEnd_7686593 : Nat := 4983230072969 + 3 ^ 40 * 7686593 * 2
def baseEnd_7686593 : Nat := 3946916804485149903237509

theorem tailTrace_7686593 : CollatzResearch.WordTrace tailWord_7686593 prefixEnd_7686593 3946916804485149903237509 := by
  unfold tailWord_7686593
  simp only [CollatzResearch.WordTrace]
  refine ⟨280353078641793801414904433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186902052427862534276602955 280353078641793801414904433)
  ·
    refine ⟨210264808981345351061178325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280353078641793801414904433 210264808981345351061178325)
    ·
      refine ⟨4928081460500281665496367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 210264808981345351061178325 4928081460500281665496367)
      ·
        refine ⟨7392122190750422498244551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4928081460500281665496367 7392122190750422498244551)
        ·
          refine ⟨11088183286125633747366827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7392122190750422498244551 11088183286125633747366827)
          ·
            refine ⟨16632274929188450621050241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11088183286125633747366827 16632274929188450621050241)
            ·
              refine ⟨12474206196891337965787681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16632274929188450621050241 12474206196891337965787681)
              ·
                refine ⟨9355654647668503474340761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12474206196891337965787681 9355654647668503474340761)
                ·
                  refine ⟨7016740985751377605755571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9355654647668503474340761 7016740985751377605755571)
                  ·
                    refine ⟨10525111478627066408633357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7016740985751377605755571 10525111478627066408633357)
                    ·
                      refine ⟨3946916804485149903237509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10525111478627066408633357 3946916804485149903237509)
                      ·
                        rfl

theorem cell23_7686593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7686593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686593 prefixEnd_7686593 := by exact prefixLift 7686593
  have htrace : WordTrace (prefixWord ++ tailWord_7686593) baseStart_7686593 baseEnd_7686593 := by
    simpa [prefixWord, tailWord_7686593, baseEnd_7686593] using wordTrace_append hprefix tailTrace_7686593
  have hstable : (prefixWord ++ tailWord_7686593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686593).length < 2 ^ (prefixWord ++ tailWord_7686593).sum := by decide
  have hdescent : baseEnd_7686593 < baseStart_7686593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686599 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 2, 2, 2]
def baseStart_7686599 : Nat := 118140960795 + 7686599 * 2 ^ 59
def prefixEnd_7686599 : Nat := 4983230072969 + 3 ^ 40 * 7686599 * 2
def baseEnd_7686599 : Nat := 3946919885369076879762481

theorem tailTrace_7686599 : CollatzResearch.WordTrace tailWord_7686599 prefixEnd_7686599 3946919885369076879762481 := by
  unfold tailWord_7686599
  simp only [CollatzResearch.WordTrace]
  refine ⟨280353297479772064439622851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186902198319848042959748567 280353297479772064439622851)
  ·
    refine ⟨420529946219658096659434277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280353297479772064439622851 420529946219658096659434277)
    ·
      refine ⟨78849364916185893123643927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420529946219658096659434277 78849364916185893123643927)
      ·
        refine ⟨118274047374278839685465891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78849364916185893123643927 118274047374278839685465891)
        ·
          refine ⟨177411071061418259528198837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118274047374278839685465891 177411071061418259528198837)
          ·
            refine ⟨16632287912007961830768641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177411071061418259528198837 16632287912007961830768641)
            ·
              refine ⟨12474215934005971373076481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16632287912007961830768641 12474215934005971373076481)
              ·
                refine ⟨9355661950504478529807361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12474215934005971373076481 9355661950504478529807361)
                ·
                  refine ⟨7016746462878358897355521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9355661950504478529807361 7016746462878358897355521)
                  ·
                    refine ⟨5262559847158769173016641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7016746462878358897355521 5262559847158769173016641)
                    ·
                      refine ⟨3946919885369076879762481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262559847158769173016641 3946919885369076879762481)
                      ·
                        rfl

theorem cell23_7686599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_7686599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686599 prefixEnd_7686599 := by exact prefixLift 7686599
  have htrace : WordTrace (prefixWord ++ tailWord_7686599) baseStart_7686599 baseEnd_7686599 := by
    simpa [prefixWord, tailWord_7686599, baseEnd_7686599] using wordTrace_append hprefix tailTrace_7686599
  have hstable : (prefixWord ++ tailWord_7686599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686599).length < 2 ^ (prefixWord ++ tailWord_7686599).sum := by decide
  have hdescent : baseEnd_7686599 < baseStart_7686599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686618 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_7686618 : Nat := 118140960795 + 7686618 * 2 ^ 59
def prefixEnd_7686618 : Nat := 4983230072969 + 3 ^ 40 * 7686618 * 2
def baseEnd_7686618 : Nat := 1315643213833837435141631

theorem tailTrace_7686618 : CollatzResearch.WordTrace tailWord_7686618 prefixEnd_7686618 1315643213833837435141631 := by
  unfold tailWord_7686618
  simp only [CollatzResearch.WordTrace]
  refine ⟨70088497616675807671141127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186902660311135487123043005 70088497616675807671141127)
  ·
    refine ⟨105132746425013711506711691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70088497616675807671141127 105132746425013711506711691)
    ·
      refine ⟨157699119637520567260067537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105132746425013711506711691 157699119637520567260067537)
      ·
        refine ⟨118274339728140425445050653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157699119637520567260067537 118274339728140425445050653)
        ·
          refine ⟨44352877398052659541893995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118274339728140425445050653 44352877398052659541893995)
          ·
            refine ⟨66529316097078989312840993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44352877398052659541893995 66529316097078989312840993)
            ·
              refine ⟨49896987072809241984630745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66529316097078989312840993 49896987072809241984630745)
              ·
                refine ⟨37422740304606931488473059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49896987072809241984630745 37422740304606931488473059)
                ·
                  refine ⟨56134110456910397232709589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37422740304606931488473059 56134110456910397232709589)
                  ·
                    refine ⟨1315643213833837435141631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56134110456910397232709589 1315643213833837435141631)
                    ·
                      rfl

theorem cell23_7686618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_7686618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686618 prefixEnd_7686618 := by exact prefixLift 7686618
  have htrace : WordTrace (prefixWord ++ tailWord_7686618) baseStart_7686618 baseEnd_7686618 := by
    simpa [prefixWord, tailWord_7686618, baseEnd_7686618] using wordTrace_append hprefix tailTrace_7686618
  have hstable : (prefixWord ++ tailWord_7686618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686618).length < 2 ^ (prefixWord ++ tailWord_7686618).sum := by decide
  have hdescent : baseEnd_7686618 < baseStart_7686618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686625 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 2, 5, 2]
def baseStart_7686625 : Nat := 118140960795 + 7686625 * 2 ^ 59
def prefixEnd_7686625 : Nat := 4983230072969 + 3 ^ 40 * 7686625 * 2
def baseEnd_7686625 : Nat := 3946933235866093778037361

theorem tailTrace_7686625 : CollatzResearch.WordTrace tailWord_7686625 prefixEnd_7686625 3946933235866093778037361 := by
  unfold tailWord_7686625
  simp only [CollatzResearch.WordTrace]
  refine ⟨280354245777677870880069329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186902830518451913920046219 280354245777677870880069329)
  ·
    refine ⟨210265684333258403160051997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280354245777677870880069329 210265684333258403160051997)
    ·
      refine ⟨78849631624971901185019499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210265684333258403160051997 78849631624971901185019499)
      ·
        refine ⟨118274447437457851777529249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78849631624971901185019499 118274447437457851777529249)
        ·
          refine ⟨88705835578093388833146937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118274447437457851777529249 88705835578093388833146937)
          ·
            refine ⟨66529376683570041624860203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88705835578093388833146937 66529376683570041624860203)
            ·
              refine ⟨99794065025355062437290305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66529376683570041624860203 99794065025355062437290305)
              ·
                refine ⟨74845548769016296827967729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99794065025355062437290305 74845548769016296827967729)
                ·
                  refine ⟨56134161576762222620975797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74845548769016296827967729 56134161576762222620975797)
                  ·
                    refine ⟨5262577647821458370716481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56134161576762222620975797 5262577647821458370716481)
                    ·
                      refine ⟨3946933235866093778037361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262577647821458370716481 3946933235866093778037361)
                      ·
                        rfl

theorem cell23_7686625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_7686625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686625 prefixEnd_7686625 := by exact prefixLift 7686625
  have htrace : WordTrace (prefixWord ++ tailWord_7686625) baseStart_7686625 baseEnd_7686625 := by
    simpa [prefixWord, tailWord_7686625, baseEnd_7686625] using wordTrace_append hprefix tailTrace_7686625
  have hstable : (prefixWord ++ tailWord_7686625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686625).length < 2 ^ (prefixWord ++ tailWord_7686625).sum := by decide
  have hdescent : baseEnd_7686625 < baseStart_7686625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686655 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 4, 4, 2]
def baseStart_7686655 : Nat := 118140960795 + 7686655 * 2 ^ 59
def prefixEnd_7686655 : Nat := 4983230072969 + 3 ^ 40 * 7686655 * 2
def baseEnd_7686655 : Nat := 3946948640285728660662223

theorem tailTrace_7686655 : CollatzResearch.WordTrace tailWord_7686655 prefixEnd_7686655 3946948640285728660662223 := by
  unfold tailWord_7686655
  simp only [CollatzResearch.WordTrace]
  refine ⟨280355339967569186003661419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186903559978379457335774279 280355339967569186003661419)
  ·
    refine ⟨420533009951353779005492129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280355339967569186003661419 420533009951353779005492129)
    ·
      refine ⟨315399757463515334254119097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420533009951353779005492129 315399757463515334254119097)
      ·
        refine ⟨236549818097636500690589323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315399757463515334254119097 236549818097636500690589323)
        ·
          refine ⟨354824727146454751035883985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236549818097636500690589323 354824727146454751035883985)
          ·
            refine ⟨266118545359841063276912989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354824727146454751035883985 266118545359841063276912989)
            ·
              refine ⟨99794454509940398728842371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266118545359841063276912989 99794454509940398728842371)
              ·
                refine ⟨149691681764910598093263557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99794454509940398728842371 149691681764910598093263557)
                ·
                  refine ⟨28067190330920737142486917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149691681764910598093263557 28067190330920737142486917)
                  ·
                    refine ⟨5262598187047638214216297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28067190330920737142486917 5262598187047638214216297)
                    ·
                      refine ⟨3946948640285728660662223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262598187047638214216297 3946948640285728660662223)
                      ·
                        rfl

theorem cell23_7686655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 4, 2].length) (baseStart_7686655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686655 prefixEnd_7686655 := by exact prefixLift 7686655
  have htrace : WordTrace (prefixWord ++ tailWord_7686655) baseStart_7686655 baseEnd_7686655 := by
    simpa [prefixWord, tailWord_7686655, baseEnd_7686655] using wordTrace_append hprefix tailTrace_7686655
  have hstable : (prefixWord ++ tailWord_7686655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686655).length < 2 ^ (prefixWord ++ tailWord_7686655).sum := by decide
  have hdescent : baseEnd_7686655 < baseStart_7686655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686716 : List Nat := [2, 2, 2, 2, 3, 2, 3, 2, 1, 4]
def baseStart_7686716 : Nat := 118140960795 + 7686716 * 2 ^ 59
def prefixEnd_7686716 : Nat := 4983230072969 + 3 ^ 40 * 7686716 * 2
def baseEnd_7686716 : Nat := 1315659987535217640666481

theorem tailTrace_7686716 : CollatzResearch.WordTrace tailWord_7686716 prefixEnd_7686716 1315659987535217640666481 := by
  unfold tailWord_7686716
  simp only [CollatzResearch.WordTrace]
  refine ⟨140178782410174096710816001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186905043213565462281088001 140178782410174096710816001)
  ·
    refine ⟨105134086807630572533112001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140178782410174096710816001 105134086807630572533112001)
    ·
      refine ⟨78850565105722929399834001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105134086807630572533112001 78850565105722929399834001)
      ·
        refine ⟨59137923829292197049875501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78850565105722929399834001 59137923829292197049875501)
        ·
          refine ⟨22176721435984573893703313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59137923829292197049875501 22176721435984573893703313)
          ·
            refine ⟨16632541076988430420277485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22176721435984573893703313 16632541076988430420277485)
            ·
              refine ⟨6237202903870661407604057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16632541076988430420277485 6237202903870661407604057)
              ·
                refine ⟨4677902177902996055703043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6237202903870661407604057 4677902177902996055703043)
                ·
                  refine ⟨7016853266854494083554565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4677902177902996055703043 7016853266854494083554565)
                  ·
                    refine ⟨1315659987535217640666481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7016853266854494083554565 1315659987535217640666481)
                    ·
                      rfl

theorem cell23_7686716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_7686716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686716 prefixEnd_7686716 := by exact prefixLift 7686716
  have htrace : WordTrace (prefixWord ++ tailWord_7686716) baseStart_7686716 baseEnd_7686716 := by
    simpa [prefixWord, tailWord_7686716, baseEnd_7686716] using wordTrace_append hprefix tailTrace_7686716
  have hstable : (prefixWord ++ tailWord_7686716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686716).length < 2 ^ (prefixWord ++ tailWord_7686716).sum := by decide
  have hdescent : baseEnd_7686716 < baseStart_7686716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686732 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 4, 3, 2]
def baseStart_7686732 : Nat := 118140960795 + 7686732 * 2 ^ 59
def prefixEnd_7686732 : Nat := 4983230072969 + 3 ^ 40 * 7686732 * 2
def baseEnd_7686732 : Nat := 3946988178296124859399369

theorem tailTrace_7686732 : CollatzResearch.WordTrace tailWord_7686732 prefixEnd_7686732 3946988178296124859399369 := by
  unfold tailWord_7686732
  simp only [CollatzResearch.WordTrace]
  refine ⟨140179074194145114077107225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186905432258860152102809633 140179074194145114077107225)
  ·
    refine ⟨105134305645608835557830419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140179074194145114077107225 105134305645608835557830419)
    ·
      refine ⟨157701458468413253336745629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105134305645608835557830419 157701458468413253336745629)
      ·
        refine ⟨59138046925654970001279611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157701458468413253336745629 59138046925654970001279611)
        ·
          refine ⟨88707070388482455001919417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59138046925654970001279611 88707070388482455001919417)
          ·
            refine ⟨66530302791361841251439563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88707070388482455001919417 66530302791361841251439563)
            ·
              refine ⟨99795454187042761877159345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66530302791361841251439563 99795454187042761877159345)
              ·
                refine ⟨74846590640282071407869509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99795454187042761877159345 74846590640282071407869509)
                ·
                  refine ⟨14033735745052888388975533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74846590640282071407869509 14033735745052888388975533)
                  ·
                    refine ⟨5262650904394833145865825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14033735745052888388975533 5262650904394833145865825)
                    ·
                      refine ⟨3946988178296124859399369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262650904394833145865825 3946988178296124859399369)
                      ·
                        rfl

theorem cell23_7686732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_7686732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686732 prefixEnd_7686732 := by exact prefixLift 7686732
  have htrace : WordTrace (prefixWord ++ tailWord_7686732) baseStart_7686732 baseEnd_7686732 := by
    simpa [prefixWord, tailWord_7686732, baseEnd_7686732] using wordTrace_append hprefix tailTrace_7686732
  have hstable : (prefixWord ++ tailWord_7686732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686732).length < 2 ^ (prefixWord ++ tailWord_7686732).sum := by decide
  have hdescent : baseEnd_7686732 < baseStart_7686732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686755 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 1, 6]
def baseStart_7686755 : Nat := 118140960795 + 7686755 * 2 ^ 59
def prefixEnd_7686755 : Nat := 4983230072969 + 3 ^ 40 * 7686755 * 2
def baseEnd_7686755 : Nat := 1315666662783726089803921

theorem tailTrace_7686755 : CollatzResearch.WordTrace tailWord_7686755 prefixEnd_7686755 1315666662783726089803921 := by
  unfold tailWord_7686755
  simp only [CollatzResearch.WordTrace]
  refine ⟨280358987267206903082301719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186905991511471268721534479 280358987267206903082301719)
  ·
    refine ⟨420538480900810354623452579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280358987267206903082301719 420538480900810354623452579)
    ·
      refine ⟨630807721351215531935178869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420538480900810354623452579 630807721351215531935178869)
      ·
        refine ⟨59138223876676456118923019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 630807721351215531935178869 59138223876676456118923019)
        ·
          refine ⟨88707335815014684178384529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59138223876676456118923019 88707335815014684178384529)
          ·
            refine ⟨66530501861261013133788397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88707335815014684178384529 66530501861261013133788397)
            ·
              refine ⟨24948938197972879925170649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66530501861261013133788397 24948938197972879925170649)
              ·
                refine ⟨18711703648479659943877987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24948938197972879925170649 18711703648479659943877987)
                ·
                  refine ⟨28067555472719489915816981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18711703648479659943877987 28067555472719489915816981)
                  ·
                    refine ⟨1315666662783726089803921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28067555472719489915816981 1315666662783726089803921)
                    ·
                      rfl

theorem cell23_7686755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 6].length) (baseStart_7686755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686755 prefixEnd_7686755 := by exact prefixLift 7686755
  have htrace : WordTrace (prefixWord ++ tailWord_7686755) baseStart_7686755 baseEnd_7686755 := by
    simpa [prefixWord, tailWord_7686755, baseEnd_7686755] using wordTrace_append hprefix tailTrace_7686755
  have hstable : (prefixWord ++ tailWord_7686755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686755).length < 2 ^ (prefixWord ++ tailWord_7686755).sum := by decide
  have hdescent : baseEnd_7686755 < baseStart_7686755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686768 : List Nat := [2, 1, 1, 1, 18]
def baseStart_7686768 : Nat := 118140960795 + 7686768 * 2 ^ 59
def prefixEnd_7686768 : Nat := 4983230072969 + 3 ^ 40 * 7686768 * 2
def baseEnd_7686768 : Nat := 5414275258710132672907

theorem tailTrace_7686768 : CollatzResearch.WordTrace tailWord_7686768 prefixEnd_7686768 5414275258710132672907 := by
  unfold tailWord_7686768
  simp only [CollatzResearch.WordTrace]
  refine ⟨140179730708079903151262479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186906307610773204201683305 140179730708079903151262479)
  ·
    refine ⟨210269596062119854726893719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140179730708079903151262479 210269596062119854726893719)
    ·
      refine ⟨315404394093179782090340579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210269596062119854726893719 315404394093179782090340579)
      ·
        refine ⟨473106591139769673135510869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315404394093179782090340579 473106591139769673135510869)
        ·
          refine ⟨5414275258710132672907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 18 473106591139769673135510869 5414275258710132672907)
          ·
            rfl

theorem cell23_7686768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 18].length) (baseStart_7686768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686768 prefixEnd_7686768 := by exact prefixLift 7686768
  have htrace : WordTrace (prefixWord ++ tailWord_7686768) baseStart_7686768 baseEnd_7686768 := by
    simpa [prefixWord, tailWord_7686768, baseEnd_7686768] using wordTrace_append hprefix tailTrace_7686768
  have hstable : (prefixWord ++ tailWord_7686768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686768).length < 2 ^ (prefixWord ++ tailWord_7686768).sum := by decide
  have hdescent : baseEnd_7686768 < baseStart_7686768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686773 : List Nat := [1, 3, 4, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_7686773 : Nat := 118140960795 + 7686773 * 2 ^ 59
def prefixEnd_7686773 : Nat := 4983230072969 + 3 ^ 40 * 7686773 * 2
def baseEnd_7686773 : Nat := 3947009231002959198986681

theorem tailTrace_7686773 : CollatzResearch.WordTrace tailWord_7686773 prefixEnd_7686773 3947009231002959198986681 := by
  unfold tailWord_7686773
  simp only [CollatzResearch.WordTrace]
  refine ⟨280359643781141692156456973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186906429187427794770971315 280359643781141692156456973)
  ·
    refine ⟨105134866417928134558671365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280359643781141692156456973 105134866417928134558671365)
    ·
      refine ⟨19712787453361525229750881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105134866417928134558671365 19712787453361525229750881)
      ·
        refine ⟨14784590590021143922313161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19712787453361525229750881 14784590590021143922313161)
        ·
          refine ⟨11088442942515857941734871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14784590590021143922313161 11088442942515857941734871)
          ·
            refine ⟨16632664413773786912602307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11088442942515857941734871 16632664413773786912602307)
            ·
              refine ⟨24948996620660680368903461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16632664413773786912602307 24948996620660680368903461)
              ·
                refine ⟨4677936866373877569169399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24948996620660680368903461 4677936866373877569169399)
                ·
                  refine ⟨7016905299560816353754099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4677936866373877569169399 7016905299560816353754099)
                  ·
                    refine ⟨10525357949341224530631149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7016905299560816353754099 10525357949341224530631149)
                    ·
                      refine ⟨3947009231002959198986681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10525357949341224530631149 3947009231002959198986681)
                      ·
                        rfl

theorem cell23_7686773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_7686773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686773 prefixEnd_7686773 := by exact prefixLift 7686773
  have htrace : WordTrace (prefixWord ++ tailWord_7686773) baseStart_7686773 baseEnd_7686773 := by
    simpa [prefixWord, tailWord_7686773, baseEnd_7686773] using wordTrace_append hprefix tailTrace_7686773
  have hstable : (prefixWord ++ tailWord_7686773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686773).length < 2 ^ (prefixWord ++ tailWord_7686773).sum := by decide
  have hdescent : baseEnd_7686773 < baseStart_7686773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686823 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 2, 4]
def baseStart_7686823 : Nat := 118140960795 + 7686823 * 2 ^ 59
def prefixEnd_7686823 : Nat := 4983230072969 + 3 ^ 40 * 7686823 * 2
def baseEnd_7686823 : Nat := 1315678301678561334453817

theorem tailTrace_7686823 : CollatzResearch.WordTrace tailWord_7686823 prefixEnd_7686823 1315678301678561334453817 := by
  unfold tailWord_7686823
  simp only [CollatzResearch.WordTrace]
  refine ⟨280361467430960550695777123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186907644953973700463851415 280361467430960550695777123)
  ·
    refine ⟨420542201146440826043665685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280361467430960550695777123 420542201146440826043665685)
    ·
      refine ⟨19712915678739413720796829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 420542201146440826043665685 19712915678739413720796829)
      ·
        refine ⟨7392343379527280145298811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19712915678739413720796829 7392343379527280145298811)
        ·
          refine ⟨11088515069290920217948217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7392343379527280145298811 11088515069290920217948217)
          ·
            refine ⟨8316386301968190163461163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11088515069290920217948217 8316386301968190163461163)
            ·
              refine ⟨12474579452952285245191745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8316386301968190163461163 12474579452952285245191745)
              ·
                refine ⟨9355934589714213933893809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12474579452952285245191745 9355934589714213933893809)
                ·
                  refine ⟨7016950942285660450420357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9355934589714213933893809 7016950942285660450420357)
                  ·
                    refine ⟨1315678301678561334453817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7016950942285660450420357 1315678301678561334453817)
                    ·
                      rfl

theorem cell23_7686823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_7686823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686823 prefixEnd_7686823 := by exact prefixLift 7686823
  have htrace : WordTrace (prefixWord ++ tailWord_7686823) baseStart_7686823 baseEnd_7686823 := by
    simpa [prefixWord, tailWord_7686823, baseEnd_7686823] using wordTrace_append hprefix tailTrace_7686823
  have hstable : (prefixWord ++ tailWord_7686823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686823).length < 2 ^ (prefixWord ++ tailWord_7686823).sum := by decide
  have hdescent : baseEnd_7686823 < baseStart_7686823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686830 : List Nat := [4, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_7686830 : Nat := 118140960795 + 7686830 * 2 ^ 59
def prefixEnd_7686830 : Nat := 4983230072969 + 3 ^ 40 * 7686830 * 2
def baseEnd_7686830 : Nat := 3947038499400265475973919

theorem tailTrace_7686830 : CollatzResearch.WordTrace tailWord_7686830 prefixEnd_7686830 3947038499400265475973919 := by
  unfold tailWord_7686830
  simp only [CollatzResearch.WordTrace]
  refine ⟨35045215342741898861410243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186907815161290127260854629 35045215342741898861410243)
  ·
    refine ⟨52567823014112848292115365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35045215342741898861410243 52567823014112848292115365)
    ·
      refine ⟨9856466815146159054771631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52567823014112848292115365 9856466815146159054771631)
      ·
        refine ⟨14784700222719238582157447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9856466815146159054771631 14784700222719238582157447)
        ·
          refine ⟨22177050334078857873236171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14784700222719238582157447 22177050334078857873236171)
          ·
            refine ⟨33265575501118286809854257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22177050334078857873236171 33265575501118286809854257)
            ·
              refine ⟨24949181625838715107390693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33265575501118286809854257 24949181625838715107390693)
              ·
                refine ⟨4677971554844759082635755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24949181625838715107390693 4677971554844759082635755)
                ·
                  refine ⟨7016957332267138623953633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4677971554844759082635755 7016957332267138623953633)
                  ·
                    refine ⟨5262717999200353967965225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7016957332267138623953633 5262717999200353967965225)
                    ·
                      refine ⟨3947038499400265475973919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262717999200353967965225 3947038499400265475973919)
                      ·
                        rfl

theorem cell23_7686830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_7686830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686830 prefixEnd_7686830 := by exact prefixLift 7686830
  have htrace : WordTrace (prefixWord ++ tailWord_7686830) baseStart_7686830 baseEnd_7686830 := by
    simpa [prefixWord, tailWord_7686830, baseEnd_7686830] using wordTrace_append hprefix tailTrace_7686830
  have hstable : (prefixWord ++ tailWord_7686830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686830).length < 2 ^ (prefixWord ++ tailWord_7686830).sum := by decide
  have hdescent : baseEnd_7686830 < baseStart_7686830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686856 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 1, 3, 2]
def baseStart_7686856 : Nat := 118140960795 + 7686856 * 2 ^ 59
def prefixEnd_7686856 : Nat := 4983230072969 + 3 ^ 40 * 7686856 * 2
def baseEnd_7686856 : Nat := 3947051849897282374248799

theorem tailTrace_7686856 : CollatzResearch.WordTrace tailWord_7686856 prefixEnd_7686856 3947051849897282374248799 := by
  unfold tailWord_7686856
  simp only [CollatzResearch.WordTrace]
  refine ⟨140181335519920498665864211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186908447359893998221152281 140181335519920498665864211)
  ·
    refine ⟨210272003279880747998796317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140181335519920498665864211 210272003279880747998796317)
    ·
      refine ⟨78852001229955280499548619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210272003279880747998796317 78852001229955280499548619)
      ·
        refine ⟨118278001844932920749322929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78852001229955280499548619 118278001844932920749322929)
        ·
          refine ⟨88708501383699690561992197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118278001844932920749322929 88708501383699690561992197)
          ·
            refine ⟨16632844009443691980373537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88708501383699690561992197 16632844009443691980373537)
            ·
              refine ⟨12474633007082768985280153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16632844009443691980373537 12474633007082768985280153)
              ·
                refine ⟨9355974755312076738960115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12474633007082768985280153 9355974755312076738960115)
                ·
                  refine ⟨14033962132968115108440173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9355974755312076738960115 14033962132968115108440173)
                  ·
                    refine ⟨5262735799863043165665065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14033962132968115108440173 5262735799863043165665065)
                    ·
                      refine ⟨3947051849897282374248799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262735799863043165665065 3947051849897282374248799)
                      ·
                        rfl

theorem cell23_7686856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_7686856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686856 prefixEnd_7686856 := by exact prefixLift 7686856
  have htrace : WordTrace (prefixWord ++ tailWord_7686856) baseStart_7686856 baseEnd_7686856 := by
    simpa [prefixWord, tailWord_7686856, baseEnd_7686856] using wordTrace_append hprefix tailTrace_7686856
  have hstable : (prefixWord ++ tailWord_7686856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686856).length < 2 ^ (prefixWord ++ tailWord_7686856).sum := by decide
  have hdescent : baseEnd_7686856 < baseStart_7686856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686872 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_7686872 : Nat := 118140960795 + 7686872 * 2 ^ 59
def prefixEnd_7686872 : Nat := 4983230072969 + 3 ^ 40 * 7686872 * 2
def baseEnd_7686872 : Nat := 3947060065587754311648725

theorem tailTrace_7686872 : CollatzResearch.WordTrace tailWord_7686872 prefixEnd_7686872 3947060065587754311648725 := by
  unfold tailWord_7686872
  simp only [CollatzResearch.WordTrace]
  refine ⟨140181627303891516032155435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186908836405188688042873913 140181627303891516032155435)
  ·
    refine ⟨210272440955837274048233153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140181627303891516032155435 210272440955837274048233153)
    ·
      refine ⟨157704330716877955536174865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210272440955837274048233153 157704330716877955536174865)
      ·
        refine ⟨118278248037658466652131149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157704330716877955536174865 118278248037658466652131149)
        ·
          refine ⟨44354343014121924994549181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118278248037658466652131149 44354343014121924994549181)
          ·
            refine ⟨16632878630295721872955943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44354343014121924994549181 16632878630295721872955943)
            ·
              refine ⟨24949317945443582809433915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16632878630295721872955943 24949317945443582809433915)
              ·
                refine ⟨37423976918165374214150873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24949317945443582809433915 37423976918165374214150873)
                ·
                  refine ⟨28067982688624030660613155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37423976918165374214150873 28067982688624030660613155)
                  ·
                    refine ⟨42101974032936045990919733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28067982688624030660613155 42101974032936045990919733)
                    ·
                      refine ⟨3947060065587754311648725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42101974032936045990919733 3947060065587754311648725)
                      ·
                        rfl

theorem cell23_7686872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_7686872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686872 prefixEnd_7686872 := by exact prefixLift 7686872
  have htrace : WordTrace (prefixWord ++ tailWord_7686872) baseStart_7686872 baseEnd_7686872 := by
    simpa [prefixWord, tailWord_7686872, baseEnd_7686872] using wordTrace_append hprefix tailTrace_7686872
  have hstable : (prefixWord ++ tailWord_7686872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686872).length < 2 ^ (prefixWord ++ tailWord_7686872).sum := by decide
  have hdescent : baseEnd_7686872 < baseStart_7686872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686905 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 3, 7]
def baseStart_7686905 : Nat := 118140960795 + 7686905 * 2 ^ 59
def prefixEnd_7686905 : Nat := 4983230072969 + 3 ^ 40 * 7686905 * 2
def baseEnd_7686905 : Nat := 1315692336816450894178691

theorem tailTrace_7686905 : CollatzResearch.WordTrace tailWord_7686905 prefixEnd_7686905 1315692336816450894178691 := by
  unfold tailWord_7686905
  simp only [CollatzResearch.WordTrace]
  refine ⟨280364458216663478700262169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186909638811108985800174779 280364458216663478700262169)
  ·
    refine ⟨210273343662497609025196627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280364458216663478700262169 210273343662497609025196627)
    ·
      refine ⟨315410015493746413537794941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210273343662497609025196627 315410015493746413537794941)
      ·
        refine ⟨118278755810154905076673103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315410015493746413537794941 118278755810154905076673103)
        ·
          refine ⟨177418133715232357615009655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118278755810154905076673103 177418133715232357615009655)
          ·
            refine ⟨266127200572848536422514483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177418133715232357615009655 266127200572848536422514483)
            ·
              refine ⟨399190800859272804633771725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266127200572848536422514483 399190800859272804633771725)
              ·
                refine ⟨149696550322227301737664397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399190800859272804633771725 149696550322227301737664397)
                ·
                  refine ⟨56136206370835238151624149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149696550322227301737664397 56136206370835238151624149)
                  ·
                    refine ⟨1315692336816450894178691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56136206370835238151624149 1315692336816450894178691)
                    ·
                      rfl

theorem cell23_7686905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_7686905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686905 prefixEnd_7686905 := by exact prefixLift 7686905
  have htrace : WordTrace (prefixWord ++ tailWord_7686905) baseStart_7686905 baseEnd_7686905 := by
    simpa [prefixWord, tailWord_7686905, baseEnd_7686905] using wordTrace_append hprefix tailTrace_7686905
  have hstable : (prefixWord ++ tailWord_7686905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686905).length < 2 ^ (prefixWord ++ tailWord_7686905).sum := by decide
  have hdescent : baseEnd_7686905 < baseStart_7686905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686915 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 7]
def baseStart_7686915 : Nat := 118140960795 + 7686915 * 2 ^ 59
def prefixEnd_7686915 : Nat := 4983230072969 + 3 ^ 40 * 7686915 * 2
def baseEnd_7686915 : Nat := 3947082145255897643411027

theorem tailTrace_7686915 : CollatzResearch.WordTrace tailWord_7686915 prefixEnd_7686915 3947082145255897643411027 := by
  unfold tailWord_7686915
  simp only [CollatzResearch.WordTrace]
  refine ⟨280364822946627250408126199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186909881964418166938750799 280364822946627250408126199)
  ·
    refine ⟨420547234419940875612189299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280364822946627250408126199 420547234419940875612189299)
    ·
      refine ⟨630820851629911313418283949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420547234419940875612189299 630820851629911313418283949)
      ·
        refine ⟨236557819361216742531856481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 630820851629911313418283949 236557819361216742531856481)
        ·
          refine ⟨177418364520912556898892361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236557819361216742531856481 177418364520912556898892361)
          ·
            refine ⟨133063773390684417674169271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177418364520912556898892361 133063773390684417674169271)
            ·
              refine ⟨199595660086026626511253907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133063773390684417674169271 199595660086026626511253907)
              ·
                refine ⟨299393490129039939766880861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199595660086026626511253907 299393490129039939766880861)
                ·
                  refine ⟨112272558798389977412580323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299393490129039939766880861 112272558798389977412580323)
                  ·
                    refine ⟨168408838197584966118870485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112272558798389977412580323 168408838197584966118870485)
                    ·
                      refine ⟨3947082145255897643411027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168408838197584966118870485 3947082145255897643411027)
                      ·
                        rfl

theorem cell23_7686915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_7686915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686915 prefixEnd_7686915 := by exact prefixLift 7686915
  have htrace : WordTrace (prefixWord ++ tailWord_7686915) baseStart_7686915 baseEnd_7686915 := by
    simpa [prefixWord, tailWord_7686915, baseEnd_7686915] using wordTrace_append hprefix tailTrace_7686915
  have hstable : (prefixWord ++ tailWord_7686915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686915).length < 2 ^ (prefixWord ++ tailWord_7686915).sum := by decide
  have hdescent : baseEnd_7686915 < baseStart_7686915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686973 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_7686973 : Nat := 118140960795 + 7686973 * 2 ^ 59
def prefixEnd_7686973 : Nat := 4983230072969 + 3 ^ 40 * 7686973 * 2
def baseEnd_7686973 : Nat := 1315703975711286138828587

theorem tailTrace_7686973 : CollatzResearch.WordTrace tailWord_7686973 prefixEnd_7686973 1315703975711286138828587 := by
  unfold tailWord_7686973
  simp only [CollatzResearch.WordTrace]
  refine ⟨280366938380417126313737573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186911292253611417542491715 280366938380417126313737573)
  ·
    refine ⟨52568800946328211183825795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280366938380417126313737573 52568800946328211183825795)
    ·
      refine ⟨78853201419492316775738693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52568800946328211183825795 78853201419492316775738693)
      ·
        refine ⟨14784975266154809395451005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78853201419492316775738693 14784975266154809395451005)
        ·
          refine ⟨5544365724808053523294127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14784975266154809395451005 5544365724808053523294127)
          ·
            refine ⟨8316548587212080284941191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5544365724808053523294127 8316548587212080284941191)
            ·
              refine ⟨12474822880818120427411787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8316548587212080284941191 12474822880818120427411787)
              ·
                refine ⟨18712234321227180641117681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12474822880818120427411787 18712234321227180641117681)
                ·
                  refine ⟨14034175740920385480838261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18712234321227180641117681 14034175740920385480838261)
                  ·
                    refine ⟨1315703975711286138828587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14034175740920385480838261 1315703975711286138828587)
                    ·
                      rfl

theorem cell23_7686973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_7686973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686973 prefixEnd_7686973 := by exact prefixLift 7686973
  have htrace : WordTrace (prefixWord ++ tailWord_7686973) baseStart_7686973 baseEnd_7686973 := by
    simpa [prefixWord, tailWord_7686973, baseEnd_7686973] using wordTrace_append hprefix tailTrace_7686973
  have hstable : (prefixWord ++ tailWord_7686973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686973).length < 2 ^ (prefixWord ++ tailWord_7686973).sum := by decide
  have hdescent : baseEnd_7686973 < baseStart_7686973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7686999 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 6]
def baseStart_7686999 : Nat := 118140960795 + 7686999 * 2 ^ 59
def prefixEnd_7686999 : Nat := 4983230072969 + 3 ^ 40 * 7686999 * 2
def baseEnd_7686999 : Nat := 438569475292319479417849

theorem tailTrace_7686999 : CollatzResearch.WordTrace tailWord_7686999 prefixEnd_7686999 438569475292319479417849 := by
  unfold tailWord_7686999
  simp only [CollatzResearch.WordTrace]
  refine ⟨280367886678322932754184051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186911924452215288502789367 280367886678322932754184051)
  ·
    refine ⟨420551830017484399131276077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280367886678322932754184051 420551830017484399131276077)
    ·
      refine ⟨157706936256556649674228529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420551830017484399131276077 157706936256556649674228529)
      ·
        refine ⟨118280202192417487255671397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157706936256556649674228529 118280202192417487255671397)
        ·
          refine ⟨22177537911078278860438387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118280202192417487255671397 22177537911078278860438387)
          ·
            refine ⟨33266306866617418290657581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22177537911078278860438387 33266306866617418290657581)
            ·
              refine ⟨12474865074981531858996593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33266306866617418290657581 12474865074981531858996593)
              ·
                refine ⟨9356148806236148894247445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12474865074981531858996593 9356148806236148894247445)
                ·
                  refine ⟨438569475292319479417849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9356148806236148894247445 438569475292319479417849)
                  ·
                    rfl

theorem cell23_7686999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 6].length) (baseStart_7686999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7686999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7686999 prefixEnd_7686999 := by exact prefixLift 7686999
  have htrace : WordTrace (prefixWord ++ tailWord_7686999) baseStart_7686999 baseEnd_7686999 := by
    simpa [prefixWord, tailWord_7686999, baseEnd_7686999] using wordTrace_append hprefix tailTrace_7686999
  have hstable : (prefixWord ++ tailWord_7686999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7686999).length < 2 ^ (prefixWord ++ tailWord_7686999).sum := by decide
  have hdescent : baseEnd_7686999 < baseStart_7686999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7686999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687002 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_7687002 : Nat := 118140960795 + 7687002 * 2 ^ 59
def prefixEnd_7687002 : Nat := 4983230072969 + 3 ^ 40 * 7687002 * 2
def baseEnd_7687002 : Nat := 3947126818072838803023127

theorem tailTrace_7687002 : CollatzResearch.WordTrace tailWord_7687002 prefixEnd_7687002 3947126818072838803023127 := by
  unfold tailWord_7687002
  simp only [CollatzResearch.WordTrace]
  refine ⟨70091999024328016066635815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186911997398208042844362173 70091999024328016066635815)
  ·
    refine ⟨105137998536492024099953723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70091999024328016066635815 105137998536492024099953723)
    ·
      refine ⟨157706997804738036149930585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105137998536492024099953723 157706997804738036149930585)
      ·
        refine ⟨118280248353553527112447939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157706997804738036149930585 118280248353553527112447939)
        ·
          refine ⟨177420372530330290668671909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118280248353553527112447939 177420372530330290668671909)
          ·
            refine ⟨33266319849436929500375983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177420372530330290668671909 33266319849436929500375983)
            ·
              refine ⟨49899479774155394250563975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33266319849436929500375983 49899479774155394250563975)
              ·
                refine ⟨74849219661233091375845963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49899479774155394250563975 74849219661233091375845963)
                ·
                  refine ⟨112273829491849637063768945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74849219661233091375845963 112273829491849637063768945)
                  ·
                    refine ⟨84205372118887227797826709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112273829491849637063768945 84205372118887227797826709)
                    ·
                      refine ⟨3947126818072838803023127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84205372118887227797826709 3947126818072838803023127)
                      ·
                        rfl

theorem cell23_7687002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_7687002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687002 prefixEnd_7687002 := by exact prefixLift 7687002
  have htrace : WordTrace (prefixWord ++ tailWord_7687002) baseStart_7687002 baseEnd_7687002 := by
    simpa [prefixWord, tailWord_7687002, baseEnd_7687002] using wordTrace_append hprefix tailTrace_7687002
  have hstable : (prefixWord ++ tailWord_7687002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687002).length < 2 ^ (prefixWord ++ tailWord_7687002).sum := by decide
  have hdescent : baseEnd_7687002 < baseStart_7687002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687016 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 6]
def baseStart_7687016 : Nat := 118140960795 + 7687016 * 2 ^ 59
def prefixEnd_7687016 : Nat := 4983230072969 + 3 ^ 40 * 7687016 * 2
def baseEnd_7687016 : Nat := 438570445200222416472007

theorem tailTrace_7687016 : CollatzResearch.WordTrace tailWord_7687016 prefixEnd_7687016 438570445200222416472007 := by
  unfold tailWord_7687016
  simp only [CollatzResearch.WordTrace]
  refine ⟨140184253359630672328776451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186912337812840896438368601 140184253359630672328776451)
  ·
    refine ⟨210276380039446008493164677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140184253359630672328776451 210276380039446008493164677)
    ·
      refine ⟨39426821257396126592468377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210276380039446008493164677 39426821257396126592468377)
      ·
        refine ⟨29570115943047094944351283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39426821257396126592468377 29570115943047094944351283)
        ·
          refine ⟨44355173914570642416526925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29570115943047094944351283 44355173914570642416526925)
          ·
            refine ⟨16633190217963990906197597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44355173914570642416526925 16633190217963990906197597)
            ·
              refine ⟨6237446331736496589824099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16633190217963990906197597 6237446331736496589824099)
              ·
                refine ⟨9356169497604744884736149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6237446331736496589824099 9356169497604744884736149)
                ·
                  refine ⟨438570445200222416472007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9356169497604744884736149 438570445200222416472007)
                  ·
                    rfl

theorem cell23_7687016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 6].length) (baseStart_7687016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687016 prefixEnd_7687016 := by exact prefixLift 7687016
  have htrace : WordTrace (prefixWord ++ tailWord_7687016) baseStart_7687016 baseEnd_7687016 := by
    simpa [prefixWord, tailWord_7687016, baseEnd_7687016] using wordTrace_append hprefix tailTrace_7687016
  have hstable : (prefixWord ++ tailWord_7687016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687016).length < 2 ^ (prefixWord ++ tailWord_7687016).sum := by decide
  have hdescent : baseEnd_7687016 < baseStart_7687016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687019 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 1, 5, 2]
def baseStart_7687019 : Nat := 118140960795 + 7687019 * 2 ^ 59
def prefixEnd_7687019 : Nat := 4983230072969 + 3 ^ 40 * 7687019 * 2
def baseEnd_7687019 : Nat := 3947135547243965236510549

theorem tailTrace_7687019 : CollatzResearch.WordTrace tailWord_7687019 prefixEnd_7687019 3947135547243965236510549 := by
  unfold tailWord_7687019
  simp only [CollatzResearch.WordTrace]
  refine ⟨280368616138250476169912111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186912410758833650779941407 280368616138250476169912111)
  ·
    refine ⟨420552924207375714254868167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280368616138250476169912111 420552924207375714254868167)
    ·
      refine ⟨630829386311063571382302251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420552924207375714254868167 630829386311063571382302251)
      ·
        refine ⟨946244079466595357073453377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630829386311063571382302251 946244079466595357073453377)
        ·
          refine ⟨709683059599946517805090033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946244079466595357073453377 709683059599946517805090033)
          ·
            refine ⟨532262294699959888353817525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709683059599946517805090033 532262294699959888353817525)
            ·
              refine ⟨49899590128121239533170393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 532262294699959888353817525 49899590128121239533170393)
              ·
                refine ⟨37424692596090929649877795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49899590128121239533170393 37424692596090929649877795)
                ·
                  refine ⟨56137038894136394474816693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37424692596090929649877795 56137038894136394474816693)
                  ·
                    refine ⟨5262847396325286982014065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56137038894136394474816693 5262847396325286982014065)
                    ·
                      refine ⟨3947135547243965236510549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262847396325286982014065 3947135547243965236510549)
                      ·
                        rfl

theorem cell23_7687019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 5, 2].length) (baseStart_7687019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687019 prefixEnd_7687019 := by exact prefixLift 7687019
  have htrace : WordTrace (prefixWord ++ tailWord_7687019) baseStart_7687019 baseEnd_7687019 := by
    simpa [prefixWord, tailWord_7687019, baseEnd_7687019] using wordTrace_append hprefix tailTrace_7687019
  have hstable : (prefixWord ++ tailWord_7687019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687019).length < 2 ^ (prefixWord ++ tailWord_7687019).sum := by decide
  have hdescent : baseEnd_7687019 < baseStart_7687019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687026 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_7687026 : Nat := 118140960795 + 7687026 * 2 ^ 59
def prefixEnd_7687026 : Nat := 4983230072969 + 3 ^ 40 * 7687026 * 2
def baseEnd_7687026 : Nat := 3947139141608546709123017

theorem tailTrace_7687026 : CollatzResearch.WordTrace tailWord_7687026 prefixEnd_7687026 3947139141608546709123017 := by
  unfold tailWord_7687026
  simp only [CollatzResearch.WordTrace]
  refine ⟨70092217862306279091354233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186912580966150077576944621 70092217862306279091354233)
  ·
    refine ⟨52569163396729709318515675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70092217862306279091354233 52569163396729709318515675)
    ·
      refine ⟨78853745095094563977773513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52569163396729709318515675 78853745095094563977773513)
      ·
        refine ⟨59140308821320922983330135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78853745095094563977773513 59140308821320922983330135)
        ·
          refine ⟨88710463231981384474995203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59140308821320922983330135 88710463231981384474995203)
          ·
            refine ⟨133065694847972076712492805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88710463231981384474995203 133065694847972076712492805)
            ·
              refine ⟨24949817783994764383592401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133065694847972076712492805 24949817783994764383592401)
              ·
                refine ⟨18712363337996073287694301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24949817783994764383592401 18712363337996073287694301)
                ·
                  refine ⟨7017136251748527482885363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18712363337996073287694301 7017136251748527482885363)
                  ·
                    refine ⟨10525704377622791224328045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7017136251748527482885363 10525704377622791224328045)
                    ·
                      refine ⟨3947139141608546709123017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10525704377622791224328045 3947139141608546709123017)
                      ·
                        rfl

theorem cell23_7687026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_7687026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687026 prefixEnd_7687026 := by exact prefixLift 7687026
  have htrace : WordTrace (prefixWord ++ tailWord_7687026) baseStart_7687026 baseEnd_7687026 := by
    simpa [prefixWord, tailWord_7687026, baseEnd_7687026] using wordTrace_append hprefix tailTrace_7687026
  have hstable : (prefixWord ++ tailWord_7687026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687026).length < 2 ^ (prefixWord ++ tailWord_7687026).sum := by decide
  have hdescent : baseEnd_7687026 < baseStart_7687026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687069 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_7687069 : Nat := 118140960795 + 7687069 * 2 ^ 59
def prefixEnd_7687069 : Nat := 4983230072969 + 3 ^ 40 * 7687069 * 2
def baseEnd_7687069 : Nat := 3947161221276690040885319

theorem tailTrace_7687069 : CollatzResearch.WordTrace tailWord_7687069 prefixEnd_7687069 3947161221276690040885319 := by
  unfold tailWord_7687069
  simp only [CollatzResearch.WordTrace]
  refine ⟨280370439788069334709232261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186913626525379556472821507 280370439788069334709232261)
  ·
    refine ⟨52569457460263000257981049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280370439788069334709232261 52569457460263000257981049)
    ·
      refine ⟨39427093095197250193485787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52569457460263000257981049 39427093095197250193485787)
      ·
        refine ⟨59140639642795875290228681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39427093095197250193485787 59140639642795875290228681)
        ·
          refine ⟨44355479732096906467671511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59140639642795875290228681 44355479732096906467671511)
          ·
            refine ⟨66533219598145359701507267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44355479732096906467671511 66533219598145359701507267)
            ·
              refine ⟨99799829397218039552260901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66533219598145359701507267 99799829397218039552260901)
              ·
                refine ⟨18712468011978382416048919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99799829397218039552260901 18712468011978382416048919)
                ·
                  refine ⟨28068702017967573624073379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18712468011978382416048919 28068702017967573624073379)
                  ·
                    refine ⟨42103053026951360436110069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28068702017967573624073379 42103053026951360436110069)
                    ·
                      refine ⟨3947161221276690040885319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42103053026951360436110069 3947161221276690040885319)
                      ·
                        rfl

theorem cell23_7687069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_7687069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687069 prefixEnd_7687069 := by exact prefixLift 7687069
  have htrace : WordTrace (prefixWord ++ tailWord_7687069) baseStart_7687069 baseEnd_7687069 := by
    simpa [prefixWord, tailWord_7687069, baseEnd_7687069] using wordTrace_append hprefix tailTrace_7687069
  have hstable : (prefixWord ++ tailWord_7687069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687069).length < 2 ^ (prefixWord ++ tailWord_7687069).sum := by decide
  have hdescent : baseEnd_7687069 < baseStart_7687069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687072 : List Nat := [2, 1, 1, 4, 1, 1, 3, 10]
def baseStart_7687072 : Nat := 118140960795 + 7687072 * 2 ^ 59
def prefixEnd_7687072 : Nat := 4983230072969 + 3 ^ 40 * 7687072 * 2
def baseEnd_7687072 : Nat := 146191213396987167746215

theorem tailTrace_7687072 : CollatzResearch.WordTrace tailWord_7687072 prefixEnd_7687072 146191213396987167746215 := by
  unfold tailWord_7687072
  simp only [CollatzResearch.WordTrace]
  refine ⟨140185274603529233110795735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186913699471372310814394313 140185274603529233110795735)
  ·
    refine ⟨210277911905293849666193603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140185274603529233110795735 210277911905293849666193603)
    ·
      refine ⟨315416867857940774499290405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210277911905293849666193603 315416867857940774499290405)
      ·
        refine ⟨59140662723363895218616951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315416867857940774499290405 59140662723363895218616951)
        ·
          refine ⟨88710994085045842827925427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59140662723363895218616951 88710994085045842827925427)
          ·
            refine ⟨133066491127568764241888141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88710994085045842827925427 133066491127568764241888141)
            ·
              refine ⟨49899934172838286590708053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133066491127568764241888141 49899934172838286590708053)
              ·
                refine ⟨146191213396987167746215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49899934172838286590708053 146191213396987167746215)
                ·
                  rfl

theorem cell23_7687072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 10].length) (baseStart_7687072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687072 prefixEnd_7687072 := by exact prefixLift 7687072
  have htrace : WordTrace (prefixWord ++ tailWord_7687072) baseStart_7687072 baseEnd_7687072 := by
    simpa [prefixWord, tailWord_7687072, baseEnd_7687072] using wordTrace_append hprefix tailTrace_7687072
  have hstable : (prefixWord ++ tailWord_7687072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687072).length < 2 ^ (prefixWord ++ tailWord_7687072).sum := by decide
  have hdescent : baseEnd_7687072 < baseStart_7687072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687076 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_7687076 : Nat := 118140960795 + 7687076 * 2 ^ 59
def prefixEnd_7687076 : Nat := 4983230072969 + 3 ^ 40 * 7687076 * 2
def baseEnd_7687076 : Nat := 1315721605213757171165929

theorem tailTrace_7687076 : CollatzResearch.WordTrace tailWord_7687076 prefixEnd_7687076 1315721605213757171165929 := by
  unfold tailWord_7687076
  simp only [CollatzResearch.WordTrace]
  refine ⟨140185347549521987452368541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186913796732695983269824721 140185347549521987452368541)
  ·
    refine ⟨52569505331070745294638203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140185347549521987452368541 52569505331070745294638203)
    ·
      refine ⟨78854257996606117941957305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52569505331070745294638203 78854257996606117941957305)
      ·
        refine ⟨59140693497454588456467979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78854257996606117941957305 59140693497454588456467979)
        ·
          refine ⟨88711040246181882684701969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59140693497454588456467979 88711040246181882684701969)
          ·
            refine ⟨66533280184636412013526477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88711040246181882684701969 66533280184636412013526477)
            ·
              refine ⟨24949980069238654505072429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66533280184636412013526477 24949980069238654505072429)
              ·
                refine ⟨9356242525964495439402161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24949980069238654505072429 9356242525964495439402161)
                ·
                  refine ⟨7017181894473371579551621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9356242525964495439402161 7017181894473371579551621)
                  ·
                    refine ⟨1315721605213757171165929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7017181894473371579551621 1315721605213757171165929)
                    ·
                      rfl

theorem cell23_7687076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_7687076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687076 prefixEnd_7687076 := by exact prefixLift 7687076
  have htrace : WordTrace (prefixWord ++ tailWord_7687076) baseStart_7687076 baseEnd_7687076 := by
    simpa [prefixWord, tailWord_7687076, baseEnd_7687076] using wordTrace_append hprefix tailTrace_7687076
  have hstable : (prefixWord ++ tailWord_7687076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687076).length < 2 ^ (prefixWord ++ tailWord_7687076).sum := by decide
  have hdescent : baseEnd_7687076 < baseStart_7687076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687133 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_7687133 : Nat := 118140960795 + 7687133 * 2 ^ 59
def prefixEnd_7687133 : Nat := 4983230072969 + 3 ^ 40 * 7687133 * 2
def baseEnd_7687133 : Nat := 3947194084038577790485025

theorem tailTrace_7687133 : CollatzResearch.WordTrace tailWord_7687133 prefixEnd_7687133 3947194084038577790485025 := by
  unfold tailWord_7687133
  simp only [CollatzResearch.WordTrace]
  refine ⟨280372774059837473639562053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186915182706558315759708035 280372774059837473639562053)
  ·
    refine ⟨52569895136219526307417885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280372774059837473639562053 52569895136219526307417885)
    ·
      refine ⟨19713710676082322365281707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52569895136219526307417885 19713710676082322365281707)
      ·
        refine ⟨29570566014123483547922561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19713710676082322365281707 29570566014123483547922561)
        ·
          refine ⟨22177924510592612660941921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29570566014123483547922561 22177924510592612660941921)
          ·
            refine ⟨16633443382944459495706441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22177924510592612660941921 16633443382944459495706441)
            ·
              refine ⟨12475082537208344621779831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16633443382944459495706441 12475082537208344621779831)
              ·
                refine ⟨18712623805812516932669747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12475082537208344621779831 18712623805812516932669747)
                ·
                  refine ⟨28068935708718775399004621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18712623805812516932669747 28068935708718775399004621)
                  ·
                    refine ⟨10525850890769540774626733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28068935708718775399004621 10525850890769540774626733)
                    ·
                      refine ⟨3947194084038577790485025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10525850890769540774626733 3947194084038577790485025)
                      ·
                        rfl

theorem cell23_7687133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_7687133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687133 prefixEnd_7687133 := by exact prefixLift 7687133
  have htrace : WordTrace (prefixWord ++ tailWord_7687133) baseStart_7687133 baseEnd_7687133 := by
    simpa [prefixWord, tailWord_7687133, baseEnd_7687133] using wordTrace_append hprefix tailTrace_7687133
  have hstable : (prefixWord ++ tailWord_7687133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687133).length < 2 ^ (prefixWord ++ tailWord_7687133).sum := by decide
  have hdescent : baseEnd_7687133 < baseStart_7687133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687139 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 4]
def baseStart_7687139 : Nat := 118140960795 + 7687139 * 2 ^ 59
def prefixEnd_7687139 : Nat := 4983230072969 + 3 ^ 40 * 7687139 * 2
def baseEnd_7687139 : Nat := 3947197164922504767009997

theorem tailTrace_7687139 : CollatzResearch.WordTrace tailWord_7687139 prefixEnd_7687139 3947197164922504767009997 := by
  unfold tailWord_7687139
  simp only [CollatzResearch.WordTrace]
  refine ⟨280372992897815736664280471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186915328598543824442853647 280372992897815736664280471)
  ·
    refine ⟨420559489346723604996420707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280372992897815736664280471 420559489346723604996420707)
    ·
      refine ⟨630839234020085407494631061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420559489346723604996420707 630839234020085407494631061)
      ·
        refine ⟨29570589094691503476310831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 630839234020085407494631061 29570589094691503476310831)
        ·
          refine ⟨44355883642037255214466247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29570589094691503476310831 44355883642037255214466247)
          ·
            refine ⟨66533825463055882821699371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44355883642037255214466247 66533825463055882821699371)
            ·
              refine ⟨99800738194583824232549057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66533825463055882821699371 99800738194583824232549057)
              ·
                refine ⟨74850553645937868174411793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99800738194583824232549057 74850553645937868174411793)
                ·
                  refine ⟨56137915234453401130808845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74850553645937868174411793 56137915234453401130808845)
                  ·
                    refine ⟨21051718212920025424053317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56137915234453401130808845 21051718212920025424053317)
                    ·
                      refine ⟨3947197164922504767009997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21051718212920025424053317 3947197164922504767009997)
                      ·
                        rfl

theorem cell23_7687139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_7687139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687139 prefixEnd_7687139 := by exact prefixLift 7687139
  have htrace : WordTrace (prefixWord ++ tailWord_7687139) baseStart_7687139 baseEnd_7687139 := by
    simpa [prefixWord, tailWord_7687139, baseEnd_7687139] using wordTrace_append hprefix tailTrace_7687139
  have hstable : (prefixWord ++ tailWord_7687139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687139).length < 2 ^ (prefixWord ++ tailWord_7687139).sum := by decide
  have hdescent : baseEnd_7687139 < baseStart_7687139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687143 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_7687143 : Nat := 118140960795 + 7687143 * 2 ^ 59
def prefixEnd_7687143 : Nat := 4983230072969 + 3 ^ 40 * 7687143 * 2
def baseEnd_7687143 : Nat := 3947199218845122751359979

theorem tailTrace_7687143 : CollatzResearch.WordTrace tailWord_7687143 prefixEnd_7687143 3947199218845122751359979 := by
  unfold tailWord_7687143
  simp only [CollatzResearch.WordTrace]
  refine ⟨280373138789801245347426083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186915425859867496898284055 280373138789801245347426083)
  ·
    refine ⟨420559708184701868021139125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280373138789801245347426083 420559708184701868021139125)
    ·
      refine ⟨39427472642315800126981793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 420559708184701868021139125 39427472642315800126981793)
      ·
        refine ⟨29570604481736850095236345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39427472642315800126981793 29570604481736850095236345)
        ·
          refine ⟨22177953361302637571427259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29570604481736850095236345 22177953361302637571427259)
          ·
            refine ⟨33266930041953956357140889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22177953361302637571427259 33266930041953956357140889)
            ·
              refine ⟨24950197531465467267855667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33266930041953956357140889 24950197531465467267855667)
              ·
                refine ⟨37425296297198200901783501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24950197531465467267855667 37425296297198200901783501)
                ·
                  refine ⟨14034486111449325338168813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37425296297198200901783501 14034486111449325338168813)
                  ·
                    refine ⟨5262932291793497001813305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14034486111449325338168813 5262932291793497001813305)
                    ·
                      refine ⟨3947199218845122751359979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262932291793497001813305 3947199218845122751359979)
                      ·
                        rfl

theorem cell23_7687143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_7687143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687143 prefixEnd_7687143 := by exact prefixLift 7687143
  have htrace : WordTrace (prefixWord ++ tailWord_7687143) baseStart_7687143 baseEnd_7687143 := by
    simpa [prefixWord, tailWord_7687143, baseEnd_7687143] using wordTrace_append hprefix tailTrace_7687143
  have hstable : (prefixWord ++ tailWord_7687143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687143).length < 2 ^ (prefixWord ++ tailWord_7687143).sum := by decide
  have hdescent : baseEnd_7687143 < baseStart_7687143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687154 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7687154 : Nat := 118140960795 + 7687154 * 2 ^ 59
def prefixEnd_7687154 : Nat := 4983230072969 + 3 ^ 40 * 7687154 * 2
def baseEnd_7687154 : Nat := 3947204867132322208322429

theorem tailTrace_7687154 : CollatzResearch.WordTrace tailWord_7687154 prefixEnd_7687154 3947204867132322208322429 := by
  unfold tailWord_7687154
  simp only [CollatzResearch.WordTrace]
  refine ⟨70093384998190348556519129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186915693328507596150717677 70093384998190348556519129)
  ·
    refine ⟨52570038748642761417389347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70093384998190348556519129 52570038748642761417389347)
    ·
      refine ⟨78855058122964142126084021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52570038748642761417389347 78855058122964142126084021)
      ·
        refine ⟨7392661699027888324320377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78855058122964142126084021 7392661699027888324320377)
        ·
          refine ⟨5544496274270916243240283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7392661699027888324320377 5544496274270916243240283)
          ·
            refine ⟨8316744411406374364860425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5544496274270916243240283 8316744411406374364860425)
            ·
              refine ⟨6237558308554780773645319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8316744411406374364860425 6237558308554780773645319)
              ·
                refine ⟨9356337462832171160467979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6237558308554780773645319 9356337462832171160467979)
                ·
                  refine ⟨14034506194248256740701969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9356337462832171160467979 14034506194248256740701969)
                  ·
                    refine ⟨10525879645686192555526477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14034506194248256740701969 10525879645686192555526477)
                    ·
                      refine ⟨3947204867132322208322429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10525879645686192555526477 3947204867132322208322429)
                      ·
                        rfl

theorem cell23_7687154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7687154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687154 prefixEnd_7687154 := by exact prefixLift 7687154
  have htrace : WordTrace (prefixWord ++ tailWord_7687154) baseStart_7687154 baseEnd_7687154 := by
    simpa [prefixWord, tailWord_7687154, baseEnd_7687154] using wordTrace_append hprefix tailTrace_7687154
  have hstable : (prefixWord ++ tailWord_7687154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687154).length < 2 ^ (prefixWord ++ tailWord_7687154).sum := by decide
  have hdescent : baseEnd_7687154 < baseStart_7687154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687173 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 4, 2, 2]
def baseStart_7687173 : Nat := 118140960795 + 7687173 * 2 ^ 59
def prefixEnd_7687173 : Nat := 4983230072969 + 3 ^ 40 * 7687173 * 2
def baseEnd_7687173 : Nat := 3947214623264757633984841

theorem tailTrace_7687173 : CollatzResearch.WordTrace tailWord_7687173 prefixEnd_7687173 3947214623264757633984841 := by
  unfold tailWord_7687173
  simp only [CollatzResearch.WordTrace]
  refine ⟨280374232979692560471018173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186916155319795040314012115 280374232979692560471018173)
  ·
    refine ⟨105140337367384710176631815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280374232979692560471018173 105140337367384710176631815)
    ·
      refine ⟨157710506051077065264947723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105140337367384710176631815 157710506051077065264947723)
      ·
        refine ⟨236565759076615597897421585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157710506051077065264947723 236565759076615597897421585)
        ·
          refine ⟨177424319307461698423066189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236565759076615597897421585 177424319307461698423066189)
          ·
            refine ⟨66534119740298136908649821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177424319307461698423066189 66534119740298136908649821)
            ·
              refine ⟨24950294902611801340743683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66534119740298136908649821 24950294902611801340743683)
              ·
                refine ⟨37425442353917702011115525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24950294902611801340743683 37425442353917702011115525)
                ·
                  refine ⟨7017270441359569127084161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37425442353917702011115525 7017270441359569127084161)
                  ·
                    refine ⟨5262952831019676845313121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7017270441359569127084161 5262952831019676845313121)
                    ·
                      refine ⟨3947214623264757633984841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5262952831019676845313121 3947214623264757633984841)
                      ·
                        rfl

theorem cell23_7687173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 2, 2].length) (baseStart_7687173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687173 prefixEnd_7687173 := by exact prefixLift 7687173
  have htrace : WordTrace (prefixWord ++ tailWord_7687173) baseStart_7687173 baseEnd_7687173 := by
    simpa [prefixWord, tailWord_7687173, baseEnd_7687173] using wordTrace_append hprefix tailTrace_7687173
  have hstable : (prefixWord ++ tailWord_7687173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687173).length < 2 ^ (prefixWord ++ tailWord_7687173).sum := by decide
  have hdescent : baseEnd_7687173 < baseStart_7687173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687179 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 7]
def baseStart_7687179 : Nat := 118140960795 + 7687179 * 2 ^ 59
def prefixEnd_7687179 : Nat := 4983230072969 + 3 ^ 40 * 7687179 * 2
def baseEnd_7687179 : Nat := 438579744905409401167757

theorem tailTrace_7687179 : CollatzResearch.WordTrace tailWord_7687179 prefixEnd_7687179 438579744905409401167757 := by
  unfold tailWord_7687179
  simp only [CollatzResearch.WordTrace]
  refine ⟨280374451817670823495736591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186916301211780548997157727 280374451817670823495736591)
  ·
    refine ⟨420561677726506235243604887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280374451817670823495736591 420561677726506235243604887)
    ·
      refine ⟨630842516589759352865407331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420561677726506235243604887 630842516589759352865407331)
      ·
        refine ⟨946263774884639029298110997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630842516589759352865407331 946263774884639029298110997)
        ·
          refine ⟨44356114447717454498348953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 946263774884639029298110997 44356114447717454498348953)
          ·
            refine ⟨33267085835788090873761715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44356114447717454498348953 33267085835788090873761715)
            ·
              refine ⟨49900628753682136310642573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33267085835788090873761715 49900628753682136310642573)
              ·
                refine ⟨18712735782630801116490965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49900628753682136310642573 18712735782630801116490965)
                ·
                  refine ⟨438579744905409401167757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18712735782630801116490965 438579744905409401167757)
                  ·
                    rfl

theorem cell23_7687179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 7].length) (baseStart_7687179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687179 prefixEnd_7687179 := by exact prefixLift 7687179
  have htrace : WordTrace (prefixWord ++ tailWord_7687179) baseStart_7687179 baseEnd_7687179 := by
    simpa [prefixWord, tailWord_7687179, baseEnd_7687179] using wordTrace_append hprefix tailTrace_7687179
  have hstable : (prefixWord ++ tailWord_7687179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687179).length < 2 ^ (prefixWord ++ tailWord_7687179).sum := by decide
  have hdescent : baseEnd_7687179 < baseStart_7687179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687219 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 5]
def baseStart_7687219 : Nat := 118140960795 + 7687219 * 2 ^ 59
def prefixEnd_7687219 : Nat := 4983230072969 + 3 ^ 40 * 7687219 * 2
def baseEnd_7687219 : Nat := 3947238243374864454009629

theorem tailTrace_7687219 : CollatzResearch.WordTrace tailWord_7687219 prefixEnd_7687219 3947238243374864454009629 := by
  unfold tailWord_7687219
  simp only [CollatzResearch.WordTrace]
  refine ⟨280375910737525910327192711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186917273825017273551461807 280375910737525910327192711)
  ·
    refine ⟨420563866106288865490789067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280375910737525910327192711 420563866106288865490789067)
    ·
      refine ⟨630845799159433298236183601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420563866106288865490789067 630845799159433298236183601)
      ·
        refine ⟨473134349369574973677137701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630845799159433298236183601 473134349369574973677137701)
        ·
          refine ⟨88712690506795307564463319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 473134349369574973677137701 88712690506795307564463319)
          ·
            refine ⟨133069035760192961346694979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88712690506795307564463319 133069035760192961346694979)
            ·
              refine ⟨199603553640289442020042469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133069035760192961346694979 199603553640289442020042469)
              ·
                refine ⟨37425666307554270378757963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199603553640289442020042469 37425666307554270378757963)
                ·
                  refine ⟨56138499461331405568136945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37425666307554270378757963 56138499461331405568136945)
                  ·
                    refine ⟨42103874595998554176102709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56138499461331405568136945 42103874595998554176102709)
                    ·
                      refine ⟨3947238243374864454009629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42103874595998554176102709 3947238243374864454009629)
                      ·
                        rfl

theorem cell23_7687219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_7687219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687219 prefixEnd_7687219 := by exact prefixLift 7687219
  have htrace : WordTrace (prefixWord ++ tailWord_7687219) baseStart_7687219 baseEnd_7687219 := by
    simpa [prefixWord, tailWord_7687219, baseEnd_7687219] using wordTrace_append hprefix tailTrace_7687219
  have hstable : (prefixWord ++ tailWord_7687219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687219).length < 2 ^ (prefixWord ++ tailWord_7687219).sum := by decide
  have hdescent : baseEnd_7687219 < baseStart_7687219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687246 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_7687246 : Nat := 118140960795 + 7687246 * 2 ^ 59
def prefixEnd_7687246 : Nat := 4983230072969 + 3 ^ 40 * 7687246 * 2
def baseEnd_7687246 : Nat := 3947252107352535848372005

theorem tailTrace_7687246 : CollatzResearch.WordTrace tailWord_7687246 prefixEnd_7687246 3947252107352535848372005 := by
  unfold tailWord_7687246
  simp only [CollatzResearch.WordTrace]
  refine ⟨35047111938553511742303199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186917930338952062625617061 35047111938553511742303199)
  ·
    refine ⟨52570667907830267613454799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35047111938553511742303199 52570667907830267613454799)
    ·
      refine ⟨78856001861745401420182199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52570667907830267613454799 78856001861745401420182199)
      ·
        refine ⟨118284002792618102130273299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78856001861745401420182199 118284002792618102130273299)
        ·
          refine ⟨177426004188927153195409949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118284002792618102130273299 177426004188927153195409949)
          ·
            refine ⟨66534751570847682448278731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177426004188927153195409949 66534751570847682448278731)
            ·
              refine ⟨99802127356271523672418097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66534751570847682448278731 99802127356271523672418097)
              ·
                refine ⟨74851595517203642754313573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99802127356271523672418097 74851595517203642754313573)
                ·
                  refine ⟨14034674159475683016433795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74851595517203642754313573 14034674159475683016433795)
                  ·
                    refine ⟨21052011239213524524650693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14034674159475683016433795 21052011239213524524650693)
                    ·
                      refine ⟨3947252107352535848372005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21052011239213524524650693 3947252107352535848372005)
                      ·
                        rfl

theorem cell23_7687246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_7687246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687246 prefixEnd_7687246 := by exact prefixLift 7687246
  have htrace : WordTrace (prefixWord ++ tailWord_7687246) baseStart_7687246 baseEnd_7687246 := by
    simpa [prefixWord, tailWord_7687246, baseEnd_7687246] using wordTrace_append hprefix tailTrace_7687246
  have hstable : (prefixWord ++ tailWord_7687246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687246).length < 2 ^ (prefixWord ++ tailWord_7687246).sum := by decide
  have hdescent : baseEnd_7687246 < baseStart_7687246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687256 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 5, 4]
def baseStart_7687256 : Nat := 118140960795 + 7687256 * 2 ^ 59
def prefixEnd_7687256 : Nat := 4983230072969 + 3 ^ 40 * 7687256 * 2
def baseEnd_7687256 : Nat := 1315752414053026936415653

theorem tailTrace_7687256 : CollatzResearch.WordTrace tailWord_7687256 prefixEnd_7687256 1315752414053026936415653 := by
  unfold tailWord_7687256
  simp only [CollatzResearch.WordTrace]
  refine ⟨140188630119195932823144811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186918173492261243764193081 140188630119195932823144811)
  ·
    refine ⟨210282945178793899234717217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140188630119195932823144811 210282945178793899234717217)
    ·
      refine ⟨157712208884095424426037913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210282945178793899234717217 157712208884095424426037913)
      ·
        refine ⟨118284156663071568319528435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157712208884095424426037913 118284156663071568319528435)
        ·
          refine ⟨177426234994607352479292653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118284156663071568319528435 177426234994607352479292653)
          ·
            refine ⟨66534838122977757179734745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177426234994607352479292653 66534838122977757179734745)
            ·
              refine ⟨49901128592233317884801059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66534838122977757179734745 49901128592233317884801059)
              ·
                refine ⟨74851692888349976827201589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49901128592233317884801059 74851692888349976827201589)
                ·
                  refine ⟨7017346208282810327550149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74851692888349976827201589 7017346208282810327550149)
                  ·
                    refine ⟨1315752414053026936415653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7017346208282810327550149 1315752414053026936415653)
                    ·
                      rfl

theorem cell23_7687256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_7687256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687256 prefixEnd_7687256 := by exact prefixLift 7687256
  have htrace : WordTrace (prefixWord ++ tailWord_7687256) baseStart_7687256 baseEnd_7687256 := by
    simpa [prefixWord, tailWord_7687256, baseEnd_7687256] using wordTrace_append hprefix tailTrace_7687256
  have hstable : (prefixWord ++ tailWord_7687256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687256).length < 2 ^ (prefixWord ++ tailWord_7687256).sum := by decide
  have hdescent : baseEnd_7687256 < baseStart_7687256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687333 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 1, 5]
def baseStart_7687333 : Nat := 118140960795 + 7687333 * 2 ^ 59
def prefixEnd_7687333 : Nat := 4983230072969 + 3 ^ 40 * 7687333 * 2
def baseEnd_7687333 : Nat := 1315765593389825669328035

theorem tailTrace_7687333 : CollatzResearch.WordTrace tailWord_7687333 prefixEnd_7687333 1315765593389825669328035 := by
  unfold tailWord_7687333
  simp only [CollatzResearch.WordTrace]
  refine ⟨280380068659112907796842653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186920045772741938531228435 280380068659112907796842653)
  ·
    refine ⟨105142525747167340423815995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280380068659112907796842653 105142525747167340423815995)
    ·
      refine ⟨157713788620751010635723993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105142525747167340423815995 157713788620751010635723993)
      ·
        refine ⟨118285341465563257976792995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157713788620751010635723993 118285341465563257976792995)
        ·
          refine ⟨177428012198344886965189493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118285341465563257976792995 177428012198344886965189493)
          ·
            refine ⟨16633876143594833152986515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177428012198344886965189493 16633876143594833152986515)
            ·
              refine ⟨24950814215392249729479773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16633876143594833152986515 24950814215392249729479773)
              ·
                refine ⟨9356555330772093648554915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24950814215392249729479773 9356555330772093648554915)
                ·
                  refine ⟨14034832996158140472832373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9356555330772093648554915 14034832996158140472832373)
                  ·
                    refine ⟨1315765593389825669328035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14034832996158140472832373 1315765593389825669328035)
                    ·
                      rfl

theorem cell23_7687333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_7687333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687333 prefixEnd_7687333 := by exact prefixLift 7687333
  have htrace : WordTrace (prefixWord ++ tailWord_7687333) baseStart_7687333 baseEnd_7687333 := by
    simpa [prefixWord, tailWord_7687333, baseEnd_7687333] using wordTrace_append hprefix tailTrace_7687333
  have hstable : (prefixWord ++ tailWord_7687333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687333).length < 2 ^ (prefixWord ++ tailWord_7687333).sum := by decide
  have hdescent : baseEnd_7687333 < baseStart_7687333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687370 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_7687370 : Nat := 118140960795 + 7687370 * 2 ^ 59
def prefixEnd_7687370 : Nat := 4983230072969 + 3 ^ 40 * 7687370 * 2
def baseEnd_7687370 : Nat := 3947315778953693363221435

theorem tailTrace_7687370 : CollatzResearch.WordTrace tailWord_7687370 prefixEnd_7687370 3947315778953693363221435 := by
  unfold tailWord_7687370
  simp only [CollatzResearch.WordTrace]
  refine ⟨70095354539994715778984891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186920945439985908743959709 70095354539994715778984891)
  ·
    refine ⟨105143031809992073668477337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70095354539994715778984891 105143031809992073668477337)
    ·
      refine ⟨78857273857494055251358003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105143031809992073668477337 78857273857494055251358003)
      ·
        refine ⟨118285910786241082877037005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78857273857494055251358003 118285910786241082877037005)
        ·
          refine ⟨44357216544840406078888877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118285910786241082877037005 44357216544840406078888877)
          ·
            refine ⟨16633956204315152279583329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44357216544840406078888877 16633956204315152279583329)
            ·
              refine ⟨12475467153236364209687497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16633956204315152279583329 12475467153236364209687497)
              ·
                refine ⟨9356600364927273157265623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12475467153236364209687497 9356600364927273157265623)
                ·
                  refine ⟨14034900547390909735898435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9356600364927273157265623 14034900547390909735898435)
                  ·
                    refine ⟨21052350821086364603847653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14034900547390909735898435 21052350821086364603847653)
                    ·
                      refine ⟨3947315778953693363221435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21052350821086364603847653 3947315778953693363221435)
                      ·
                        rfl

theorem cell23_7687370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_7687370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687370 prefixEnd_7687370 := by exact prefixLift 7687370
  have htrace : WordTrace (prefixWord ++ tailWord_7687370) baseStart_7687370 baseEnd_7687370 := by
    simpa [prefixWord, tailWord_7687370, baseEnd_7687370] using wordTrace_append hprefix tailTrace_7687370
  have hstable : (prefixWord ++ tailWord_7687370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687370).length < 2 ^ (prefixWord ++ tailWord_7687370).sum := by decide
  have hdescent : baseEnd_7687370 < baseStart_7687370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687460 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 3, 4, 2]
def baseStart_7687460 : Nat := 118140960795 + 7687460 * 2 ^ 59
def prefixEnd_7687460 : Nat := 4983230072969 + 3 ^ 40 * 7687460 * 2
def baseEnd_7687460 : Nat := 3947361992212598011096021

theorem tailTrace_7687460 : CollatzResearch.WordTrace tailWord_7687460 prefixEnd_7687460 3947361992212598011096021 := by
  unfold tailWord_7687460
  simp only [CollatzResearch.WordTrace]
  refine ⟨140192350364826404243357917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186923133819768538991143889 140192350364826404243357917)
  ·
    refine ⟨52572131386809901591259219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140192350364826404243357917 52572131386809901591259219)
    ·
      refine ⟨78858197080214852386888829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52572131386809901591259219 78858197080214852386888829)
      ·
        refine ⟨29571823905080569645083311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78858197080214852386888829 29571823905080569645083311)
        ·
          refine ⟨44357735857620854467624967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29571823905080569645083311 44357735857620854467624967)
          ·
            refine ⟨66536603786431281701437451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44357735857620854467624967 66536603786431281701437451)
            ·
              refine ⟨99804905679646922552156177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66536603786431281701437451 99804905679646922552156177)
              ·
                refine ⟨74853679259735191914117133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99804905679646922552156177 74853679259735191914117133)
                ·
                  refine ⟨28070129722400696967793925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74853679259735191914117133 28070129722400696967793925)
                  ·
                    refine ⟨5263149322950130681461361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28070129722400696967793925 5263149322950130681461361)
                    ·
                      refine ⟨3947361992212598011096021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263149322950130681461361 3947361992212598011096021)
                      ·
                        rfl

theorem cell23_7687460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_7687460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687460 prefixEnd_7687460 := by exact prefixLift 7687460
  have htrace : WordTrace (prefixWord ++ tailWord_7687460) baseStart_7687460 baseEnd_7687460 := by
    simpa [prefixWord, tailWord_7687460, baseEnd_7687460] using wordTrace_append hprefix tailTrace_7687460
  have hstable : (prefixWord ++ tailWord_7687460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687460).length < 2 ^ (prefixWord ++ tailWord_7687460).sum := by decide
  have hdescent : baseEnd_7687460 < baseStart_7687460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687473 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_7687473 : Nat := 118140960795 + 7687473 * 2 ^ 59
def prefixEnd_7687473 : Nat := 4983230072969 + 3 ^ 40 * 7687473 * 2
def baseEnd_7687473 : Nat := 3947368667461106460233461

theorem tailTrace_7687473 : CollatzResearch.WordTrace tailWord_7687473 prefixEnd_7687473 3947368667461106460233461 := by
  unfold tailWord_7687473
  simp only [CollatzResearch.WordTrace]
  refine ⟨280385174878605711706939073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186923449919070474471292715 280385174878605711706939073)
  ·
    refine ⟨210288881158954283780204305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280385174878605711706939073 210288881158954283780204305)
    ·
      refine ⟨157716660869215712835153229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210288881158954283780204305 157716660869215712835153229)
      ·
        refine ⟨59143747825955892313182461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157716660869215712835153229 59143747825955892313182461)
        ·
          refine ⟨22178905434733459617443423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59143747825955892313182461 22178905434733459617443423)
          ·
            refine ⟨33268358152100189426165135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22178905434733459617443423 33268358152100189426165135)
            ·
              refine ⟨49902537228150284139247703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33268358152100189426165135 49902537228150284139247703)
              ·
                refine ⟨74853805842225426208871555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49902537228150284139247703 74853805842225426208871555)
                ·
                  refine ⟨112280708763338139313307333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74853805842225426208871555 112280708763338139313307333)
                  ·
                    refine ⟨21052632893125901121245125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112280708763338139313307333 21052632893125901121245125)
                    ·
                      refine ⟨3947368667461106460233461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21052632893125901121245125 3947368667461106460233461)
                      ·
                        rfl

theorem cell23_7687473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_7687473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687473 prefixEnd_7687473 := by exact prefixLift 7687473
  have htrace : WordTrace (prefixWord ++ tailWord_7687473) baseStart_7687473 baseEnd_7687473 := by
    simpa [prefixWord, tailWord_7687473, baseEnd_7687473] using wordTrace_append hprefix tailTrace_7687473
  have hstable : (prefixWord ++ tailWord_7687473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687473).length < 2 ^ (prefixWord ++ tailWord_7687473).sum := by decide
  have hdescent : baseEnd_7687473 < baseStart_7687473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687477 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_7687477 : Nat := 118140960795 + 7687477 * 2 ^ 59
def prefixEnd_7687477 : Nat := 4983230072969 + 3 ^ 40 * 7687477 * 2
def baseEnd_7687477 : Nat := 3947370721383724444583443

theorem tailTrace_7687477 : CollatzResearch.WordTrace tailWord_7687477 prefixEnd_7687477 3947370721383724444583443 := by
  unfold tailWord_7687477
  simp only [CollatzResearch.WordTrace]
  refine ⟨280385320770591220390084685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186923547180394146926723123 280385320770591220390084685)
  ·
    refine ⟨105144495288971707646281757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280385320770591220390084685 105144495288971707646281757)
    ·
      refine ⟨39429185733364390367355659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105144495288971707646281757 39429185733364390367355659)
      ·
        refine ⟨59143778600046585551033489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39429185733364390367355659 59143778600046585551033489)
        ·
          refine ⟨44357833950034939163275117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59143778600046585551033489 44357833950034939163275117)
          ·
            refine ⟨16634187731263102186228169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44357833950034939163275117 16634187731263102186228169)
            ·
              refine ⟨12475640798447326639671127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16634187731263102186228169 12475640798447326639671127)
              ·
                refine ⟨18713461197670989959506691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12475640798447326639671127 18713461197670989959506691)
                ·
                  refine ⟨28070191796506484939260037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18713461197670989959506691 28070191796506484939260037)
                  ·
                    refine ⟨5263160961844965926111257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28070191796506484939260037 5263160961844965926111257)
                    ·
                      refine ⟨3947370721383724444583443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263160961844965926111257 3947370721383724444583443)
                      ·
                        rfl

theorem cell23_7687477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_7687477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687477 prefixEnd_7687477 := by exact prefixLift 7687477
  have htrace : WordTrace (prefixWord ++ tailWord_7687477) baseStart_7687477 baseEnd_7687477 := by
    simpa [prefixWord, tailWord_7687477, baseEnd_7687477] using wordTrace_append hprefix tailTrace_7687477
  have hstable : (prefixWord ++ tailWord_7687477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687477).length < 2 ^ (prefixWord ++ tailWord_7687477).sum := by decide
  have hdescent : baseEnd_7687477 < baseStart_7687477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687500 : List Nat := [2, 2, 1, 3, 2, 2, 1, 5, 5]
def baseStart_7687500 : Nat := 118140960795 + 7687500 * 2 ^ 59
def prefixEnd_7687500 : Nat := 4983230072969 + 3 ^ 40 * 7687500 * 2
def baseEnd_7687500 : Nat := 438598059048753094955093

theorem tailTrace_7687500 : CollatzResearch.WordTrace tailWord_7687500 prefixEnd_7687500 438598059048753094955093 := by
  unfold tailWord_7687500
  simp only [CollatzResearch.WordTrace]
  refine ⟨140193079824753947659085977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186924106433005263545447969 140193079824753947659085977)
  ·
    refine ⟨105144809868565460744314483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140193079824753947659085977 105144809868565460744314483)
    ·
      refine ⟨157717214802848191116471725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105144809868565460744314483 157717214802848191116471725)
      ·
        refine ⟨59143955551068071668676897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157717214802848191116471725 59143955551068071668676897)
        ·
          refine ⟨44357966663301053751507673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59143955551068071668676897 44357966663301053751507673)
          ·
            refine ⟨33268474997475790313630755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44357966663301053751507673 33268474997475790313630755)
            ·
              refine ⟨49902712496213685470446133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33268474997475790313630755 49902712496213685470446133)
              ·
                refine ⟨4678379296520033012854325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49902712496213685470446133 4678379296520033012854325)
                ·
                  refine ⟨438598059048753094955093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4678379296520033012854325 438598059048753094955093)
                  ·
                    rfl

theorem cell23_7687500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_7687500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687500 prefixEnd_7687500 := by exact prefixLift 7687500
  have htrace : WordTrace (prefixWord ++ tailWord_7687500) baseStart_7687500 baseEnd_7687500 := by
    simpa [prefixWord, tailWord_7687500, baseEnd_7687500] using wordTrace_append hprefix tailTrace_7687500
  have hstable : (prefixWord ++ tailWord_7687500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687500).length < 2 ^ (prefixWord ++ tailWord_7687500).sum := by decide
  have hdescent : baseEnd_7687500 < baseStart_7687500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687513 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 2, 5]
def baseStart_7687513 : Nat := 118140960795 + 7687513 * 2 ^ 59
def prefixEnd_7687513 : Nat := 4983230072969 + 3 ^ 40 * 7687513 * 2
def baseEnd_7687513 : Nat := 1315796402229095434577759

theorem tailTrace_7687513 : CollatzResearch.WordTrace tailWord_7687513 prefixEnd_7687513 1315796402229095434577759 := by
  unfold tailWord_7687513
  simp only [CollatzResearch.WordTrace]
  refine ⟨280386633798460798538395193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186924422532307199025596795 280386633798460798538395193)
  ·
    refine ⟨210289975348845598903796395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280386633798460798538395193 210289975348845598903796395)
    ·
      refine ⟨315434963023268398355694593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210289975348845598903796395 315434963023268398355694593)
      ·
        refine ⟨236576222267451298766770945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315434963023268398355694593 236576222267451298766770945)
        ·
          refine ⟨177432166700588474075078209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236576222267451298766770945 177432166700588474075078209)
          ·
            refine ⟨133074125025441355556308657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177432166700588474075078209 133074125025441355556308657)
            ·
              refine ⟨99805593769081016667231493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133074125025441355556308657 99805593769081016667231493)
              ·
                refine ⟨18713548831702690625105905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99805593769081016667231493 18713548831702690625105905)
                ·
                  refine ⟨14035161623777017968829429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18713548831702690625105905 14035161623777017968829429)
                  ·
                    refine ⟨1315796402229095434577759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14035161623777017968829429 1315796402229095434577759)
                    ·
                      rfl

theorem cell23_7687513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_7687513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687513 prefixEnd_7687513 := by exact prefixLift 7687513
  have htrace : WordTrace (prefixWord ++ tailWord_7687513) baseStart_7687513 baseEnd_7687513 := by
    simpa [prefixWord, tailWord_7687513, baseEnd_7687513] using wordTrace_append hprefix tailTrace_7687513
  have hstable : (prefixWord ++ tailWord_7687513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687513).length < 2 ^ (prefixWord ++ tailWord_7687513).sum := by decide
  have hdescent : baseEnd_7687513 < baseStart_7687513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687573 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 8]
def baseStart_7687573 : Nat := 118140960795 + 7687573 * 2 ^ 59
def prefixEnd_7687573 : Nat := 4983230072969 + 3 ^ 40 * 7687573 * 2
def baseEnd_7687573 : Nat := 438602223947395118775889

theorem tailTrace_7687573 : CollatzResearch.WordTrace tailWord_7687573 prefixEnd_7687573 438602223947395118775889 := by
  unfold tailWord_7687573
  simp only [CollatzResearch.WordTrace]
  refine ⟨280388822178243428785579373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186925881452162285857052915 280388822178243428785579373)
  ·
    refine ⟨105145808316841285794592265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280388822178243428785579373 105145808316841285794592265)
    ·
      refine ⟨78859356237630964345944199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105145808316841285794592265 78859356237630964345944199)
      ·
        refine ⟨118289034356446446518916299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78859356237630964345944199 118289034356446446518916299)
        ·
          refine ⟨177433551534669669778374449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118289034356446446518916299 177433551534669669778374449)
          ·
            refine ⟨133075163651002252333780837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177433551534669669778374449 133075163651002252333780837)
            ·
              refine ⟨24951593184562922312583907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133075163651002252333780837 24951593184562922312583907)
              ·
                refine ⟨37427389776844383468875861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24951593184562922312583907 37427389776844383468875861)
                ·
                  refine ⟨438602223947395118775889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37427389776844383468875861 438602223947395118775889)
                  ·
                    rfl

theorem cell23_7687573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_7687573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687573 prefixEnd_7687573 := by exact prefixLift 7687573
  have htrace : WordTrace (prefixWord ++ tailWord_7687573) baseStart_7687573 baseEnd_7687573 := by
    simpa [prefixWord, tailWord_7687573, baseEnd_7687573] using wordTrace_append hprefix tailTrace_7687573
  have hstable : (prefixWord ++ tailWord_7687573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687573).length < 2 ^ (prefixWord ++ tailWord_7687573).sum := by decide
  have hdescent : baseEnd_7687573 < baseStart_7687573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687577 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 3, 4]
def baseStart_7687577 : Nat := 118140960795 + 7687577 * 2 ^ 59
def prefixEnd_7687577 : Nat := 4983230072969 + 3 ^ 40 * 7687577 * 2
def baseEnd_7687577 : Nat := 1315807356483058017777661

theorem tailTrace_7687577 : CollatzResearch.WordTrace tailWord_7687577 prefixEnd_7687577 1315807356483058017777661 := by
  unfold tailWord_7687577
  simp only [CollatzResearch.WordTrace]
  refine ⟨280388968070228937468724985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186925978713485958312483323 280388968070228937468724985)
  ·
    refine ⟨210291726052671703101543739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280388968070228937468724985 210291726052671703101543739)
    ·
      refine ⟨315437589079007554652315609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210291726052671703101543739 315437589079007554652315609)
      ·
        refine ⟨236578191809255665989236707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315437589079007554652315609 236578191809255665989236707)
        ·
          refine ⟨354867287713883498983855061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236578191809255665989236707 354867287713883498983855061)
          ·
            refine ⟨8317202055794144507434103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 354867287713883498983855061 8317202055794144507434103)
            ·
              refine ⟨12475803083691216761151155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8317202055794144507434103 12475803083691216761151155)
              ·
                refine ⟨18713704625536825141726733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12475803083691216761151155 18713704625536825141726733)
                ·
                  refine ⟨7017639234576309428147525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18713704625536825141726733 7017639234576309428147525)
                  ·
                    refine ⟨1315807356483058017777661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7017639234576309428147525 1315807356483058017777661)
                    ·
                      rfl

theorem cell23_7687577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 4].length) (baseStart_7687577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687577 prefixEnd_7687577 := by exact prefixLift 7687577
  have htrace : WordTrace (prefixWord ++ tailWord_7687577) baseStart_7687577 baseEnd_7687577 := by
    simpa [prefixWord, tailWord_7687577, baseEnd_7687577] using wordTrace_append hprefix tailTrace_7687577
  have hstable : (prefixWord ++ tailWord_7687577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687577).length < 2 ^ (prefixWord ++ tailWord_7687577).sum := by decide
  have hdescent : baseEnd_7687577 < baseStart_7687577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687627 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 2, 3, 2]
def baseStart_7687627 : Nat := 118140960795 + 7687627 * 2 ^ 59
def prefixEnd_7687627 : Nat := 4983230072969 + 3 ^ 40 * 7687627 * 2
def baseEnd_7687627 : Nat := 3947447743481898857707753

theorem tailTrace_7687627 : CollatzResearch.WordTrace tailWord_7687627 prefixEnd_7687627 3947447743481898857707753 := by
  unfold tailWord_7687627
  simp only [CollatzResearch.WordTrace]
  refine ⟨280390791720047796008045135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186927194480031864005363423 280390791720047796008045135)
  ·
    refine ⟨420586187580071694012067703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280390791720047796008045135 420586187580071694012067703)
    ·
      refine ⟨630879281370107541018101555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420586187580071694012067703 630879281370107541018101555)
      ·
        refine ⟨946318922055161311527152333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630879281370107541018101555 946318922055161311527152333)
        ·
          refine ⟨354869595770685491822682125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 946318922055161311527152333 354869595770685491822682125)
          ·
            refine ⟨133076098414007059433505797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354869595770685491822682125 133076098414007059433505797)
            ·
              refine ⟨24951768452626323643782337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133076098414007059433505797 24951768452626323643782337)
              ·
                refine ⟨18713826339469742732836753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24951768452626323643782337 18713826339469742732836753)
                ·
                  refine ⟨14035369754602307049627565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18713826339469742732836753 14035369754602307049627565)
                  ·
                    refine ⟨5263263657975865143610337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14035369754602307049627565 5263263657975865143610337)
                    ·
                      refine ⟨3947447743481898857707753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263263657975865143610337 3947447743481898857707753)
                      ·
                        rfl

theorem cell23_7687627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 3, 2].length) (baseStart_7687627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687627 prefixEnd_7687627 := by exact prefixLift 7687627
  have htrace : WordTrace (prefixWord ++ tailWord_7687627) baseStart_7687627 baseEnd_7687627 := by
    simpa [prefixWord, tailWord_7687627, baseEnd_7687627] using wordTrace_append hprefix tailTrace_7687627
  have hstable : (prefixWord ++ tailWord_7687627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687627).length < 2 ^ (prefixWord ++ tailWord_7687627).sum := by decide
  have hdescent : baseEnd_7687627 < baseStart_7687627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687640 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_7687640 : Nat := 118140960795 + 7687640 * 2 ^ 59
def prefixEnd_7687640 : Nat := 4983230072969 + 3 ^ 40 * 7687640 * 2
def baseEnd_7687640 : Nat := 3947454418730407306845193

theorem tailTrace_7687640 : CollatzResearch.WordTrace tailWord_7687640 prefixEnd_7687640 3947454418730407306845193 := by
  unfold tailWord_7687640
  simp only [CollatzResearch.WordTrace]
  refine ⟨140195632934500349614134187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186927510579333799485512249 140195632934500349614134187)
  ·
    refine ⟨210293449401750524421201281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140195632934500349614134187 210293449401750524421201281)
    ·
      refine ⟨157720087051312893315900961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210293449401750524421201281 157720087051312893315900961)
      ·
        refine ⟨118290065288484669986925721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157720087051312893315900961 118290065288484669986925721)
        ·
          refine ⟨88717548966363502490194291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118290065288484669986925721 88717548966363502490194291)
          ·
            refine ⟨133076323449545253735291437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88717548966363502490194291 133076323449545253735291437)
            ·
              refine ⟨49903621293579470150734289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133076323449545253735291437 49903621293579470150734289)
              ·
                refine ⟨37427715970184602613050717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49903621293579470150734289 37427715970184602613050717)
                ·
                  refine ⟨14035393488819225979894019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37427715970184602613050717 14035393488819225979894019)
                  ·
                    refine ⟨21053090233228838969841029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14035393488819225979894019 21053090233228838969841029)
                    ·
                      refine ⟨3947454418730407306845193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21053090233228838969841029 3947454418730407306845193)
                      ·
                        rfl

theorem cell23_7687640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_7687640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687640 prefixEnd_7687640 := by exact prefixLift 7687640
  have htrace : WordTrace (prefixWord ++ tailWord_7687640) baseStart_7687640 baseEnd_7687640 := by
    simpa [prefixWord, tailWord_7687640, baseEnd_7687640] using wordTrace_append hprefix tailTrace_7687640
  have hstable : (prefixWord ++ tailWord_7687640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687640).length < 2 ^ (prefixWord ++ tailWord_7687640).sum := by decide
  have hdescent : baseEnd_7687640 < baseStart_7687640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687663 : List Nat := [1, 1, 2, 1, 4, 1, 2, 11]
def baseStart_7687663 : Nat := 118140960795 + 7687663 * 2 ^ 59
def prefixEnd_7687663 : Nat := 4983230072969 + 3 ^ 40 * 7687663 * 2
def baseEnd_7687663 : Nat := 146202452917980026550281

theorem tailTrace_7687663 : CollatzResearch.WordTrace tailWord_7687663 prefixEnd_7687663 146202452917980026550281 := by
  unfold tailWord_7687663
  simp only [CollatzResearch.WordTrace]
  refine ⟨280392104747917374156355643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186928069831944916104237095 280392104747917374156355643)
  ·
    refine ⟨420588157121876061234533465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280392104747917374156355643 420588157121876061234533465)
    ·
      refine ⟨315441117841407045925900099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420588157121876061234533465 315441117841407045925900099)
      ·
        refine ⟨473161676762110568888850149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315441117841407045925900099 473161676762110568888850149)
        ·
          refine ⟨88717814392895731666659403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 473161676762110568888850149 88717814392895731666659403)
          ·
            refine ⟨133076721589343597499989105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88717814392895731666659403 133076721589343597499989105)
            ·
              refine ⟨99807541192007698124991829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133076721589343597499989105 99807541192007698124991829)
              ·
                refine ⟨146202452917980026550281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 99807541192007698124991829 146202452917980026550281)
                ·
                  rfl

theorem cell23_7687663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 11].length) (baseStart_7687663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687663 prefixEnd_7687663 := by exact prefixLift 7687663
  have htrace : WordTrace (prefixWord ++ tailWord_7687663) baseStart_7687663 baseEnd_7687663 := by
    simpa [prefixWord, tailWord_7687663, baseEnd_7687663] using wordTrace_append hprefix tailTrace_7687663
  have hstable : (prefixWord ++ tailWord_7687663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687663).length < 2 ^ (prefixWord ++ tailWord_7687663).sum := by decide
  have hdescent : baseEnd_7687663 < baseStart_7687663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687684 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_7687684 : Nat := 118140960795 + 7687684 * 2 ^ 59
def prefixEnd_7687684 : Nat := 4983230072969 + 3 ^ 40 * 7687684 * 2
def baseEnd_7687684 : Nat := 1315825670626401711564997

theorem tailTrace_7687684 : CollatzResearch.WordTrace tailWord_7687684 prefixEnd_7687684 1315825670626401711564997 := by
  unfold tailWord_7687684
  simp only [CollatzResearch.WordTrace]
  refine ⟨140196435340420647371435053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186928580453894196495246737 140196435340420647371435053)
  ·
    refine ⟨52573663252657742764288145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140196435340420647371435053 52573663252657742764288145)
    ·
      refine ⟨39430247439493307073216109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52573663252657742764288145 39430247439493307073216109)
      ·
        refine ⟨14786342789809990152456041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39430247439493307073216109 14786342789809990152456041)
        ·
          refine ⟨11089757092357492614342031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14786342789809990152456041 11089757092357492614342031)
          ·
            refine ⟨16634635638536238921513047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11089757092357492614342031 16634635638536238921513047)
            ·
              refine ⟨24951953457804358382269571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16634635638536238921513047 24951953457804358382269571)
              ·
                refine ⟨37427930186706537573404357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24951953457804358382269571 37427930186706537573404357)
                ·
                  refine ⟨7017736910007475795013317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37427930186706537573404357 7017736910007475795013317)
                  ·
                    refine ⟨1315825670626401711564997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7017736910007475795013317 1315825670626401711564997)
                    ·
                      rfl

theorem cell23_7687684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_7687684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687684 prefixEnd_7687684 := by exact prefixLift 7687684
  have htrace : WordTrace (prefixWord ++ tailWord_7687684) baseStart_7687684 baseEnd_7687684 := by
    simpa [prefixWord, tailWord_7687684, baseEnd_7687684] using wordTrace_append hprefix tailTrace_7687684
  have hstable : (prefixWord ++ tailWord_7687684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687684).length < 2 ^ (prefixWord ++ tailWord_7687684).sum := by decide
  have hdescent : baseEnd_7687684 < baseStart_7687684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687691 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 3, 2, 2]
def baseStart_7687691 : Nat := 118140960795 + 7687691 * 2 ^ 59
def prefixEnd_7687691 : Nat := 4983230072969 + 3 ^ 40 * 7687691 * 2
def baseEnd_7687691 : Nat := 3947480606243786607307459

theorem tailTrace_7687691 : CollatzResearch.WordTrace tailWord_7687691 prefixEnd_7687691 3947480606243786607307459 := by
  unfold tailWord_7687691
  simp only [CollatzResearch.WordTrace]
  refine ⟨280393125991815934938374927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186928750661210623292249951 280393125991815934938374927)
  ·
    refine ⟨420589688987723902407562391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280393125991815934938374927 420589688987723902407562391)
    ·
      refine ⟨630884533481585853611343587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420589688987723902407562391 630884533481585853611343587)
      ·
        refine ⟨946326800222378780417015381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630884533481585853611343587 946326800222378780417015381)
        ·
          refine ⟨11089767190106001333011899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 946326800222378780417015381 11089767190106001333011899)
          ·
            refine ⟨16634650785159001999517849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11089767190106001333011899 16634650785159001999517849)
            ·
              refine ⟨12475988088869251499638387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16634650785159001999517849 12475988088869251499638387)
              ·
                refine ⟨18713982133303877249457581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12475988088869251499638387 18713982133303877249457581)
                ·
                  refine ⟨7017743299988953968546593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18713982133303877249457581 7017743299988953968546593)
                  ·
                    refine ⟨5263307474991715476409945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7017743299988953968546593 5263307474991715476409945)
                    ·
                      refine ⟨3947480606243786607307459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263307474991715476409945 3947480606243786607307459)
                      ·
                        rfl

theorem cell23_7687691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 2, 2].length) (baseStart_7687691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687691 prefixEnd_7687691 := by exact prefixLift 7687691
  have htrace : WordTrace (prefixWord ++ tailWord_7687691) baseStart_7687691 baseEnd_7687691 := by
    simpa [prefixWord, tailWord_7687691, baseEnd_7687691] using wordTrace_append hprefix tailTrace_7687691
  have hstable : (prefixWord ++ tailWord_7687691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687691).length < 2 ^ (prefixWord ++ tailWord_7687691).sum := by decide
  have hdescent : baseEnd_7687691 < baseStart_7687691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687704 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 1, 2, 4]
def baseStart_7687704 : Nat := 118140960795 + 7687704 * 2 ^ 59
def prefixEnd_7687704 : Nat := 4983230072969 + 3 ^ 40 * 7687704 * 2
def baseEnd_7687704 : Nat := 3947487281492295056444899

theorem tailTrace_7687704 : CollatzResearch.WordTrace tailWord_7687704 prefixEnd_7687704 3947487281492295056444899 := by
  unfold tailWord_7687704
  simp only [CollatzResearch.WordTrace]
  refine ⟨140196800070384419079299083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186929066760512558772398777 140196800070384419079299083)
  ·
    refine ⟨210295200105576628618948625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140196800070384419079299083 210295200105576628618948625)
    ·
      refine ⟨157721400079182471464211469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210295200105576628618948625 157721400079182471464211469)
      ·
        refine ⟨59145525029693426799079301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157721400079182471464211469 59145525029693426799079301)
        ·
          refine ⟨11089785943067517524827369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59145525029693426799079301 11089785943067517524827369)
          ·
            refine ⟨8317339457300638143620527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11089785943067517524827369 8317339457300638143620527)
            ·
              refine ⟨12476009185950957215430791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8317339457300638143620527 12476009185950957215430791)
              ·
                refine ⟨18714013778926435823146187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12476009185950957215430791 18714013778926435823146187)
                ·
                  refine ⟨28071020668389653734719281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18714013778926435823146187 28071020668389653734719281)
                  ·
                    refine ⟨21053265501292240301039461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28071020668389653734719281 21053265501292240301039461)
                    ·
                      refine ⟨3947487281492295056444899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21053265501292240301039461 3947487281492295056444899)
                      ·
                        rfl

theorem cell23_7687704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_7687704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687704 prefixEnd_7687704 := by exact prefixLift 7687704
  have htrace : WordTrace (prefixWord ++ tailWord_7687704) baseStart_7687704 baseEnd_7687704 := by
    simpa [prefixWord, tailWord_7687704, baseEnd_7687704] using wordTrace_append hprefix tailTrace_7687704
  have hstable : (prefixWord ++ tailWord_7687704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687704).length < 2 ^ (prefixWord ++ tailWord_7687704).sum := by decide
  have hdescent : baseEnd_7687704 < baseStart_7687704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687730 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_7687730 : Nat := 118140960795 + 7687730 * 2 ^ 59
def prefixEnd_7687730 : Nat := 4983230072969 + 3 ^ 40 * 7687730 * 2
def baseEnd_7687730 : Nat := 3947500631989311954719779

theorem tailTrace_7687730 : CollatzResearch.WordTrace tailWord_7687730 prefixEnd_7687730 3947500631989311954719779 := by
  unfold tailWord_7687730
  simp only [CollatzResearch.WordTrace]
  refine ⟨70098637109668661149761161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186929698959116429732696429 70098637109668661149761161)
  ·
    refine ⟨52573977832251495862320871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70098637109668661149761161 52573977832251495862320871)
    ·
      refine ⟨78860966748377243793481307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52573977832251495862320871 78860966748377243793481307)
      ·
        refine ⟨118291450122565865690221961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78860966748377243793481307 118291450122565865690221961)
        ·
          refine ⟨88718587591924399267666471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118291450122565865690221961 88718587591924399267666471)
          ·
            refine ⟨133077881387886598901499707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88718587591924399267666471 133077881387886598901499707)
            ·
              refine ⟨199616822081829898352249561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133077881387886598901499707 199616822081829898352249561)
              ·
                refine ⟨149712616561372423764187171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199616822081829898352249561 149712616561372423764187171)
                ·
                  refine ⟨224568924842058635646280757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149712616561372423764187171 224568924842058635646280757)
                  ·
                    refine ⟨21053336703942997091838821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 224568924842058635646280757 21053336703942997091838821)
                    ·
                      refine ⟨3947500631989311954719779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21053336703942997091838821 3947500631989311954719779)
                      ·
                        rfl

theorem cell23_7687730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_7687730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687730 prefixEnd_7687730 := by exact prefixLift 7687730
  have htrace : WordTrace (prefixWord ++ tailWord_7687730) baseStart_7687730 baseEnd_7687730 := by
    simpa [prefixWord, tailWord_7687730, baseEnd_7687730] using wordTrace_append hprefix tailTrace_7687730
  have hstable : (prefixWord ++ tailWord_7687730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687730).length < 2 ^ (prefixWord ++ tailWord_7687730).sum := by decide
  have hdescent : baseEnd_7687730 < baseStart_7687730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687760 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 4]
def baseStart_7687760 : Nat := 118140960795 + 7687760 * 2 ^ 59
def prefixEnd_7687760 : Nat := 4983230072969 + 3 ^ 40 * 7687760 * 2
def baseEnd_7687760 : Nat := 3947516036408946837344641

theorem tailTrace_7687760 : CollatzResearch.WordTrace tailWord_7687760 prefixEnd_7687760 3947516036408946837344641 := by
  unfold tailWord_7687760
  simp only [CollatzResearch.WordTrace]
  refine ⟨140197821314282979861318367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186930428419043973148424489 140197821314282979861318367)
  ·
    refine ⟨210296731971424469791977551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140197821314282979861318367 210296731971424469791977551)
    ·
      refine ⟨315445097957136704687966327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210296731971424469791977551 315445097957136704687966327)
      ·
        refine ⟨473167646935705057031949491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315445097957136704687966327 473167646935705057031949491)
        ·
          refine ⟨709751470403557585547924237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473167646935705057031949491 709751470403557585547924237)
          ·
            refine ⟨266156801401334094580471589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 709751470403557585547924237 266156801401334094580471589)
            ·
              refine ⟨49904400262750142733838423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266156801401334094580471589 49904400262750142733838423)
              ·
                refine ⟨74856600394125214100757635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49904400262750142733838423 74856600394125214100757635)
                ·
                  refine ⟨112284900591187821151136453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74856600394125214100757635 112284900591187821151136453)
                  ·
                    refine ⟨21053418860847716465838085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112284900591187821151136453 21053418860847716465838085)
                    ·
                      refine ⟨3947516036408946837344641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21053418860847716465838085 3947516036408946837344641)
                      ·
                        rfl

theorem cell23_7687760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_7687760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687760 prefixEnd_7687760 := by exact prefixLift 7687760
  have htrace : WordTrace (prefixWord ++ tailWord_7687760) baseStart_7687760 baseEnd_7687760 := by
    simpa [prefixWord, tailWord_7687760, baseEnd_7687760] using wordTrace_append hprefix tailTrace_7687760
  have hstable : (prefixWord ++ tailWord_7687760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687760).length < 2 ^ (prefixWord ++ tailWord_7687760).sum := by decide
  have hdescent : baseEnd_7687760 < baseStart_7687760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687764 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_7687764 : Nat := 118140960795 + 7687764 * 2 ^ 59
def prefixEnd_7687764 : Nat := 4983230072969 + 3 ^ 40 * 7687764 * 2
def baseEnd_7687764 : Nat := 3947518090331564821694623

theorem tailTrace_7687764 : CollatzResearch.WordTrace tailWord_7687764 prefixEnd_7687764 3947518090331564821694623 := by
  unfold tailWord_7687764
  simp only [CollatzResearch.WordTrace]
  refine ⟨140197894260275734202891173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186930525680367645603854897 140197894260275734202891173)
  ·
    refine ⟨26287105173801700163042095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140197894260275734202891173 26287105173801700163042095)
    ·
      refine ⟨39430657760702550244563143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26287105173801700163042095 39430657760702550244563143)
      ·
        refine ⟨59145986641053825366844715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39430657760702550244563143 59145986641053825366844715)
        ·
          refine ⟨88718979961580738050267073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59145986641053825366844715 88718979961580738050267073)
          ·
            refine ⟨66539234971185553537700305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88718979961580738050267073 66539234971185553537700305)
            ·
              refine ⟨49904426228389165153275229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66539234971185553537700305 49904426228389165153275229)
              ·
                refine ⟨18714159835645936932478211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49904426228389165153275229 18714159835645936932478211)
                ·
                  refine ⟨28071239753468905398717317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18714159835645936932478211 28071239753468905398717317)
                  ·
                    refine ⟨5263357453775419762259497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28071239753468905398717317 5263357453775419762259497)
                    ·
                      refine ⟨3947518090331564821694623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263357453775419762259497 3947518090331564821694623)
                      ·
                        rfl

theorem cell23_7687764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_7687764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687764 prefixEnd_7687764 := by exact prefixLift 7687764
  have htrace : WordTrace (prefixWord ++ tailWord_7687764) baseStart_7687764 baseEnd_7687764 := by
    simpa [prefixWord, tailWord_7687764, baseEnd_7687764] using wordTrace_append hprefix tailTrace_7687764
  have hstable : (prefixWord ++ tailWord_7687764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687764).length < 2 ^ (prefixWord ++ tailWord_7687764).sum := by decide
  have hdescent : baseEnd_7687764 < baseStart_7687764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687770 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 7]
def baseStart_7687770 : Nat := 118140960795 + 7687770 * 2 ^ 59
def prefixEnd_7687770 : Nat := 4983230072969 + 3 ^ 40 * 7687770 * 2
def baseEnd_7687770 : Nat := 438613463468387977579955

theorem tailTrace_7687770 : CollatzResearch.WordTrace tailWord_7687770 prefixEnd_7687770 438613463468387977579955 := by
  unfold tailWord_7687770
  simp only [CollatzResearch.WordTrace]
  refine ⟨70099001839632432857625191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186930671572353154287000509 70099001839632432857625191)
  ·
    refine ⟨105148502759448649286437787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70099001839632432857625191 105148502759448649286437787)
    ·
      refine ⟨157722754139172973929656681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105148502759448649286437787 157722754139172973929656681)
      ·
        refine ⟨118292065604379730447242511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157722754139172973929656681 118292065604379730447242511)
        ·
          refine ⟨177438098406569595670863767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118292065604379730447242511 177438098406569595670863767)
          ·
            refine ⟨266157147609854393506295651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177438098406569595670863767 266157147609854393506295651)
            ·
              refine ⟨399235721414781590259443477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266157147609854393506295651 399235721414781590259443477)
              ·
                refine ⟨18714174441317887043411413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 399235721414781590259443477 18714174441317887043411413)
                ·
                  refine ⟨438613463468387977579955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18714174441317887043411413 438613463468387977579955)
                  ·
                    rfl

theorem cell23_7687770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_7687770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687770 prefixEnd_7687770 := by exact prefixLift 7687770
  have htrace : WordTrace (prefixWord ++ tailWord_7687770) baseStart_7687770 baseEnd_7687770 := by
    simpa [prefixWord, tailWord_7687770, baseEnd_7687770] using wordTrace_append hprefix tailTrace_7687770
  have hstable : (prefixWord ++ tailWord_7687770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687770).length < 2 ^ (prefixWord ++ tailWord_7687770).sum := by decide
  have hdescent : baseEnd_7687770 < baseStart_7687770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687798 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_7687798 : Nat := 118140960795 + 7687798 * 2 ^ 59
def prefixEnd_7687798 : Nat := 4983230072969 + 3 ^ 40 * 7687798 * 2
def baseEnd_7687798 : Nat := 3947535548673817688669467

theorem tailTrace_7687798 : CollatzResearch.WordTrace tailWord_7687798 prefixEnd_7687798 3947535548673817688669467 := by
  unfold tailWord_7687798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17524814287651768263282503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186931352401618861475013365 17524814287651768263282503)
  ·
    refine ⟨26287221431477652394923755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17524814287651768263282503 26287221431477652394923755)
    ·
      refine ⟨39430832147216478592385633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26287221431477652394923755 39430832147216478592385633)
      ·
        refine ⟨29573124110412358944289225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39430832147216478592385633 29573124110412358944289225)
        ·
          refine ⟨22179843082809269208216919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29573124110412358944289225 22179843082809269208216919)
          ·
            refine ⟨33269764624213903812325379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22179843082809269208216919 33269764624213903812325379)
            ·
              refine ⟨49904646936320855718488069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33269764624213903812325379 49904646936320855718488069)
              ·
                refine ⟨9357121300560160447216513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49904646936320855718488069 9357121300560160447216513)
                ·
                  refine ⟨7017840975420120335412385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9357121300560160447216513 7017840975420120335412385)
                  ·
                    refine ⟨5263380731565090251559289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7017840975420120335412385 5263380731565090251559289)
                    ·
                      refine ⟨3947535548673817688669467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263380731565090251559289 3947535548673817688669467)
                      ·
                        rfl

theorem cell23_7687798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_7687798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687798 prefixEnd_7687798 := by exact prefixLift 7687798
  have htrace : WordTrace (prefixWord ++ tailWord_7687798) baseStart_7687798 baseEnd_7687798 := by
    simpa [prefixWord, tailWord_7687798, baseEnd_7687798] using wordTrace_append hprefix tailTrace_7687798
  have hstable : (prefixWord ++ tailWord_7687798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687798).length < 2 ^ (prefixWord ++ tailWord_7687798).sum := by decide
  have hdescent : baseEnd_7687798 < baseStart_7687798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687898 : List Nat := [3, 1, 1, 2, 2, 5, 1, 3, 1, 4]
def baseStart_7687898 : Nat := 118140960795 + 7687898 * 2 ^ 59
def prefixEnd_7687898 : Nat := 4983230072969 + 3 ^ 40 * 7687898 * 2
def baseEnd_7687898 : Nat := 1315862298913089099139669

theorem tailTrace_7687898 : CollatzResearch.WordTrace tailWord_7687898 prefixEnd_7687898 1315862298913089099139669 := by
  unfold tailWord_7687898
  simp only [CollatzResearch.WordTrace]
  refine ⟨70100168975516502322790087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186933783934710672860773565 70100168975516502322790087)
  ·
    refine ⟨105150253463274753484185131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70100168975516502322790087 105150253463274753484185131)
    ·
      refine ⟨157725380194912130226277697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105150253463274753484185131 157725380194912130226277697)
      ·
        refine ⟨118294035146184097669708273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157725380194912130226277697 118294035146184097669708273)
        ·
          refine ⟨88720526359638073252281205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118294035146184097669708273 88720526359638073252281205)
          ·
            refine ⟨8317549346216069367401363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88720526359638073252281205 8317549346216069367401363)
            ·
              refine ⟨12476324019324104051102045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8317549346216069367401363 12476324019324104051102045)
              ·
                refine ⟨4678621507246539019163267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12476324019324104051102045 4678621507246539019163267)
                ·
                  refine ⟨7017932260869808528744901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678621507246539019163267 7017932260869808528744901)
                  ·
                    refine ⟨1315862298913089099139669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7017932260869808528744901 1315862298913089099139669)
                    ·
                      rfl

theorem cell23_7687898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_7687898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687898 prefixEnd_7687898 := by exact prefixLift 7687898
  have htrace : WordTrace (prefixWord ++ tailWord_7687898) baseStart_7687898 baseEnd_7687898 := by
    simpa [prefixWord, tailWord_7687898, baseEnd_7687898] using wordTrace_append hprefix tailTrace_7687898
  have hstable : (prefixWord ++ tailWord_7687898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687898).length < 2 ^ (prefixWord ++ tailWord_7687898).sum := by decide
  have hdescent : baseEnd_7687898 < baseStart_7687898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687904 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 5, 1, 3]
def baseStart_7687904 : Nat := 118140960795 + 7687904 * 2 ^ 59
def prefixEnd_7687904 : Nat := 4983230072969 + 3 ^ 40 * 7687904 * 2
def baseEnd_7687904 : Nat := 3947589977623194273943979

theorem tailTrace_7687904 : CollatzResearch.WordTrace tailWord_7687904 prefixEnd_7687904 3947589977623194273943979 := by
  unfold tailWord_7687904
  simp only [CollatzResearch.WordTrace]
  refine ⟨140200447370022136157939383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186933929826696181543919177 140200447370022136157939383)
  ·
    refine ⟨210300671055033204236909075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140200447370022136157939383 210300671055033204236909075)
    ·
      refine ⟨315451006582549806355363613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210300671055033204236909075 315451006582549806355363613)
      ·
        refine ⟨118294127468456177383261355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315451006582549806355363613 118294127468456177383261355)
        ·
          refine ⟨177441191202684266074892033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118294127468456177383261355 177441191202684266074892033)
          ·
            refine ⟨133080893402013199556169025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177441191202684266074892033 133080893402013199556169025)
            ·
              refine ⟨99810670051509899667126769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133080893402013199556169025 99810670051509899667126769)
              ·
                refine ⟨74858002538632424750345077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99810670051509899667126769 74858002538632424750345077)
                ·
                  refine ⟨7017937737996789820344851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74858002538632424750345077 7017937737996789820344851)
                  ·
                    refine ⟨10526906606995184730517277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7017937737996789820344851 10526906606995184730517277)
                    ·
                      refine ⟨3947589977623194273943979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10526906606995184730517277 3947589977623194273943979)
                      ·
                        rfl

theorem cell23_7687904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_7687904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687904 prefixEnd_7687904 := by exact prefixLift 7687904
  have htrace : WordTrace (prefixWord ++ tailWord_7687904) baseStart_7687904 baseEnd_7687904 := by
    simpa [prefixWord, tailWord_7687904, baseEnd_7687904] using wordTrace_append hprefix tailTrace_7687904
  have hstable : (prefixWord ++ tailWord_7687904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687904).length < 2 ^ (prefixWord ++ tailWord_7687904).sum := by decide
  have hdescent : baseEnd_7687904 < baseStart_7687904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687921 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 3, 1, 3]
def baseStart_7687921 : Nat := 118140960795 + 7687921 * 2 ^ 59
def prefixEnd_7687921 : Nat := 4983230072969 + 3 ^ 40 * 7687921 * 2
def baseEnd_7687921 : Nat := 3947598706794320707431401

theorem tailTrace_7687921 : CollatzResearch.WordTrace tailWord_7687921 prefixEnd_7687921 3947598706794320707431401 := by
  unfold tailWord_7687921
  simp only [CollatzResearch.WordTrace]
  refine ⟨280401514780982684219247617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186934343187321789479498411 280401514780982684219247617)
  ·
    refine ⟨210301136085737013164435713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280401514780982684219247617 210301136085737013164435713)
    ·
      refine ⟨157725852064302759873326785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210301136085737013164435713 157725852064302759873326785)
      ·
        refine ⟨118294389048227069904995089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157725852064302759873326785 118294389048227069904995089)
        ·
          refine ⟨88720791786170302428746317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118294389048227069904995089 88720791786170302428746317)
          ·
            refine ⟨33270296919813863410779869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88720791786170302428746317 33270296919813863410779869)
            ·
              refine ⟨12476361344930198779042451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33270296919813863410779869 12476361344930198779042451)
              ·
                refine ⟨18714542017395298168563677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12476361344930198779042451 18714542017395298168563677)
                ·
                  refine ⟨7017953256523236813211379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18714542017395298168563677 7017953256523236813211379)
                  ·
                    refine ⟨10526929884784855219817069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7017953256523236813211379 10526929884784855219817069)
                    ·
                      refine ⟨3947598706794320707431401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10526929884784855219817069 3947598706794320707431401)
                      ·
                        rfl

theorem cell23_7687921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_7687921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687921 prefixEnd_7687921 := by exact prefixLift 7687921
  have htrace : WordTrace (prefixWord ++ tailWord_7687921) baseStart_7687921 baseEnd_7687921 := by
    simpa [prefixWord, tailWord_7687921, baseEnd_7687921] using wordTrace_append hprefix tailTrace_7687921
  have hstable : (prefixWord ++ tailWord_7687921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687921).length < 2 ^ (prefixWord ++ tailWord_7687921).sum := by decide
  have hdescent : baseEnd_7687921 < baseStart_7687921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687944 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_7687944 : Nat := 118140960795 + 7687944 * 2 ^ 59
def prefixEnd_7687944 : Nat := 4983230072969 + 3 ^ 40 * 7687944 * 2
def baseEnd_7687944 : Nat := 3947610516849374117443795

theorem tailTrace_7687944 : CollatzResearch.WordTrace tailWord_7687944 prefixEnd_7687944 3947610516849374117443795 := by
  unfold tailWord_7687944
  simp only [CollatzResearch.WordTrace]
  refine ⟨140201176829949679573667443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186934902439932906098223257 140201176829949679573667443)
  ·
    refine ⟨210301765244924519360501165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140201176829949679573667443 210301765244924519360501165)
    ·
      refine ⟨78863161966846694760187937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210301765244924519360501165 78863161966846694760187937)
      ·
        refine ⟨59147371475135021070140953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78863161966846694760187937 59147371475135021070140953)
        ·
          refine ⟨44360528606351265802605715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59147371475135021070140953 44360528606351265802605715)
          ·
            refine ⟨66540792909526898703908573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44360528606351265802605715 66540792909526898703908573)
            ·
              refine ⟨24952797341072587013965715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66540792909526898703908573 24952797341072587013965715)
              ·
                refine ⟨37429196011608880520948573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24952797341072587013965715 37429196011608880520948573)
                ·
                  refine ⟨14035948504353330195355715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37429196011608880520948573 14035948504353330195355715)
                  ·
                    refine ⟨21053922756529995293033573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14035948504353330195355715 21053922756529995293033573)
                    ·
                      refine ⟨3947610516849374117443795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21053922756529995293033573 3947610516849374117443795)
                      ·
                        rfl

theorem cell23_7687944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_7687944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687944 prefixEnd_7687944 := by exact prefixLift 7687944
  have htrace : WordTrace (prefixWord ++ tailWord_7687944) baseStart_7687944 baseEnd_7687944 := by
    simpa [prefixWord, tailWord_7687944, baseEnd_7687944] using wordTrace_append hprefix tailTrace_7687944
  have hstable : (prefixWord ++ tailWord_7687944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687944).length < 2 ^ (prefixWord ++ tailWord_7687944).sum := by decide
  have hdescent : baseEnd_7687944 < baseStart_7687944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687947 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 5]
def baseStart_7687947 : Nat := 118140960795 + 7687947 * 2 ^ 59
def prefixEnd_7687947 : Nat := 4983230072969 + 3 ^ 40 * 7687947 * 2
def baseEnd_7687947 : Nat := 3947612057291337605706281

theorem tailTrace_7687947 : CollatzResearch.WordTrace tailWord_7687947 prefixEnd_7687947 3947612057291337605706281 := by
  unfold tailWord_7687947
  simp only [CollatzResearch.WordTrace]
  refine ⟨280402463078888490659694095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186934975385925660439796063 280402463078888490659694095)
  ·
    refine ⟨420603694618332735989541143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280402463078888490659694095 420603694618332735989541143)
    ·
      refine ⟨630905541927499103984311715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420603694618332735989541143 630905541927499103984311715)
      ·
        refine ⟨946358312891248655976467573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630905541927499103984311715 946358312891248655976467573)
        ·
          refine ⟨88721091833554561497793835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 946358312891248655976467573 88721091833554561497793835)
          ·
            refine ⟨133081637750331842246690753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88721091833554561497793835 133081637750331842246690753)
            ·
              refine ⟨99811228312748881685018065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133081637750331842246690753 99811228312748881685018065)
              ·
                refine ⟨74858421234561661263763549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99811228312748881685018065 74858421234561661263763549)
                ·
                  refine ⟨28071907962960622973911331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74858421234561661263763549 28071907962960622973911331)
                  ·
                    refine ⟨42107861944440934460866997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28071907962960622973911331 42107861944440934460866997)
                    ·
                      refine ⟨3947612057291337605706281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42107861944440934460866997 3947612057291337605706281)
                      ·
                        rfl

theorem cell23_7687947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 5].length) (baseStart_7687947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687947 prefixEnd_7687947 := by exact prefixLift 7687947
  have htrace : WordTrace (prefixWord ++ tailWord_7687947) baseStart_7687947 baseEnd_7687947 := by
    simpa [prefixWord, tailWord_7687947, baseEnd_7687947] using wordTrace_append hprefix tailTrace_7687947
  have hstable : (prefixWord ++ tailWord_7687947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687947).length < 2 ^ (prefixWord ++ tailWord_7687947).sum := by decide
  have hdescent : baseEnd_7687947 < baseStart_7687947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687966 : List Nat := [4, 3, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7687966 : Nat := 118140960795 + 7687966 * 2 ^ 59
def prefixEnd_7687966 : Nat := 4983230072969 + 3 ^ 40 * 7687966 * 2
def baseEnd_7687966 : Nat := 1315873937807924343789565

theorem tailTrace_7687966 : CollatzResearch.WordTrace tailWord_7687966 prefixEnd_7687966 1315873937807924343789565 := by
  unfold tailWord_7687966
  simp only [CollatzResearch.WordTrace]
  refine ⟨35050394508227457113079469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186935437377213104603090501 35050394508227457113079469)
  ·
    refine ⟨13143897940585296417404801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35050394508227457113079469 13143897940585296417404801)
    ·
      refine ⟨9857923455438972313053601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13143897940585296417404801 9857923455438972313053601)
      ·
        refine ⟨7393442591579229234790201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9857923455438972313053601 7393442591579229234790201)
        ·
          refine ⟨5545081943684421926092651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7393442591579229234790201 5545081943684421926092651)
          ·
            refine ⟨8317622915526632889138977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545081943684421926092651 8317622915526632889138977)
            ·
              refine ⟨6238217186644974666854233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8317622915526632889138977 6238217186644974666854233)
              ·
                refine ⟨4678662889983731000140675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6238217186644974666854233 4678662889983731000140675)
                ·
                  refine ⟨7017994334975596500211013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678662889983731000140675 7017994334975596500211013)
                  ·
                    refine ⟨1315873937807924343789565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7017994334975596500211013 1315873937807924343789565)
                    ·
                      rfl

theorem cell23_7687966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7687966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687966 prefixEnd_7687966 := by exact prefixLift 7687966
  have htrace : WordTrace (prefixWord ++ tailWord_7687966) baseStart_7687966 baseEnd_7687966 := by
    simpa [prefixWord, tailWord_7687966, baseEnd_7687966] using wordTrace_append hprefix tailTrace_7687966
  have hstable : (prefixWord ++ tailWord_7687966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687966).length < 2 ^ (prefixWord ++ tailWord_7687966).sum := by decide
  have hdescent : baseEnd_7687966 < baseStart_7687966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687972 : List Nat := [2, 3, 1, 3, 2, 3, 2, 2, 1, 1, 3]
def baseStart_7687972 : Nat := 118140960795 + 7687972 * 2 ^ 59
def prefixEnd_7687972 : Nat := 4983230072969 + 3 ^ 40 * 7687972 * 2
def baseEnd_7687972 : Nat := 3947624894307700007893667

theorem tailTrace_7687972 : CollatzResearch.WordTrace tailWord_7687972 prefixEnd_7687972 3947624894307700007893667 := by
  unfold tailWord_7687972
  simp only [CollatzResearch.WordTrace]
  refine ⟨140201687451898959964677085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186935583269198613286236113 140201687451898959964677085)
  ·
    refine ⟨52575632794462109986753907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140201687451898959964677085 52575632794462109986753907)
    ·
      refine ⟨78863449191693164980130861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52575632794462109986753907 78863449191693164980130861)
      ·
        refine ⟨29573793446884936867549073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78863449191693164980130861 29573793446884936867549073)
        ·
          refine ⟨22180345085163702650661805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29573793446884936867549073 22180345085163702650661805)
          ·
            refine ⟨8317629406936388493998177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22180345085163702650661805 8317629406936388493998177)
            ·
              refine ⟨6238222055202291370498633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8317629406936388493998177 6238222055202291370498633)
              ·
                refine ⟨4678666541401718527873975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6238222055202291370498633 4678666541401718527873975)
                ·
                  refine ⟨7017999812102577791810963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678666541401718527873975 7017999812102577791810963)
                  ·
                    refine ⟨10526999718153866687716445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7017999812102577791810963 10526999718153866687716445)
                    ·
                      refine ⟨3947624894307700007893667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10526999718153866687716445 3947624894307700007893667)
                      ·
                        rfl

theorem cell23_7687972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_7687972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687972 prefixEnd_7687972 := by exact prefixLift 7687972
  have htrace : WordTrace (prefixWord ++ tailWord_7687972) baseStart_7687972 baseEnd_7687972 := by
    simpa [prefixWord, tailWord_7687972, baseEnd_7687972] using wordTrace_append hprefix tailTrace_7687972
  have hstable : (prefixWord ++ tailWord_7687972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687972).length < 2 ^ (prefixWord ++ tailWord_7687972).sum := by decide
  have hdescent : baseEnd_7687972 < baseStart_7687972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7687988 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_7687988 : Nat := 118140960795 + 7687988 * 2 ^ 59
def prefixEnd_7687988 : Nat := 4983230072969 + 3 ^ 40 * 7687988 * 2
def baseEnd_7687988 : Nat := 1315877703332723981764531

theorem tailTrace_7687988 : CollatzResearch.WordTrace tailWord_7687988 prefixEnd_7687988 1315877703332723981764531 := by
  unfold tailWord_7687988
  simp only [CollatzResearch.WordTrace]
  refine ⟨140201979235869977330968309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186935972314493303107957745 140201979235869977330968309)
  ·
    refine ⟨13143935553362810374778279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140201979235869977330968309 13143935553362810374778279)
    ·
      refine ⟨19715903330044215562167419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13143935553362810374778279 19715903330044215562167419)
      ·
        refine ⟨29573854995066323343251129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19715903330044215562167419 29573854995066323343251129)
        ·
          refine ⟨22180391246299742507438347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29573854995066323343251129 22180391246299742507438347)
          ·
            refine ⟨33270586869449613761157521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22180391246299742507438347 33270586869449613761157521)
            ·
              refine ⟨24952940152087210320868141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33270586869449613761157521 24952940152087210320868141)
              ·
                refine ⟨9357352557032703870325553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24952940152087210320868141 9357352557032703870325553)
                ·
                  refine ⟨7018014417774527902744165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9357352557032703870325553 7018014417774527902744165)
                  ·
                    refine ⟨1315877703332723981764531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7018014417774527902744165 1315877703332723981764531)
                    ·
                      rfl

theorem cell23_7687988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_7687988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7687988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7687988 prefixEnd_7687988 := by exact prefixLift 7687988
  have htrace : WordTrace (prefixWord ++ tailWord_7687988) baseStart_7687988 baseEnd_7687988 := by
    simpa [prefixWord, tailWord_7687988, baseEnd_7687988] using wordTrace_append hprefix tailTrace_7687988
  have hstable : (prefixWord ++ tailWord_7687988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7687988).length < 2 ^ (prefixWord ++ tailWord_7687988).sum := by decide
  have hdescent : baseEnd_7687988 < baseStart_7687988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7687988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
